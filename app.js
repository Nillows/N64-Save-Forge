/* N64 Save Forge - app.js (engine + OoT schema + granular flags + versions) */

/* =====================================================================
   N64 SAVE FORGE — generic engine + Ocarina of Time (NTSC) schema
   One engine reads a declarative SCHEMA of where each value lives
   (byte/bit). Same schema powers analysis (read) and editing (write).
   To add a game: add a schema; the engine is untouched.
   Schema offsets are RELATIVE TO SLOT START (0x1C before "ZELDAZ").
   Refs: CloudModding OoT "Save Format"; core offsets cross-checked
   against the zeldaret/oot decomp struct layout.
   ===================================================================== */
const SLOT_SIZE=0x1450, SRAM_SIZE=0x8000;
const MAGIC_OFF=0x1C, MAGIC=[0x5A,0x45,0x4C,0x44,0x41,0x5A]; // "ZELDAZ"
const CHKSUM_OFF=0x1352, CHKSUM_WORDS=0x9A9;
const SLOT_BASES=[0x20,0x1470,0x28C0,0x3D10,0x5160,0x65B0];
const NAME_PAD=0xDF;

const S={ work:null, order:'be', fileName:'save.sra', slots:[], slotBase:null, version:'ntsc' };

/* byte-order helpers (self-inverse) */
function swapN(buf,n){
  const out=new Uint8Array(buf.length); let i=0;
  for(;i+n<=buf.length;i+=n) for(let j=0;j<n;j++) out[i+j]=buf[i+n-1-j];
  for(;i<buf.length;i++) out[i]=buf[i];
  return out;
}
const swap16=b=>swapN(b,2), swap32=b=>swapN(b,4);
function findMagic(buf){
  const hits=[];
  outer: for(let i=0;i+MAGIC.length<=buf.length;i++){
    for(let k=0;k<MAGIC.length;k++) if(buf[i+k]!==MAGIC[k]) continue outer;
    hits.push(i);
  }
  return hits;
}

/* big-endian accessors (absolute = slotBase + off) */
const A=off=>S.slotBase+off;
const u8=o=>S.work[A(o)];
const setU8=(o,v)=>{S.work[A(o)]=v&0xFF;};
const u16=o=>{const a=A(o);return (S.work[a]<<8)|S.work[a+1];};
const setU16=(o,v)=>{const a=A(o);S.work[a]=(v>>8)&0xFF;S.work[a+1]=v&0xFF;};
const u32=o=>{const a=A(o);return ((S.work[a]<<24)|(S.work[a+1]<<16)|(S.work[a+2]<<8)|S.work[a+3])>>>0;};
const setU32=(o,v)=>{const a=A(o);v>>>=0;S.work[a]=(v>>>24)&0xFF;S.work[a+1]=(v>>>16)&0xFF;S.work[a+2]=(v>>>8)&0xFF;S.work[a+3]=v&0xFF;};

/* bit ops by scope */
const readWord=(sc,o)=>sc==='u32'?u32(o):sc==='u16'?u16(o):u8(o);
const writeWord=(sc,o,v)=>{sc==='u32'?setU32(o,v):sc==='u16'?setU16(o,v):setU8(o,v);};
const getBit=(sc,o,b)=>(readWord(sc,o)>>>b)&1;
function setBit(sc,o,b,on){let w=readWord(sc,o);w=on?(w|(1<<b))>>>0:(w&~(1<<b))>>>0;writeWord(sc,o,w);}
const getChoice=(sc,o,m,sh)=>(readWord(sc,o)&m)>>>sh;
function setChoice(sc,o,m,sh,v){let w=readWord(sc,o);w=((w&~m)|((v<<sh)&m))>>>0;writeWord(sc,o,w);}

/* name codec (OoT NTSC charset; cosmetic only) */
/* ---- Versions & player-name codecs (decomp: include/message.h FILENAME_* macros) ----
   The save STRUCTURE is identical across every OoT version. The one editor-relevant
   difference is the player-name charset:
     NTSC (US/JP, GC US/JP): digits 00-09, kana 0A-AA, A-Z AB-C4, a-z C5-DE, space DF
     PAL  (EU,    GC EU):    digits 00-09,           A-Z 0A-23, a-z 24-3D, space 3E
   This codec layer is also where future games can diverge by version.            */
const NAME_CODECS={
  ntsc:{ space:0xDF,
    dec(c){
      if(c<=0x09) return String.fromCharCode(48+c);
      if(c>=0xAB&&c<=0xC4) return String.fromCharCode(65+(c-0xAB));
      if(c>=0xC5&&c<=0xDE) return String.fromCharCode(97+(c-0xC5));
      if(c===0xDF) return ' ';
      const p={0xE1:'?',0xE2:'!',0xE3:':',0xE4:'-',0xE5:'(',0xE6:')',0xE9:',',0xEA:'.',0xEB:'/'};
      if(p[c]!=null) return p[c];
      if(c>=0x0A&&c<=0xAA) return '\u00B7';
      return '';
    },
    enc(ch){
      const c=ch.charCodeAt(0);
      if(c>=48&&c<=57) return c-48;
      if(c>=65&&c<=90) return 0xAB+(c-65);
      if(c>=97&&c<=122) return 0xC5+(c-97);
      const r={' ':0xDF,'?':0xE1,'!':0xE2,':':0xE3,'-':0xE4,'(':0xE5,')':0xE6,',':0xE9,'.':0xEA,'/':0xEB};
      return r[ch]!=null?r[ch]:0xDF;
    }},
  pal:{ space:0x3E,
    dec(c){
      if(c<=0x09) return String.fromCharCode(48+c);
      if(c>=0x0A&&c<=0x23) return String.fromCharCode(65+(c-0x0A));
      if(c>=0x24&&c<=0x3D) return String.fromCharCode(97+(c-0x24));
      if(c===0x3E) return ' ';
      if(c===0x3F) return '-';
      if(c===0x40) return '.';
      return '';
    },
    enc(ch){
      const c=ch.charCodeAt(0);
      if(c>=48&&c<=57) return c-48;
      if(c>=65&&c<=90) return 0x0A+(c-65);
      if(c>=97&&c<=122) return 0x24+(c-97);
      const r={' ':0x3E,'-':0x3F,'.':0x40};
      return r[ch]!=null?r[ch]:0x3E;
    }}
};
const VERSIONS=[
  {id:'ntsc', label:'NTSC \u2014 US / JP', codec:'ntsc'},
  {id:'pal',  label:'PAL \u2014 Europe',   codec:'pal'}
];
function activeCodec(){const v=VERSIONS.find(x=>x.id===S.version)||VERSIONS[0];return NAME_CODECS[v.codec];}
function getName(){const cd=activeCodec();let s='';for(let i=0;i<8;i++) s+=cd.dec(u8(0x24+i));return s;}
function setName(str){const cd=activeCodec();for(let i=0;i<8;i++) setU8(0x24+i, i<str.length?cd.enc(str[i]):cd.space);}
/* Best-effort version guess: the space/pad byte alone separates NTSC (0xDF) from PAL (0x3E). */
function guessVersion(){
  let ntsc=0,pal=0;
  for(let i=0;i<8;i++){const c=u8(0x24+i);
    if(c>=0xAB&&c<=0xEB) ntsc++; else if(c>=0x0A&&c<=0x40) pal++;}
  return pal>ntsc?'pal':'ntsc';
}

/* checksum */
function computeChecksum(){
  let sum=0;
  for(let i=0;i<CHKSUM_WORDS;i++){const a=S.slotBase+i*2;sum=(sum+((S.work[a]<<8)|S.work[a+1]))&0xFFFF;}
  return sum;
}
const storedChecksum=()=>u16(CHKSUM_OFF);
const refreshChecksum=()=>setU16(CHKSUM_OFF,computeChecksum());
function magicValid(){for(let k=0;k<MAGIC.length;k++) if(u8(MAGIC_OFF+k)!==MAGIC[k]) return false;return true;}

/* =====================================================================
   SCHEMA — Ocarina of Time (NTSC). Add a game by adding a block like this.
   ===================================================================== */
const ecf=(off,bit,label)=>({type:'flag',scope:'u16',off,bit,label}); // event_chk_inf (u16[])
const bf =(off,bit,label)=>({type:'flag',scope:'u8', off,bit,label}); // byte-indexed bitflag
const qf =(bit,label)=>({type:'flag',scope:'u32',off:0xA4,bit,label}); // quest status u32
const eqf=(bit,label)=>({type:'flag',scope:'u16',off:0x9C,bit,label}); // equipment u16

const DUNGEONS=[
  [0,"Deku Tree"],[1,"Dodongo's Cavern"],[2,"Jabu-Jabu"],[3,"Forest Temple"],
  [4,"Fire Temple"],[5,"Water Temple"],[6,"Spirit Temple"],[7,"Shadow Temple"],
  [8,"Bottom of the Well"],[9,"Ice Cavern"],[10,"Gerudo Training Ground"],
  [11,"Thieves' Hideout"],[13,"Ganon's Castle"]
];
const KEYED=[3,4,5,6,7,8,10,11,13];
function dungeonItemFields(){
  const f=[];
  for(const [s,n] of DUNGEONS){
    f.push({type:'flag',scope:'u8',off:0xA8+s,bit:0,label:n+" — Boss Key"});
    f.push({type:'flag',scope:'u8',off:0xA8+s,bit:1,label:n+" — Compass"});
    f.push({type:'flag',scope:'u8',off:0xA8+s,bit:2,label:n+" — Map"});
  }
  return f;
}
function smallKeyFields(){
  const byName=Object.fromEntries(DUNGEONS);
  return KEYED.map(s=>({type:'int',off:0xBC+s,size:1,min:0,max:9,label:byName[s]+" keys"}));
}
const inv =(idx,id,label)=>({type:'invtoggle',off:0x74+idx,id,label});
const ammo=(idx,label,max)=>({type:'int',off:0x8C+idx,size:1,min:0,max:max||99,label});

const SCHEMA={
  game:"The Legend of Zelda: Ocarina of Time (NTSC)",
  groups:[
    { id:'player', title:'File & Player', fields:[
      {type:'text', off:0x24, label:'File name'},
      {type:'choice', scope:'u32', off:0x04, mask:0xFFFFFFFF, shift:0,
        options:[['Adult Link',0],['Child Link',1]], label:'Age'},
      {type:'int', off:0x2E, size:2, scale:0x10, min:3, max:20, label:'Heart containers'},
      {type:'int', off:0x30, size:2, scale:0x10, min:0, max:20, label:'Current health (hearts)'},
      {type:'byteflag', off:0x3A, label:'Magic — unlocked'},
      {type:'byteflag', off:0x3C, label:'Magic — double (upgraded)'},
      {type:'choice', scope:'u8', off:0x32, mask:0xFF, shift:0,
        options:[['None',0],['Single bar',1],['Double bar',2]], label:'Magic meter size'},
      {type:'int', off:0x33, size:1, min:0, max:0x60, label:'Magic (current, 0x60=full)'},
      {type:'int', off:0x34, size:2, min:0, max:999, label:'Rupees'},
      {type:'int', off:0xD0, size:2, min:0, max:100, label:'Gold Skulltula tokens'},
      {type:'byteflag', off:0x3E, label:"Biggoron's Sword — unlocked"},
      {type:'int', off:0x22, size:2, min:0, max:65535, label:'Death count'},
    ]},
    { id:'equip', title:'Equipment Owned', toggleable:true, fields:[
      {sub:'Swords'}, eqf(0,'Kokiri Sword'), eqf(1,'Master Sword'), eqf(2,"Biggoron's Sword"), eqf(3,"Giant's Knife"),
      {sub:'Shields'}, eqf(4,'Deku Shield'), eqf(5,'Hylian Shield'), eqf(6,'Mirror Shield'),
      {sub:'Tunics'}, eqf(8,'Kokiri Tunic'), eqf(9,'Goron Tunic'), eqf(10,'Zora Tunic'),
      {sub:'Boots'}, eqf(12,'Kokiri Boots'), eqf(13,'Iron Boots'), eqf(14,'Hover Boots'),
    ]},
    { id:'upgrades', title:'Upgrades', fields:[
      {type:'choice', scope:'u32', off:0xA0, mask:0x00000007, shift:0,
        options:[['None',0],['Quiver (30)',1],['Big Quiver (40)',2],['Biggest Quiver (50)',3]], label:'Quiver'},
      {type:'choice', scope:'u32', off:0xA0, mask:0x00000038, shift:3,
        options:[['None',0],['Bomb Bag (20)',1],['Big (30)',2],['Biggest (40)',3]], label:'Bomb Bag'},
      {type:'choice', scope:'u32', off:0xA0, mask:0x000001C0, shift:6,
        options:[['None',0],['Goron Bracelet',1],['Silver Gauntlets',2],['Golden Gauntlets',3]], label:'Strength'},
      {type:'choice', scope:'u32', off:0xA0, mask:0x00000E00, shift:9,
        options:[['None',0],['Silver Scale',1],['Golden Scale',2]], label:'Diving Scale'},
      {type:'choice', scope:'u32', off:0xA0, mask:0x00003000, shift:12,
        options:[['Child Wallet (99)',0],['Adult Wallet (200)',1],['Giant Wallet (500)',2]], label:'Wallet'},
      {type:'choice', scope:'u32', off:0xA0, mask:0x0001C000, shift:14,
        options:[['None',0],['Bullet Bag (30)',1],['(40)',2],['(50)',3]], label:'Slingshot Bag'},
      {type:'choice', scope:'u32', off:0xA0, mask:0x000E0000, shift:17,
        options:[['Base (10)',0],['(20)',1],['(30)',2]], label:'Deku Stick capacity'},
      {type:'choice', scope:'u32', off:0xA0, mask:0x00700000, shift:20,
        options:[['Base (20)',0],['(30)',1],['(40)',2]], label:'Deku Nut capacity'},
    ]},
    { id:'inventory', title:'Inventory Items', fields:[
      {sub:'Items'},
      inv(0,0x00,'Deku Sticks'), inv(1,0x01,'Deku Nuts'), inv(2,0x02,'Bombs'),
      inv(3,0x03,'Fairy Bow'), inv(4,0x04,'Fire Arrow'),
      {type:'choice',scope:'u8',off:0x7B,mask:0xFF,shift:0,
        options:[['—',0xFF],['Fairy Ocarina',0x07],['Ocarina of Time',0x08]],label:'Ocarina'},
      inv(5,0x05,"Din's Fire"), inv(6,0x06,'Slingshot'), inv(8,0x09,'Bombchu'),
      {type:'choice',scope:'u8',off:0x7D,mask:0xFF,shift:0,
        options:[['—',0xFF],['Hookshot',0x0A],['Longshot',0x0B]],label:'Hookshot'},
      inv(10,0x0C,'Ice Arrow'), inv(11,0x0D,"Farore's Wind"), inv(12,0x0E,'Boomerang'),
      inv(13,0x0F,'Lens of Truth'), inv(14,0x10,'Magic Beans'), inv(15,0x11,'Megaton Hammer'),
      inv(16,0x12,'Light Arrow'), inv(17,0x13,"Nayru's Love"),
      {sub:'Bottles'},
      {type:'choice',scope:'u8',off:0x86,mask:0xFF,shift:0,options:[['Empty slot',0xFF],['Empty Bottle',0x14]],label:'Bottle 1'},
      {type:'choice',scope:'u8',off:0x87,mask:0xFF,shift:0,options:[['Empty slot',0xFF],['Empty Bottle',0x14]],label:'Bottle 2'},
      {type:'choice',scope:'u8',off:0x88,mask:0xFF,shift:0,options:[['Empty slot',0xFF],['Empty Bottle',0x14]],label:'Bottle 3'},
      {type:'choice',scope:'u8',off:0x89,mask:0xFF,shift:0,options:[['Empty slot',0xFF],['Empty Bottle',0x14]],label:'Bottle 4'},
      {sub:'Trade items (advanced — raw item ID, 255 = none)'},
      {type:'int',off:0x8A,size:1,min:0,max:255,label:'Adult trade item ID'},
      {type:'int',off:0x8B,size:1,min:0,max:255,label:'Child trade item ID'},
    ]},
    { id:'ammo', title:'Ammo Counts', fields:[
      ammo(0,'Deku Sticks',30), ammo(1,'Deku Nuts',40), ammo(2,'Bombs',40),
      ammo(3,'Arrows',50), ammo(6,'Slingshot Seeds',50), ammo(8,'Bombchu',50), ammo(14,'Magic Beans',10),
    ]},
    { id:'medallions', title:'Medallions', toggleable:true, fields:[
      qf(0,'Forest Medallion'), qf(1,'Fire Medallion'), qf(2,'Water Medallion'),
      qf(3,'Spirit Medallion'), qf(4,'Shadow Medallion'), qf(5,'Light Medallion'),
    ]},
    { id:'stones', title:'Spiritual Stones', toggleable:true, fields:[
      qf(18,"Kokiri's Emerald"), qf(19,"Goron's Ruby"), qf(20,"Zora's Sapphire"),
    ]},
    { id:'songs', title:'Ocarina Songs', toggleable:true, fields:[
      qf(12,"Zelda's Lullaby"), qf(13,"Epona's Song"), qf(14,"Saria's Song"),
      qf(15,"Sun's Song"), qf(16,'Song of Time'), qf(17,'Song of Storms'),
      qf(6,'Minuet of Forest'), qf(7,'Bolero of Fire'), qf(8,'Serenade of Water'),
      qf(9,'Requiem of Spirit'), qf(10,'Nocturne of Shadow'), qf(11,'Prelude of Light'),
    ]},
    { id:'questmisc', title:'Other Quest Items', toggleable:true, fields:[
      qf(21,'Stone of Agony'), qf(22,'Gerudo Card'), qf(23,'Gold Skulltula (first collected)'),
    ]},
    { id:'dungeonitems', title:'Dungeon Items', toggleable:true, fields:dungeonItemFields() },
    { id:'smallkeys', title:'Small Keys', fields:smallKeyFields() },
    { id:'events', title:'Story / Event Flags', toggleable:true, fields:[
      {sub:'Deku Tree & Kokiri'},
      ecf(0xED4,2,'First spoke to Mido'), ecf(0xED4,3,'Complained about Mido to Saria'),
      ecf(0xED4,4,'Showed Mido sword & shield'), ecf(0xED4,5,'Deku Tree opened mouth'),
      ecf(0xED4,6,"Spoke to Saria after Deku Tree's death"), ecf(0xED4,7,'Kokiri Emerald & Deku Tree dead'),
      ecf(0xED4,9,"Used blue warp in Gohma's lair"), ecf(0xED4,10,"Played Saria's Song for Mido (adult)"),
      ecf(0xED4,12,'Met Deku Tree'),
      ecf(0xEEC,6,'Spoke to Deku Tree Sprout'), ecf(0xEEC,1,'Spoke to Saria on Lost Woods Bridge'),
      {sub:'Lon Lon Ranch & Epona'},
      ecf(0xED6,0,'Spoke to child Malon at Castle/Market'), ecf(0xED6,1,'Spoke to Ingo before Talon returns'),
      ecf(0xED6,2,'Obtained Pocket Egg'), ecf(0xED6,3,'Woke Talon'),
      ecf(0xED6,4,'Talon fled Hyrule Castle'), ecf(0xED6,5,'Spoke to child Malon at Ranch'),
      ecf(0xED6,6,'Invited to sing with child Malon'), ecf(0xED6,8,'Obtained Epona'),
      ecf(0xED6,11,'Rented horse from Ingo'), ecf(0xED6,14,"Won the cow in Malon's race"),
      ecf(0xEE0,10,'Woke Talon in Kakariko'), ecf(0xEE0,11,'Spoke to Talon after saving ranch'),
      {sub:'Zora & Jabu-Jabu'},
      ecf(0xEDA,0,'Spoke to a Zora'), ecf(0xEDA,1,"Obtained Ruto's Letter"),
      ecf(0xEDA,3,'King Zora moved aside'), ecf(0xEDA,7,"Obtained Zora's Sapphire"),
      ecf(0xEDA,8,'Obtained Silver Scale'), ecf(0xEDA,9,"Opened entrance to Zora's Domain"),
      ecf(0xEDA,10,'Offered fish to Jabu-Jabu'), ecf(0xEDA,11,'Began Nabooru battle'),
      ecf(0xEDA,12,'Finished Nabooru battle'),
      {sub:'Hyrule Castle & Master Sword'},
      ecf(0xED6,7,'Great Deku Tree is dead'), ecf(0xED6,9,"Obtained Kokiri's Emerald"),
      ecf(0xEDC,0,"Obtained Zelda's Letter"), ecf(0xEDC,3,'Obtained Ocarina of Time'),
      ecf(0xEDC,5,'Pulled Master Sword from pedestal'), ecf(0xEDC,8,'Obtained Forest Medallion'),
      ecf(0xEDC,9,'Obtained Fire Medallion'), ecf(0xEDC,10,'Obtained Water Medallion'),
      ecf(0xEDC,11,'Opened the Door of Time'), ecf(0xEDC,13,'Rainbow Bridge built by Sages'),
      ecf(0xEDC,14,'Caught by Hyrule Castle guards'), ecf(0xEDC,15,'Entered Master Sword chamber'),
      ecf(0xEE4,0,'Zelda fled Hyrule Castle'), ecf(0xEE4,2,'Bridge unlocked (Zelda escape)'),
      ecf(0xEEC,8,'Obtained Spirit Medallion'),
      {sub:'Learned Songs'},
      ecf(0xEDE,0,'Learned Minuet of Forest'), ecf(0xEDE,1,'Learned Bolero of Fire'),
      ecf(0xEDE,2,'Learned Serenade of Water'), ecf(0xEDE,4,'Learned Nocturne of Shadow'),
      ecf(0xEDE,9,"Learned Zelda's Lullaby"), ecf(0xEDE,10,"Learned Sun's Song"),
      ecf(0xEDE,11,'Learned Song of Storms'), ecf(0xEE8,9,'Learned Song of Time'),
      ecf(0xEE8,12,'Learned Requiem of Spirit'), ecf(0xEDE,5,'Sheik moved from sword pedestal'),
      {sub:'Boss Battles Begun'},
      ecf(0xEE2,0,'Gohma'), ecf(0xEE2,1,'King Dodongo'), ecf(0xEE2,2,'Phantom Ganon'),
      ecf(0xEE2,3,'Volvagia'), ecf(0xEE2,4,'Morpha'), ecf(0xEE2,5,'Twinrova'),
      ecf(0xEE2,6,'Barinade'), ecf(0xEE2,7,'Bongo Bongo'), ecf(0xEE2,8,'Ganondorf'),
      {sub:'Trials & Endgame'},
      ecf(0xEE8,13,'Completed Spirit Trial'),
      ecf(0xEEA,11,'Completed Forest Trial'), ecf(0xEEA,12,'Completed Water Trial'),
      ecf(0xEEA,13,'Completed Shadow Trial'), ecf(0xEEA,14,'Completed Fire Trial'),
      ecf(0xEEA,15,'Completed Light Trial'),
      ecf(0xEEC,3,"Dispelled Ganon's Tower barrier"),
      ecf(0xEEC,4,'Returned to Temple of Time with all Medallions'),
      ecf(0xEEC,7,"Watched Ganon's Tower collapse"),
      {sub:'Area First-Entry'},
      ecf(0xEE8,0,'Hyrule Field'), ecf(0xEE8,1,'Death Mountain Trail'), ecf(0xEE8,3,'Kakariko Village'),
      ecf(0xEE8,4,"Zora's Domain"), ecf(0xEE8,5,'Hyrule Castle'), ecf(0xEE8,6,'Goron City'),
      ecf(0xEE8,7,'Temple of Time'), ecf(0xEE8,8,'Deku Tree'),
      ecf(0xEEA,0,"Dodongo's Cavern"), ecf(0xEEA,1,'Lake Hylia'), ecf(0xEEA,2,'Gerudo Valley'),
      ecf(0xEEA,3,"Gerudo's Fortress"), ecf(0xEEA,4,'Lon Lon Ranch'), ecf(0xEEA,5,"Jabu-Jabu's Belly"),
      ecf(0xEEA,6,'Graveyard'), ecf(0xEEA,7,"Zora's Fountain"), ecf(0xEEA,8,'Desert Colossus'),
      ecf(0xEEA,9,'Death Mountain Crater'), ecf(0xEEA,10,"Ganon's Castle (exterior)"),
      {sub:'Wallets, Hearts & Misc'},
      ecf(0xED8,3,"Bombed Dodongo's Cavern entrance"), ecf(0xED8,5,"Completed Dodongo's Cavern"),
      ecf(0xED8,15,'Death Mountain erupted'),
      ecf(0xEE0,7,'Drained well in Kakariko'), ecf(0xEE0,8,'Played Gerudo Archery minigame'),
      ecf(0xEE0,9,"Restored Lake Hylia's water"), ecf(0xEE0,15,'Spoke to Kaepora Gaebora by Lost Woods'),
      ecf(0xEE6,4,'Spoke to Nabooru in Spirit Temple'), ecf(0xEE6,5,'Nabooru captured by Twinrova'),
      ecf(0xEE6,0,'Rescued Red Carpenter'), ecf(0xEE6,1,'Rescued Yellow Carpenter'),
      ecf(0xEE6,2,'Rescued Blue Carpenter'), ecf(0xEE6,3,'Rescued Green Carpenter'),
      ecf(0xEEE,0,"Frogs' Piece of Heart"), ecf(0xEEE,10,"Obtained Adult's Wallet"),
      ecf(0xEEE,11,'Obtained Stone of Agony'), ecf(0xEEE,12,"Obtained Giant's Wallet"),
      ecf(0xEEE,13,"Skulltula House's Bombchu"), ecf(0xEEE,14,"Skulltula House's Piece of Heart"),
    ]},
    { id:'itemget', title:'Item-Get Flags', toggleable:true, fields:[
      bf(0xEF0,3,'Heart Piece — Grotto Scrub'), bf(0xEF0,4,'Bottle from Cucco Lady'),
      bf(0xEF0,6,'Quiver Upgrade — Kakariko'), bf(0xEF0,7,'Quiver Upgrade — Gerudo'),
      bf(0xEF2,0,"Farore's Wind"), bf(0xEF2,1,"Din's Fire"), bf(0xEF2,2,"Nayru's Love"),
      bf(0xEF2,5,'Deku Seed Bag Upgrade'), bf(0xEF2,6,'Deku Stick Upgrade (stage)'),
      bf(0xEF2,7,'Deku Nut Upgrade (stage)'),
      bf(0xEF3,0,'Heart Piece — Lake Researcher'), bf(0xEF3,5,'Heart Piece — Man on Roof'),
      bf(0xEF3,6,'Heart Piece — Skull Kid'), bf(0xEF3,7,'Heart Piece — Skull Kids'),
      bf(0xEF4,2,'Mask of Truth'), bf(0xEF4,4,'Pocket Egg from Cucco Lady'),
      bf(0xEF4,6,'Cojiro from Cucco Lady'),
      bf(0xEF5,3,'Keaton Mask'), bf(0xEF5,4,'Skull Mask'), bf(0xEF5,5,'Spooky Mask'),
      bf(0xEF5,6,'Bunny Hood'),
      bf(0xEF7,0,'Odd Potion from Granny'), bf(0xEF7,1,"Poacher's Saw from Fado"),
    ]},
    { id:'world', title:'World / NPC Flags', toggleable:true, fields:[
      {sub:'Useful state'},
      bf(0xF2A,0,'Get Magic Container'),
      bf(0xF18,1,'Obtained Fire Tunic from Goron Link'),
      bf(0xF1E,0,'Thawed King Zora'), bf(0xF1E,1,'Obtained Zora Tunic'),
      bf(0xF2B,0,'Gerudo Archery Heart Piece'), bf(0xF2B,1,'Heart Piece — Found Richard'),
      bf(0xF2B,2,'Deku Stick Upgrade — Lost Woods'), bf(0xF2B,3,'Deku Nut Upgrade — Grotto'),
      bf(0xF07,7,'Soldier wears Keaton Mask'),
      {sub:'Dungeon first-entry (inf_table)'},
      bf(0xF2D,0,'Deku Tree'), bf(0xF2D,1,"Dodongo's Cavern"), bf(0xF2D,2,"Jabu-Jabu's Belly"),
      bf(0xF2D,3,'Forest Temple'), bf(0xF2D,4,'Fire Temple'), bf(0xF2D,5,'Water Temple'),
      bf(0xF2D,6,'Spirit Temple'), bf(0xF2D,7,'Shadow Temple'),
      bf(0xF2C,0,'Bottom of the Well'), bf(0xF2C,1,'Ice Cavern'), bf(0xF2C,2,"Ganon's Tower"),
      bf(0xF2C,3,'Gerudo Training Ground'), bf(0xF2C,4,"Thieves' Hideout"),
      bf(0xF2C,5,"Ganon's Castle"),
    ]},
  ]
};

/* =====================================================================
   RENDERING + UI
   ===================================================================== */
const $=s=>document.querySelector(s);
const editorEl=$('#editor');
let CONTROLS=[];

function fieldOffsetLabel(f){
  if(f.type==='text') return '0x'+f.off.toString(16)+'·str8';
  if(f.type==='int'||f.type==='byteflag'||f.type==='invtoggle')
    return '0x'+f.off.toString(16)+(f.size===2?'·u16':'');
  if(f.type==='choice') return '0x'+f.off.toString(16)+'·m'+f.mask.toString(16);
  if(f.type==='flag') return '0x'+f.off.toString(16)+'.'+f.bit;
  return '';
}

function render(){
  editorEl.innerHTML=''; CONTROLS=[];
  for(const g of SCHEMA.groups){
    const det=document.createElement('details');
    det.className='group'; det.dataset.gid=g.id;
    if(g.id==='player'||g.id==='medallions') det.open=true;

    const sum=document.createElement('summary');
    sum.className='ghead';
    sum.innerHTML='<span class="chev"></span><span class="gtitle">'+g.title+'</span><span class="gcount" data-count></span>';
    if(g.toggleable){
      const m=document.createElement('label');
      m.className='gmaster';
      m.innerHTML='<input type="checkbox" data-master> all';
      m.addEventListener('click',e=>e.stopPropagation());
      m.querySelector('input').addEventListener('change',e=>masterToggle(g.id,e.target.checked));
      sum.appendChild(m);
    }
    det.appendChild(sum);

    const body=document.createElement('div'); body.className='gbody';
    let grid=null;
    const ensureGrid=()=>{ if(!grid){grid=document.createElement('div');grid.className='grid';body.appendChild(grid);} return grid; };
    for(const f of g.fields){
      if(f.sub!==undefined){
        const h=document.createElement('div'); h.className='subhdr'; h.textContent=f.sub;
        body.appendChild(h); grid=null; continue;
      }
      const row=buildRow(f,g);
      ensureGrid().appendChild(row.el);
      CONTROLS.push(row);
    }
    det.appendChild(body);
    editorEl.appendChild(det);
  }
}

function buildRow(f,g){
  const row=document.createElement('div'); row.className='row';
  const isCheck=(f.type==='flag'||f.type==='byteflag'||f.type==='invtoggle');
  if(!isCheck) row.classList.add('field');
  const off=document.createElement('span'); off.className='off'; off.textContent=fieldOffsetLabel(f);
  let input;
  if(isCheck){
    input=document.createElement('input'); input.type='checkbox';
    const lab=document.createElement('label'); lab.className='flab';
    lab.appendChild(input); lab.appendChild(document.createTextNode(f.label)); lab.appendChild(off);
    row.appendChild(lab);
    input.addEventListener('change',()=>{ writeField(f,input); afterEdit(g.id); });
  } else {
    const lab=document.createElement('label'); lab.className='flab';
    lab.textContent=f.label; lab.appendChild(off); row.appendChild(lab);
    if(f.type==='choice'){
      input=document.createElement('select');
      for(const [t,v] of f.options){const o=document.createElement('option');o.value=v;o.textContent=t;input.appendChild(o);}
    } else if(f.type==='int'){
      input=document.createElement('input'); input.type='number';
      if(f.min!==undefined)input.min=f.min; if(f.max!==undefined)input.max=f.max;
    } else { // text
      input=document.createElement('input'); input.type='text'; input.maxLength=8;
    }
    const ctl=document.createElement('span'); ctl.className='ctl'; ctl.appendChild(input); row.appendChild(ctl);
    input.addEventListener('change',()=>{ writeField(f,input); afterEdit(g.id); });
  }
  return {field:f, el:row, input, group:g};
}

/* read buffer -> controls (analyzer) */
function populate(){
  for(const c of CONTROLS) readField(c.field,c.input);
  for(const g of SCHEMA.groups) updateGroupMeta(g.id);
}
function readField(f,input){
  if(f.type==='flag') input.checked=!!getBit(f.scope,f.off,f.bit);
  else if(f.type==='byteflag') input.checked=u8(f.off)!==0;
  else if(f.type==='invtoggle') input.checked=u8(f.off)===f.id;
  else if(f.type==='choice') input.value=String(getChoice(f.scope,f.off,f.mask,f.shift));
  else if(f.type==='int'){ let raw=f.size===2?u16(f.off):u8(f.off); input.value=f.scale?Math.round(raw/f.scale):raw; }
  else if(f.type==='text') input.value=getName().replace(/\s+$/,'');
}
function writeField(f,input){
  if(f.type==='flag') setBit(f.scope,f.off,f.bit,input.checked);
  else if(f.type==='byteflag') setU8(f.off,input.checked?1:0);
  else if(f.type==='invtoggle') setU8(f.off,input.checked?f.id:0xFF);
  else if(f.type==='choice') setChoice(f.scope,f.off,f.mask,f.shift,parseInt(input.value,10));
  else if(f.type==='int'){
    let v=parseInt(input.value,10); if(isNaN(v))v=0;
    if(f.min!==undefined)v=Math.max(f.min,v); if(f.max!==undefined)v=Math.min(f.max,v);
    input.value=v;
    let raw=f.scale?Math.round(v*f.scale):v;
    f.size===2?setU16(f.off,raw):setU8(f.off,raw);
  }
  else if(f.type==='text') setName(input.value);
}
function afterEdit(gid){ refreshChecksum(); updateGroupMeta(gid); updateBadge(); }

function masterToggle(gid,on){
  for(const c of CONTROLS){
    if(c.group.id!==gid) continue;
    if(c.input.type==='checkbox'){ c.input.checked=on; writeField(c.field,c.input); }
  }
  afterEdit(gid);
}
function updateGroupMeta(gid){
  const det=editorEl.querySelector('details[data-gid="'+gid+'"]'); if(!det) return;
  const checks=CONTROLS.filter(c=>c.group.id===gid && c.input.type==='checkbox');
  const on=checks.filter(c=>c.input.checked).length;
  const countEl=det.querySelector('[data-count]');
  if(checks.length) countEl.innerHTML='<span class="on">'+on+'</span> / '+checks.length;
  else countEl.textContent=String(CONTROLS.filter(c=>c.group.id===gid).length);
  const master=det.querySelector('[data-master]');
  if(master){ master.checked=on===checks.length && checks.length>0; master.indeterminate=on>0 && on<checks.length; }
}

/* badge + dock */
function updateBadge(){
  const b=$('#badge');
  if(!S.work){ b.className='badge'; b.innerHTML='<span class="dot"></span><span class="k">no file</span>'; return; }
  const valid=magicValid(); const cs=storedChecksum();
  b.className='badge '+(valid?'ok':'bad');
  b.innerHTML='<span class="dot"></span>'+
    (valid?'<span class="k">save</span><span class="v">valid</span>':'<span class="k">marker</span><span class="v">missing</span>')+
    '<span class="k">chk</span><span class="v">0x'+cs.toString(16).toUpperCase().padStart(4,'0')+'</span>';
  updateDock();
}
function updateDock(){
  const m=$('#dockMeta');
  if(!S.work){ m.innerHTML='<span><span class="k">no file loaded</span></span>'; return; }
  const on={be:'big-endian',swap16:'byte-swapped (16)',swap32:'byte-swapped (32)'}[S.order];
  m.innerHTML='<span><span class="k">file</span> '+S.fileName+'</span>'+
    '<span><span class="k">order</span> '+on+'</span>'+
    '<span><span class="k">slot</span> 0x'+S.slotBase.toString(16)+'</span>'+
    '<span><span class="k">size</span> '+S.work.length+' B</span>';
}

/* filter */
function applyFilter(){
  const q=$('#filter').value.trim().toLowerCase();
  for(const det of editorEl.querySelectorAll('details.group')){
    let anyVisible=false;
    for(const c of CONTROLS){
      if(c.group.id!==det.dataset.gid) continue;
      const match=!q || c.field.label.toLowerCase().includes(q);
      c.el.classList.toggle('hidden',!match);
      if(match) anyVisible=true;
    }
    // hide empty sub-headers
    const body=det.querySelector('.gbody');
    if(body){
      body.querySelectorAll('.subhdr').forEach(h=>{
        let sib=h.nextElementSibling, hasVisible=false;
        while(sib && !sib.classList.contains('subhdr')){
          if(sib.classList.contains('grid')){
            if([...sib.children].some(ch=>!ch.classList.contains('hidden'))) hasVisible=true;
          }
          sib=sib.nextElementSibling;
        }
        h.classList.toggle('hidden',!hasVisible);
      });
    }
    det.classList.toggle('hidden',!anyVisible);
    if(q && anyVisible) det.open=true;
  }
}

/* =====================================================================
   LOAD / NEW / DOWNLOAD
   ===================================================================== */
function tryOrders(orig){
  const cands=[['be',orig],['swap16',swap16(orig)],['swap32',swap32(orig)]];
  for(const [order,buf] of cands){
    const hits=findMagic(buf).filter(h=>h-MAGIC_OFF>=0 && (h-MAGIC_OFF)+SLOT_SIZE<=buf.length);
    if(hits.length) return {order,buf,hits};
  }
  return null;
}
function loadBuffer(orig,fileName){
  const res=tryOrders(orig);
  if(!res){
    alert("Couldn't find an Ocarina of Time save in this file.\n\n"+
      "It looks for the \"ZELDAZ\" marker in big-endian and byte-swapped layouts. "+
      "Supported: raw SRAM (.sra), RetroArch (.srm), and common byte-swapped dumps. "+
      "An unusual source may need converting first (e.g. with n64SaveConverter).");
    return;
  }
  S.work=res.buf; S.order=res.order; S.fileName=fileName;
  S.slots=res.hits.map((h,i)=>({base:h-MAGIC_OFF, label:'Save '+(i+1)+' — 0x'+(h-MAGIC_OFF).toString(16)}));
  S.slotBase=S.slots[0].base;

  const sel=$('#slotSel'); sel.innerHTML='';
  S.slots.forEach((s,i)=>{const o=document.createElement('option');o.value=i;o.textContent=s.label;sel.appendChild(o);});
  $('#slotWrap').style.display=S.slots.length>1?'flex':'none';

  $('#dropzone').style.display='none';
  $('#dlBtn').disabled=false;

  S.version=guessVersion(); { const vs=document.getElementById('versionSel'); if(vs) vs.value=S.version; }
  render(); populate(); if(window.renderBig){window.renderBig();window.populateBig();} updateBadge(); applyFilter();
}
function buildNewFile(){
  const buf=new Uint8Array(SRAM_SIZE);
  const hdr=[0x98,0x09,0x10,0x21,0x5A,0x45,0x4C,0x44,0x41];
  hdr.forEach((b,i)=>buf[0x03+i]=b);
  const base=SLOT_BASES[0];
  MAGIC.forEach((b,i)=>buf[base+MAGIC_OFF+i]=b);
  buf[base+0x2E]=0x00; buf[base+0x2F]=0x30;   // 3 heart containers
  buf[base+0x30]=0x00; buf[base+0x31]=0x30;   // full health
  for(let i=0;i<8;i++) buf[base+0x24+i]=NAME_PAD;
  for(let i=0xBC;i<=0xCF;i++) buf[base+i]=0xFF; // small keys none
  for(let i=0;i<24;i++) buf[base+0x74+i]=0xFF;  // empty inventory
  buf[base+0x07]=0x01;                          // child Link (age int32)
  return buf;
}
function newFile(){
  if(S.work && !confirm('Start a new blank file? Current edits will be discarded.')) return;
  const buf=buildNewFile();
  S.work=buf; S.order='be'; S.slotBase=SLOT_BASES[0];
  refreshChecksum();
  loadBuffer(buf,'new-file.sra');
}
function download(){
  refreshChecksum();
  let out=S.work;
  if(S.order==='swap16') out=swap16(S.work);
  else if(S.order==='swap32') out=swap32(S.work);
  const blob=new Blob([out],{type:'application/octet-stream'});
  const a=document.createElement('a');
  const dot=S.fileName.lastIndexOf('.');
  const stem=dot>0?S.fileName.slice(0,dot):S.fileName;
  const ext=dot>0?S.fileName.slice(dot):'.sra';
  a.href=URL.createObjectURL(blob); a.download=stem+'-edited'+ext;
  document.body.appendChild(a); a.click(); a.remove();
  setTimeout(()=>URL.revokeObjectURL(a.href),1000);
  const t=$('#toast'); t.classList.add('show'); setTimeout(()=>t.classList.remove('show'),1600);
}

/* =====================================================================
   WIRING
   ===================================================================== */
function readFile(file){
  const r=new FileReader();
  r.onload=()=>loadBuffer(new Uint8Array(r.result), file.name);
  r.readAsArrayBuffer(file);
}
$('#loadBtn').addEventListener('click',()=>$('#fileInput').click());
$('#fileInput').addEventListener('change',e=>{ if(e.target.files[0]) readFile(e.target.files[0]); });
$('#newBtn').addEventListener('click',newFile);
$('#dlBtn').addEventListener('click',download);
$('#filter').addEventListener('input',applyFilter);
$('#offToggle').addEventListener('change',e=>document.body.classList.toggle('show-off',e.target.checked));
$('#slotSel').addEventListener('change',e=>{
  S.slotBase=S.slots[+e.target.value].base; populate(); if(window.populateBig)window.populateBig(); updateBadge(); applyFilter();
});

const dz=$('#dropzone');
['dragenter','dragover'].forEach(ev=>dz.addEventListener(ev,e=>{e.preventDefault();dz.classList.add('drag');}));
['dragleave','drop'].forEach(ev=>dz.addEventListener(ev,e=>{e.preventDefault();dz.classList.remove('drag');}));
dz.addEventListener('drop',e=>{ if(e.dataTransfer.files[0]) readFile(e.dataTransfer.files[0]); });
// allow dropping anywhere on the page too
window.addEventListener('dragover',e=>e.preventDefault());
window.addEventListener('drop',e=>{ e.preventDefault(); if(!S.work && e.dataTransfer.files[0]) readFile(e.dataTransfer.files[0]); });

$('#footer').innerHTML=
  'N64 Save Forge · '+SCHEMA.game+' · schema-driven editor/analyzer<br>'+
  'Format from the CloudModding OoT wiki; core offsets cross-checked against the zeldaret/oot decomp. '+
  'NTSC layout. Always keep a backup of your original save.';



/* ============ Granular per-scene flags + Gold Skulltulas (decomp-derived) ============ */
const SCENE_NAMES={
  0:"Deku Tree",
  1:"Dodongo's Cavern",
  2:"Jabu-Jabu",
  3:"Forest Temple",
  4:"Fire Temple",
  5:"Water Temple",
  6:"Spirit Temple",
  7:"Shadow Temple",
  8:"Bottom Of The Well",
  9:"Ice Cavern",
  10:"Ganon's Tower",
  11:"Gerudo Training Ground",
  12:"Thieves Hideout",
  13:"Inside Ganon's Castle",
  14:"Ganon's Tower Collapse Interior",
  15:"Inside Ganon's Castle Collapse",
  16:"Treasure Box Shop",
  17:"Deku Tree Boss",
  18:"Dodongo's Cavern Boss",
  19:"Jabu-Jabu Boss",
  20:"Forest Temple Boss",
  21:"Fire Temple Boss",
  22:"Water Temple Boss",
  23:"Spirit Temple Boss",
  24:"Shadow Temple Boss",
  25:"Ganondorf Boss",
  26:"Ganon's Tower Collapse Exterior",
  27:"Market Entrance Day",
  28:"Market Entrance Night",
  29:"Market Entrance Ruins",
  30:"Back Alley Day",
  31:"Back Alley Night",
  32:"Market Day",
  33:"Market Night",
  34:"Market Ruins",
  35:"Temple Of Time Exterior Day",
  36:"Temple Of Time Exterior Night",
  37:"Temple Of Time Exterior Ruins",
  38:"Know It All Bros House",
  39:"Twins House",
  40:"Midos House",
  41:"Sarias House",
  42:"Kakariko Center Guest House",
  43:"Back Alley House",
  44:"Bazaar",
  45:"Kokiri Shop",
  46:"Goron Shop",
  47:"Zora Shop",
  48:"Potion Shop Kakariko",
  49:"Potion Shop Market",
  50:"Bombchu Shop",
  51:"Happy Mask Shop",
  52:"Links House",
  53:"Dog Lady House",
  54:"Stable",
  55:"Impas House",
  56:"Lakeside Laboratory",
  57:"Carpenters Tent",
  58:"Gravekeepers Hut",
  59:"Great Fairys Fountain Magic",
  60:"Fairys Fountain",
  61:"Great Fairys Fountain Spells",
  62:"Grottos",
  63:"Redead Grave",
  64:"Grave With Fairys Fountain",
  65:"Royal Familys Tomb",
  66:"Shooting Gallery",
  67:"Temple Of Time",
  68:"Chamber Of The Sages",
  69:"Castle Courtyard Guards Day",
  70:"Castle Courtyard Guards Night",
  71:"Cutscene Map",
  72:"Windmill And Dampes Grave",
  73:"Fishing Pond",
  74:"Castle Courtyard Zelda",
  75:"Bombchu Bowling Alley",
  76:"Lon Lon Buildings",
  77:"Market Guard House",
  78:"Potion Shop Granny",
  79:"Ganon Boss",
  80:"House Of Skulltula",
  81:"Hyrule Field",
  82:"Kakariko Village",
  83:"Graveyard",
  84:"Zora's River",
  85:"Kokiri Forest",
  86:"Sacred Forest Meadow",
  87:"Lake Hylia",
  88:"Zora's Domain",
  89:"Zora's Fountain",
  90:"Gerudo Valley",
  91:"Lost Woods",
  92:"Desert Colossus",
  93:"Gerudo's Fortress",
  94:"Haunted Wasteland",
  95:"Hyrule Castle",
  96:"Death Mountain Trail",
  97:"Death Mountain Crater",
  98:"Goron City",
  99:"Lon Lon Ranch",
  100:"Outside Ganon's Castle",
  101:"Test01",
  102:"Besitu",
  103:"Depth Test",
  104:"Syotes",
  105:"Syotes2",
  106:"Sutaru",
  107:"Hairal Niwa2",
  108:"Sasatest",
  109:"Testroom",
};
// 110 scenes named

/* ---- layout constants (verified against include/save.h) ---- */
const SCENE_BASE=0xD4, SCENE_STRIDE=0x1C, SCENE_COUNT=124;
const SCENE_FIELDS=[
  ['Chests',0x00],['Switches / Doors',0x04],['Room Clear',0x08],
  ['Collectibles',0x0C],['Visited Rooms',0x14],['Visited Floors',0x18]
];
const GS_BASE=0xE9C;
// gAreaGsFlags[] from z_kaleido_scope.c — per-area "all collected" masks (sum of bits = 100)
const GS_AREA_MASKS=[0x0F,0x1F,0x0F,0x1F,0x1F,0x1F,0x1F,0x1F,0x07,0x07,0x03,0x0F,0x07,0x0F,0x0F,0xFF,0xFF,0xFF,0x1F,0x0F,0x03,0x0F];
// dungeon GS areas (mapIndex = sceneId for dungeons); overworld areas shown by index
const GS_NAMES={0:"Deku Tree",1:"Dodongo's Cavern",2:"Jabu-Jabu",3:"Forest Temple",4:"Fire Temple",5:"Water Temple",6:"Spirit Temple",7:"Shadow Temple",8:"Bottom of the Well",9:"Ice Cavern",10:"Gerudo Training Ground"};

const popc=x=>{x>>>=0;let c=0;while(x){c+=x&1;x>>>=1;}return c;};
const sceneOff=idx=>SCENE_BASE+idx*SCENE_STRIDE;
function sceneSetBits(idx){const b=sceneOff(idx);let n=0;for(const[,o]of SCENE_FIELDS)n+=popc(u32(b+o));return n;}


const sceneBuilt=new Set();
function afterBigEdit(){ refreshChecksum(); updateBadge(); }

function buildSceneInner(det,idx){
  const wrap=document.createElement('div');
  const base=sceneOff(idx);
  for(const[label,off]of SCENE_FIELDS){
    const foff=base+off;
    const blk=document.createElement('div'); blk.className='fieldblk';
    const head=document.createElement('div'); head.className='fieldhead';
    head.innerHTML='<span>'+label+'</span><span class="hx" data-hx>0x'+u32(foff).toString(16).toUpperCase().padStart(8,'0')+'</span>';
    const all=document.createElement('span'); all.className='mini'; all.textContent='[all]';
    const clr=document.createElement('span'); clr.className='mini'; clr.textContent='[clear]';
    head.appendChild(all); head.appendChild(clr); blk.appendChild(head);
    const grid=document.createElement('div'); grid.className='bitgrid';
    const boxes=[];
    const syncHx=()=>{head.querySelector('[data-hx]').textContent='0x'+u32(foff).toString(16).toUpperCase().padStart(8,'0');};
    for(let bit=0;bit<32;bit++){
      const cell=document.createElement('label'); cell.className='bitcell';
      const cb=document.createElement('input'); cb.type='checkbox'; cb.checked=!!getBit('u32',foff,bit);
      cb.addEventListener('change',()=>{ setBit('u32',foff,bit,cb.checked); syncHx(); afterBigEdit(); updateSceneCount(idx); });
      boxes.push(cb); cell.appendChild(cb); cell.appendChild(document.createTextNode(bit)); grid.appendChild(cell);
    }
    all.addEventListener('click',()=>{setU32(foff,0xFFFFFFFF);boxes.forEach(cb=>cb.checked=true);syncHx();afterBigEdit();updateSceneCount(idx);});
    clr.addEventListener('click',()=>{setU32(foff,0);boxes.forEach(cb=>cb.checked=false);syncHx();afterBigEdit();updateSceneCount(idx);});
    blk.appendChild(grid); blk._boxes=boxes; blk._foff=foff; wrap.appendChild(blk);
  }
  det.appendChild(wrap); det._wrap=wrap;
}

function updateSceneCount(idx){
  const det=document.querySelector('.scene[data-scene="'+idx+'"]'); if(!det)return;
  const n=sceneSetBits(idx);
  const c=det.querySelector('.scnt'); c.textContent=n+' set'; c.classList.toggle('has',n>0);
  updateSceneTotal();
}
function updateSceneTotal(){
  let t=0; for(let i=0;i<SCENE_COUNT;i++) t+=sceneSetBits(i);
  const el=document.getElementById('sceneTotal'); if(el) el.textContent=t+' bits';
}

function renderSceneSection(){
  const parent=document.createElement('details'); parent.className='group'; parent.id='sceneSection';
  parent.innerHTML='<summary class="ghead"><span class="chev"></span><span class="gtitle">Area / Scene Flags — granular save state</span><span class="gcount" id="sceneTotal"></span></summary>';
  const body=document.createElement('div'); body.className='gbody';
  const note=document.createElement('div'); note.className='bignote';
  note.textContent='Raw per-scene save state for all 124 scenes: chest, switch/door, room-clear and collectible bits, plus visited room/floor maps (chest+0, swch+4, clear+8, collect+C, rooms+14, floors+18 at slot 0xD4 + scene*0x1C). Each scene expands on click. For all-flags runs, scan which scenes still show unset bits.';
  body.appendChild(note);
  for(let i=0;i<SCENE_COUNT;i++){
    const name=SCENE_NAMES[i]||'Unused slot';
    const det=document.createElement('details'); det.className='scene'; det.dataset.scene=i;
    det.dataset.name=(name+' '+i.toString(16)).toLowerCase();
    det.innerHTML='<summary><span class="chev"></span><span class="sidx">0x'+i.toString(16).toUpperCase().padStart(2,'0')+'</span><span class="sname">'+name+'</span><span class="scnt"></span></summary>';
    det.addEventListener('toggle',()=>{ if(det.open&&!sceneBuilt.has(i)){sceneBuilt.add(i);buildSceneInner(det,i);} });
    body.appendChild(det);
  }
  parent.appendChild(body); document.getElementById('bigflags').appendChild(parent);
}

function renderGsSection(){
  const parent=document.createElement('details'); parent.className='group'; parent.id='gsSection';
  parent.innerHTML='<summary class="ghead"><span class="chev"></span><span class="gtitle">Gold Skulltulas</span><span class="gcount" id="gsTotal"></span></summary>';
  const body=document.createElement('div'); body.className='gbody';
  const note=document.createElement('div'); note.className='bignote';
  note.textContent='All 100 gold-skulltula bits, addressed exactly as the game does — gsFlags[6] at slot 0xE9C, area a -> word (a>>2), bit (a&3)*8 + n. Dungeon areas are named; overworld areas are shown by in-game index, since the open decomp does not expose their location names.';
  body.appendChild(note);
  GS_AREA_MASKS.forEach((mask,area)=>{
    const n=popc(mask), off=GS_BASE+(area>>2)*4, shift=(area&3)*8;
    const name=GS_NAMES[area]||('Overworld area 0x'+area.toString(16).toUpperCase().padStart(2,'0'));
    const blk=document.createElement('div'); blk.className='gsarea'; blk.dataset.name=name.toLowerCase();
    const head=document.createElement('div'); head.className='fieldhead';
    head.innerHTML='<span>'+name+'</span><span class="hx" data-gc>0/'+n+'</span>';
    const all=document.createElement('span'); all.className='mini'; all.textContent='[all]';
    head.appendChild(all); blk.appendChild(head);
    const grid=document.createElement('div'); grid.className='bitgrid';
    const boxes=[];
    for(let b=0;b<n;b++){
      const bit=shift+b;
      const cell=document.createElement('label'); cell.className='bitcell';
      const cb=document.createElement('input'); cb.type='checkbox'; cb.checked=!!getBit('u32',off,bit);
      cb.addEventListener('change',()=>{ setBit('u32',off,bit,cb.checked); afterBigEdit(); updateGsCount(); });
      boxes.push(cb); cell.appendChild(cb); cell.appendChild(document.createTextNode('#'+(b+1))); grid.appendChild(cell);
    }
    all.addEventListener('click',()=>{for(let b=0;b<n;b++){setBit('u32',off,shift+b,true);boxes[b].checked=true;}afterBigEdit();updateGsCount();});
    blk.appendChild(grid); blk._boxes=boxes; blk._off=off; blk._shift=shift; blk._n=n;
    body.appendChild(blk);
  });
  parent.appendChild(body); document.getElementById('bigflags').appendChild(parent);
}
function updateGsCount(){
  let total=0;
  document.querySelectorAll('#gsSection .gsarea').forEach(blk=>{
    let on=0; for(let b=0;b<blk._n;b++) if(getBit('u32',blk._off,blk._shift+b)) on++;
    total+=on; blk.querySelector('[data-gc]').textContent=on+'/'+blk._n;
  });
  const el=document.getElementById('gsTotal'); if(el) el.innerHTML='<span class="'+(total===100?'on':'')+'">'+total+'</span> / 100';
}

function renderBig(){
  const host=document.getElementById('bigflags'); host.innerHTML=''; sceneBuilt.clear();
  if(!S.work) return;
  renderSceneSection(); renderGsSection();
  filterBig(document.getElementById('filter').value.trim().toLowerCase());
}
function populateBig(){
  if(!S.work) return;
  document.querySelectorAll('#sceneSection .scene').forEach(det=>{
    const idx=+det.dataset.scene;
    if(sceneBuilt.has(idx)&&det._wrap){
      det._wrap.querySelectorAll('.fieldblk').forEach(blk=>{
        blk._boxes.forEach((cb,bit)=>{cb.checked=!!getBit('u32',blk._foff,bit);});
        const hx=blk.querySelector('[data-hx]'); if(hx) hx.textContent='0x'+u32(blk._foff).toString(16).toUpperCase().padStart(8,'0');
      });
    }
    updateSceneCount(idx);
  });
  updateSceneTotal();
  document.querySelectorAll('#gsSection .gsarea').forEach(blk=>{ blk._boxes.forEach((cb,b)=>{cb.checked=!!getBit('u32',blk._off,blk._shift+b);}); });
  updateGsCount();
}
function filterBig(q){
  const ss=document.getElementById('sceneSection');
  if(ss){ let any=false;
    ss.querySelectorAll('.scene').forEach(det=>{const m=!q||det.dataset.name.includes(q);det.style.display=m?'':'none';if(m)any=true;});
    ss.style.display=any?'':'none'; if(q&&any)ss.open=true;
  }
  const gs=document.getElementById('gsSection');
  if(gs){ let any=false;
    gs.querySelectorAll('.gsarea').forEach(blk=>{const m=!q||blk.dataset.name.includes(q)||'gold skulltula'.includes(q);blk.style.display=m?'':'none';if(m)any=true;});
    gs.style.display=any?'':'none'; if(q&&any)gs.open=true;
  }
}
window.renderBig=renderBig; window.populateBig=populateBig;
document.getElementById('filter').addEventListener('input',()=>filterBig(document.getElementById('filter').value.trim().toLowerCase()));


/* ---- version selector ---- */
(function(){
  const sel=document.getElementById('versionSel');
  if(!sel) return;
  VERSIONS.forEach(v=>{const o=document.createElement('option');o.value=v.id;o.textContent=v.label;sel.appendChild(o);});
  sel.value=S.version;
  sel.addEventListener('change',e=>{ S.version=e.target.value; if(S.work){ populate(); if(window.populateBig) window.populateBig(); } });
})();
