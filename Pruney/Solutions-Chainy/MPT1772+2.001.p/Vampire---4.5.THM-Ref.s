%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 671 expanded)
%              Number of leaves         :   55 ( 378 expanded)
%              Depth                    :    9
%              Number of atoms          : 1363 (10159 expanded)
%              Number of equality atoms :   69 ( 584 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f79,f83,f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f147,f151,f155,f159,f164,f169,f186,f191,f194,f199,f207,f216,f222,f230,f235,f239,f247,f254,f263,f270,f276,f280,f289,f293])).

fof(f293,plain,
    ( ~ spl8_9
    | ~ spl8_24
    | spl8_16
    | ~ spl8_15
    | spl8_34
    | ~ spl8_33
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f291,f287,f228,f233,f129,f133,f167,f105])).

fof(f105,plain,
    ( spl8_9
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f167,plain,
    ( spl8_24
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f133,plain,
    ( spl8_16
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f129,plain,
    ( spl8_15
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f233,plain,
    ( spl8_34
  <=> r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f228,plain,
    ( spl8_33
  <=> k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f287,plain,
    ( spl8_40
  <=> ! [X0] :
        ( ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK6)
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f291,plain,
    ( r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK6)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl8_33
    | ~ spl8_40 ),
    inference(superposition,[],[f288,f229])).

fof(f229,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f228])).

fof(f288,plain,
    ( ! [X0] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK6)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f287])).

fof(f289,plain,
    ( ~ spl8_21
    | ~ spl8_20
    | spl8_22
    | spl8_40
    | ~ spl8_13
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f285,f252,f121,f287,f157,f149,f153])).

fof(f153,plain,
    ( spl8_21
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f149,plain,
    ( spl8_20
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f157,plain,
    ( spl8_22
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f121,plain,
    ( spl8_13
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f252,plain,
    ( spl8_36
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK6)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_13
    | ~ spl8_36 ),
    inference(resolution,[],[f253,f122])).

fof(f122,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f252])).

fof(f280,plain,
    ( ~ spl8_8
    | ~ spl8_5
    | ~ spl8_4
    | ~ spl8_39 ),
    inference(avatar_split_clause,[],[f277,f274,f85,f89,f101])).

fof(f101,plain,
    ( spl8_8
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f89,plain,
    ( spl8_5
  <=> r1_tarski(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f85,plain,
    ( spl8_4
  <=> m1_connsp_2(sK5,sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f274,plain,
    ( spl8_39
  <=> ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f277,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_4
    | ~ spl8_39 ),
    inference(resolution,[],[f275,f86])).

fof(f86,plain,
    ( m1_connsp_2(sK5,sK3,sK6)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK6)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f274])).

fof(f276,plain,
    ( spl8_1
    | ~ spl8_7
    | ~ spl8_24
    | spl8_39
    | ~ spl8_34
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f271,f268,f233,f274,f167,f97,f71])).

fof(f71,plain,
    ( spl8_1
  <=> r1_tmap_1(sK3,sK1,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f97,plain,
    ( spl8_7
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f268,plain,
    ( spl8_38
  <=> ! [X1,X0] :
        ( ~ r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),X0)
        | ~ r1_tarski(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X1,sK3,X0)
        | r1_tmap_1(sK3,sK1,sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X0,sK3,sK6)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
    | ~ spl8_34
    | ~ spl8_38 ),
    inference(resolution,[],[f269,f234])).

fof(f234,plain,
    ( r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK6)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f233])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( ~ r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),X0)
        | ~ r1_tarski(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X1,sK3,X0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f268])).

fof(f270,plain,
    ( spl8_16
    | spl8_38
    | ~ spl8_9
    | ~ spl8_29
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f265,f261,f204,f105,f268,f133])).

fof(f204,plain,
    ( spl8_29
  <=> k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f261,plain,
    ( spl8_37
  <=> ! [X1,X0,X2] :
        ( ~ m1_connsp_2(X0,sK3,X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ r1_tmap_1(X2,sK1,k2_tmap_1(sK3,sK1,sK4,X2),X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ r1_tarski(X0,u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( ~ r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),X0)
        | r1_tmap_1(sK3,sK1,sK4,X0)
        | v2_struct_0(sK2)
        | ~ m1_connsp_2(X1,sK3,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tarski(X1,u1_struct_0(sK2)) )
    | ~ spl8_9
    | ~ spl8_29
    | ~ spl8_37 ),
    inference(forward_demodulation,[],[f264,f205])).

fof(f205,plain,
    ( k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f204])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(sK3,sK1,sK4,X0)
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X0)
        | v2_struct_0(sK2)
        | ~ m1_connsp_2(X1,sK3,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tarski(X1,u1_struct_0(sK2)) )
    | ~ spl8_9
    | ~ spl8_37 ),
    inference(resolution,[],[f262,f106])).

fof(f106,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f262,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X2,sK3)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ r1_tmap_1(X2,sK1,k2_tmap_1(sK3,sK1,sK4,X2),X1)
        | v2_struct_0(X2)
        | ~ m1_connsp_2(X0,sK3,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ r1_tarski(X0,u1_struct_0(X2)) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f261])).

fof(f263,plain,
    ( spl8_19
    | ~ spl8_18
    | ~ spl8_17
    | spl8_14
    | ~ spl8_25
    | ~ spl8_26
    | ~ spl8_10
    | spl8_37
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f259,f117,f113,f261,f109,f177,f174,f125,f137,f141,f145])).

fof(f145,plain,
    ( spl8_19
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f141,plain,
    ( spl8_18
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

% (11172)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f137,plain,
    ( spl8_17
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f125,plain,
    ( spl8_14
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f174,plain,
    ( spl8_25
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f177,plain,
    ( spl8_26
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f109,plain,
    ( spl8_10
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f113,plain,
    ( spl8_11
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f117,plain,
    ( spl8_12
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

% (11159)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f259,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_connsp_2(X0,sK3,X1)
        | ~ r1_tarski(X0,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X2,sK3)
        | v2_struct_0(X2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tmap_1(X2,sK1,k2_tmap_1(sK3,sK1,sK4,X2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f248,f114])).

fof(f114,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f248,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_connsp_2(X4,X2,X3)
        | ~ r1_tarski(X4,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
        | r1_tmap_1(X2,X1,sK4,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_12 ),
    inference(resolution,[],[f68,f118])).

fof(f118,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | r1_tmap_1(X1,X0,X2,X6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f254,plain,
    ( ~ spl8_7
    | spl8_36
    | ~ spl8_1
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f249,f245,f71,f252,f97])).

fof(f245,plain,
    ( spl8_35
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | r1_tmap_1(X0,sK1,k3_tmap_1(X2,sK1,sK3,X0,sK4),X1)
        | ~ r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(X1)) )
    | ~ spl8_1
    | ~ spl8_35 ),
    inference(resolution,[],[f246,f77])).

fof(f77,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tmap_1(sK3,sK1,sK4,X1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | r1_tmap_1(X0,sK1,k3_tmap_1(X2,sK1,sK3,X0,sK4),X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f245])).

fof(f247,plain,
    ( spl8_19
    | ~ spl8_18
    | ~ spl8_17
    | spl8_14
    | ~ spl8_10
    | spl8_35
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f243,f117,f113,f245,f109,f125,f137,f141,f145])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tmap_1(sK3,sK1,sK4,X1)
        | r1_tmap_1(X0,sK1,k3_tmap_1(X2,sK1,sK3,X0,sK4),X1)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f242,f114])).

fof(f242,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_pre_topc(X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ r1_tmap_1(X0,X1,sK4,X2)
        | r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,sK4),X2)
        | ~ m1_pre_topc(X3,X4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X0,X4)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4) )
    | ~ spl8_12 ),
    inference(resolution,[],[f67,f118])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f239,plain,
    ( ~ spl8_34
    | spl8_2
    | ~ spl8_3
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f237,f228,f81,f74,f233])).

fof(f74,plain,
    ( spl8_2
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f81,plain,
    ( spl8_3
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f237,plain,
    ( ~ r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK6)
    | spl8_2
    | ~ spl8_3
    | ~ spl8_33 ),
    inference(forward_demodulation,[],[f236,f229])).

fof(f236,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f75,f82])).

fof(f82,plain,
    ( sK6 = sK7
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f75,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f235,plain,
    ( spl8_34
    | ~ spl8_23
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f231,f228,f162,f233])).

fof(f162,plain,
    ( spl8_23
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f231,plain,
    ( r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK6)
    | ~ spl8_23
    | ~ spl8_33 ),
    inference(superposition,[],[f163,f229])).

fof(f163,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f162])).

fof(f230,plain,
    ( ~ spl8_15
    | spl8_33
    | ~ spl8_9
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f225,f219,f204,f197,f105,f228,f129])).

fof(f197,plain,
    ( spl8_28
  <=> k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f219,plain,
    ( spl8_32
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f225,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_9
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f224,f205])).

fof(f224,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_9
    | ~ spl8_28
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f223,f198])).

fof(f198,plain,
    ( k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f197])).

fof(f223,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_9
    | ~ spl8_32 ),
    inference(resolution,[],[f220,f106])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f219])).

fof(f222,plain,
    ( spl8_32
    | ~ spl8_20
    | ~ spl8_21
    | spl8_22
    | ~ spl8_13
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f217,f214,f121,f157,f153,f149,f219])).

fof(f214,plain,
    ( spl8_31
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,X1)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f217,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) )
    | ~ spl8_13
    | ~ spl8_31 ),
    inference(resolution,[],[f215,f122])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,X1)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4) )
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl8_19
    | ~ spl8_18
    | ~ spl8_17
    | spl8_31
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f212,f117,f113,f109,f214,f137,f141,f145])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f211,f114])).

fof(f211,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ m1_pre_topc(X0,X1)
        | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4)
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_12 ),
    inference(resolution,[],[f60,f118])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f207,plain,
    ( ~ spl8_12
    | ~ spl8_10
    | spl8_29
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f201,f197,f204,f109,f117])).

fof(f201,plain,
    ( k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ spl8_28 ),
    inference(superposition,[],[f66,f198])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f199,plain,
    ( spl8_28
    | ~ spl8_9
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f195,f183,f105,f197])).

fof(f183,plain,
    ( spl8_27
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f195,plain,
    ( k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl8_9
    | ~ spl8_27 ),
    inference(resolution,[],[f184,f106])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f183])).

fof(f194,plain,
    ( ~ spl8_20
    | ~ spl8_13
    | spl8_26 ),
    inference(avatar_split_clause,[],[f193,f177,f121,f149])).

fof(f193,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_13
    | spl8_26 ),
    inference(resolution,[],[f192,f122])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_26 ),
    inference(resolution,[],[f178,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f178,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_26 ),
    inference(avatar_component_clause,[],[f177])).

fof(f191,plain,
    ( ~ spl8_21
    | ~ spl8_20
    | ~ spl8_13
    | spl8_25 ),
    inference(avatar_split_clause,[],[f188,f174,f121,f149,f153])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_13
    | spl8_25 ),
    inference(resolution,[],[f187,f122])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl8_25 ),
    inference(resolution,[],[f175,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f175,plain,
    ( ~ v2_pre_topc(sK3)
    | spl8_25 ),
    inference(avatar_component_clause,[],[f174])).

fof(f186,plain,
    ( spl8_14
    | ~ spl8_25
    | ~ spl8_26
    | spl8_19
    | ~ spl8_18
    | ~ spl8_17
    | spl8_27
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f171,f117,f113,f109,f183,f137,f141,f145,f177,f174,f125])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f170,f114])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ m1_pre_topc(X0,X1)
        | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_12 ),
    inference(resolution,[],[f62,f118])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f169,plain,
    ( spl8_24
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f165,f93,f81,f167])).

fof(f93,plain,
    ( spl8_6
  <=> m1_subset_1(sK7,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f165,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(superposition,[],[f94,f82])).

fof(f94,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f164,plain,
    ( spl8_23
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f160,f81,f74,f162])).

fof(f160,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f78,f82])).

fof(f78,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f159,plain,(
    ~ spl8_22 ),
    inference(avatar_split_clause,[],[f37,f157])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK1,sK4,sK6) )
    & sK6 = sK7
    & m1_connsp_2(sK5,sK3,sK6)
    & r1_tarski(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f26,f34,f33,f32,f31,f30,f29,f28,f27])).

% (11160)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X1,X4,X6) )
                                    & X6 = X7
                                    & m1_connsp_2(X5,X3,X6)
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & m1_subset_1(X7,u1_struct_0(X2)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X1,X4,X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,X1,X4,X6) )
                                & X6 = X7
                                & m1_connsp_2(X5,X3,X6)
                                & r1_tarski(X5,u1_struct_0(X2))
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,sK1,X4,X6) )
                              & ( r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7)
                                | r1_tmap_1(X3,sK1,X4,X6) )
                              & X6 = X7
                              & m1_connsp_2(X5,X3,X6)
                              & r1_tarski(X5,u1_struct_0(X2))
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7)
                              | ~ r1_tmap_1(X3,sK1,X4,X6) )
                            & ( r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7)
                              | r1_tmap_1(X3,sK1,X4,X6) )
                            & X6 = X7
                            & m1_connsp_2(X5,X3,X6)
                            & r1_tarski(X5,u1_struct_0(X2))
                            & m1_subset_1(X7,u1_struct_0(X2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7)
                            | ~ r1_tmap_1(X3,sK1,X4,X6) )
                          & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7)
                            | r1_tmap_1(X3,sK1,X4,X6) )
                          & X6 = X7
                          & m1_connsp_2(X5,X3,X6)
                          & r1_tarski(X5,u1_struct_0(sK2))
                          & m1_subset_1(X7,u1_struct_0(sK2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7)
                          | ~ r1_tmap_1(X3,sK1,X4,X6) )
                        & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7)
                          | r1_tmap_1(X3,sK1,X4,X6) )
                        & X6 = X7
                        & m1_connsp_2(X5,X3,X6)
                        & r1_tarski(X5,u1_struct_0(sK2))
                        & m1_subset_1(X7,u1_struct_0(sK2)) )
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7)
                        | ~ r1_tmap_1(sK3,sK1,X4,X6) )
                      & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7)
                        | r1_tmap_1(sK3,sK1,X4,X6) )
                      & X6 = X7
                      & m1_connsp_2(X5,sK3,X6)
                      & r1_tarski(X5,u1_struct_0(sK2))
                      & m1_subset_1(X7,u1_struct_0(sK2)) )
                  & m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7)
                      | ~ r1_tmap_1(sK3,sK1,X4,X6) )
                    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7)
                      | r1_tmap_1(sK3,sK1,X4,X6) )
                    & X6 = X7
                    & m1_connsp_2(X5,sK3,X6)
                    & r1_tarski(X5,u1_struct_0(sK2))
                    & m1_subset_1(X7,u1_struct_0(sK2)) )
                & m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                    | ~ r1_tmap_1(sK3,sK1,sK4,X6) )
                  & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                    | r1_tmap_1(sK3,sK1,sK4,X6) )
                  & X6 = X7
                  & m1_connsp_2(X5,sK3,X6)
                  & r1_tarski(X5,u1_struct_0(sK2))
                  & m1_subset_1(X7,u1_struct_0(sK2)) )
              & m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                  | ~ r1_tmap_1(sK3,sK1,sK4,X6) )
                & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                  | r1_tmap_1(sK3,sK1,sK4,X6) )
                & X6 = X7
                & m1_connsp_2(X5,sK3,X6)
                & r1_tarski(X5,u1_struct_0(sK2))
                & m1_subset_1(X7,u1_struct_0(sK2)) )
            & m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                | ~ r1_tmap_1(sK3,sK1,sK4,X6) )
              & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                | r1_tmap_1(sK3,sK1,sK4,X6) )
              & X6 = X7
              & m1_connsp_2(sK5,sK3,X6)
              & r1_tarski(sK5,u1_struct_0(sK2))
              & m1_subset_1(X7,u1_struct_0(sK2)) )
          & m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

% (11176)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f33,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
              | ~ r1_tmap_1(sK3,sK1,sK4,X6) )
            & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
              | r1_tmap_1(sK3,sK1,sK4,X6) )
            & X6 = X7
            & m1_connsp_2(sK5,sK3,X6)
            & r1_tarski(sK5,u1_struct_0(sK2))
            & m1_subset_1(X7,u1_struct_0(sK2)) )
        & m1_subset_1(X6,u1_struct_0(sK3)) )
   => ( ? [X7] :
          ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
            | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
          & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
            | r1_tmap_1(sK3,sK1,sK4,sK6) )
          & sK6 = X7
          & m1_connsp_2(sK5,sK3,sK6)
          & r1_tarski(sK5,u1_struct_0(sK2))
          & m1_subset_1(X7,u1_struct_0(sK2)) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X7] :
        ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
          | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
        & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
          | r1_tmap_1(sK3,sK1,sK4,sK6) )
        & sK6 = X7
        & m1_connsp_2(sK5,sK3,sK6)
        & r1_tarski(sK5,u1_struct_0(sK2))
        & m1_subset_1(X7,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
        | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
      & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
      & sK6 = sK7
      & m1_connsp_2(sK5,sK3,sK6)
      & r1_tarski(sK5,u1_struct_0(sK2))
      & m1_subset_1(sK7,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & m1_connsp_2(X5,X3,X6)
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & m1_connsp_2(X5,X3,X6)
                                          & r1_tarski(X5,u1_struct_0(X2)) )
                                       => ( r1_tmap_1(X3,X1,X4,X6)
                                        <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f155,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f38,f153])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f151,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f39,f149])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f147,plain,(
    ~ spl8_19 ),
    inference(avatar_split_clause,[],[f40,f145])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f143,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f41,f141])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f139,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f42,f137])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f135,plain,(
    ~ spl8_16 ),
    inference(avatar_split_clause,[],[f43,f133])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f131,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f44,f129])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f127,plain,(
    ~ spl8_14 ),
    inference(avatar_split_clause,[],[f45,f125])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f123,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f46,f121])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f119,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f47,f117])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f48,f113])).

fof(f48,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f49,f109])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f107,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f50,f105])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f51,f101])).

fof(f51,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f52,f97])).

fof(f52,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

% (11158)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f95,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f53,f93])).

fof(f53,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f54,f89])).

fof(f54,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f55,f85])).

fof(f55,plain,(
    m1_connsp_2(sK5,sK3,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f56,f81])).

fof(f56,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f57,f74,f71])).

fof(f57,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f58,f74,f71])).

fof(f58,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:33:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.48  % (11165)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.49  % (11157)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.49  % (11164)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.23/0.49  % (11171)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.50  % (11161)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.50  % (11162)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.50  % (11163)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.50  % (11168)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.23/0.51  % (11169)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.51  % (11177)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.23/0.51  % (11167)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.23/0.51  % (11163)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % (11166)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f294,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(avatar_sat_refutation,[],[f76,f79,f83,f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f147,f151,f155,f159,f164,f169,f186,f191,f194,f199,f207,f216,f222,f230,f235,f239,f247,f254,f263,f270,f276,f280,f289,f293])).
% 0.23/0.51  fof(f293,plain,(
% 0.23/0.51    ~spl8_9 | ~spl8_24 | spl8_16 | ~spl8_15 | spl8_34 | ~spl8_33 | ~spl8_40),
% 0.23/0.51    inference(avatar_split_clause,[],[f291,f287,f228,f233,f129,f133,f167,f105])).
% 0.23/0.51  fof(f105,plain,(
% 0.23/0.51    spl8_9 <=> m1_pre_topc(sK2,sK3)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.23/0.51  fof(f167,plain,(
% 0.23/0.51    spl8_24 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.23/0.51  fof(f133,plain,(
% 0.23/0.51    spl8_16 <=> v2_struct_0(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.23/0.51  fof(f129,plain,(
% 0.23/0.51    spl8_15 <=> m1_pre_topc(sK2,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.23/0.51  fof(f233,plain,(
% 0.23/0.51    spl8_34 <=> r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK6)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.23/0.51  fof(f228,plain,(
% 0.23/0.51    spl8_33 <=> k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.23/0.51  fof(f287,plain,(
% 0.23/0.51    spl8_40 <=> ! [X0] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK6) | ~m1_pre_topc(X0,sK3))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.23/0.51  fof(f291,plain,(
% 0.23/0.51    r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK6) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | (~spl8_33 | ~spl8_40)),
% 0.23/0.51    inference(superposition,[],[f288,f229])).
% 0.23/0.51  fof(f229,plain,(
% 0.23/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) | ~spl8_33),
% 0.23/0.51    inference(avatar_component_clause,[],[f228])).
% 0.23/0.51  fof(f288,plain,(
% 0.23/0.51    ( ! [X0] : (r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK6) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3)) ) | ~spl8_40),
% 0.23/0.51    inference(avatar_component_clause,[],[f287])).
% 0.23/0.51  fof(f289,plain,(
% 0.23/0.51    ~spl8_21 | ~spl8_20 | spl8_22 | spl8_40 | ~spl8_13 | ~spl8_36),
% 0.23/0.51    inference(avatar_split_clause,[],[f285,f252,f121,f287,f157,f149,f153])).
% 0.23/0.51  fof(f153,plain,(
% 0.23/0.51    spl8_21 <=> v2_pre_topc(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.23/0.51  fof(f149,plain,(
% 0.23/0.51    spl8_20 <=> l1_pre_topc(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.23/0.51  fof(f157,plain,(
% 0.23/0.51    spl8_22 <=> v2_struct_0(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.23/0.51  fof(f121,plain,(
% 0.23/0.51    spl8_13 <=> m1_pre_topc(sK3,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.23/0.51  fof(f252,plain,(
% 0.23/0.51    spl8_36 <=> ! [X1,X0] : (v2_struct_0(X0) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.23/0.51  fof(f285,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,sK4),sK6) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl8_13 | ~spl8_36)),
% 0.23/0.51    inference(resolution,[],[f253,f122])).
% 0.23/0.51  fof(f122,plain,(
% 0.23/0.51    m1_pre_topc(sK3,sK0) | ~spl8_13),
% 0.23/0.51    inference(avatar_component_clause,[],[f121])).
% 0.23/0.51  fof(f253,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_36),
% 0.23/0.51    inference(avatar_component_clause,[],[f252])).
% 0.23/0.51  fof(f280,plain,(
% 0.23/0.51    ~spl8_8 | ~spl8_5 | ~spl8_4 | ~spl8_39),
% 0.23/0.51    inference(avatar_split_clause,[],[f277,f274,f85,f89,f101])).
% 0.23/0.51  fof(f101,plain,(
% 0.23/0.51    spl8_8 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.23/0.51  fof(f89,plain,(
% 0.23/0.51    spl8_5 <=> r1_tarski(sK5,u1_struct_0(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.23/0.51  fof(f85,plain,(
% 0.23/0.51    spl8_4 <=> m1_connsp_2(sK5,sK3,sK6)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.23/0.51  fof(f274,plain,(
% 0.23/0.51    spl8_39 <=> ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.23/0.51  fof(f277,plain,(
% 0.23/0.51    ~r1_tarski(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | (~spl8_4 | ~spl8_39)),
% 0.23/0.51    inference(resolution,[],[f275,f86])).
% 0.23/0.51  fof(f86,plain,(
% 0.23/0.51    m1_connsp_2(sK5,sK3,sK6) | ~spl8_4),
% 0.23/0.51    inference(avatar_component_clause,[],[f85])).
% 0.23/0.51  fof(f275,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) ) | ~spl8_39),
% 0.23/0.51    inference(avatar_component_clause,[],[f274])).
% 0.23/0.51  fof(f276,plain,(
% 0.23/0.51    spl8_1 | ~spl8_7 | ~spl8_24 | spl8_39 | ~spl8_34 | ~spl8_38),
% 0.23/0.51    inference(avatar_split_clause,[],[f271,f268,f233,f274,f167,f97,f71])).
% 0.23/0.51  fof(f71,plain,(
% 0.23/0.51    spl8_1 <=> r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.23/0.51  fof(f97,plain,(
% 0.23/0.51    spl8_7 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.23/0.51  fof(f268,plain,(
% 0.23/0.51    spl8_38 <=> ! [X1,X0] : (~r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),X0) | ~r1_tarski(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(X1,sK3,X0) | r1_tmap_1(sK3,sK1,sK4,X0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.23/0.51  fof(f271,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(X0,sK3,sK6) | r1_tmap_1(sK3,sK1,sK4,sK6)) ) | (~spl8_34 | ~spl8_38)),
% 0.23/0.51    inference(resolution,[],[f269,f234])).
% 0.23/0.51  fof(f234,plain,(
% 0.23/0.51    r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK6) | ~spl8_34),
% 0.23/0.51    inference(avatar_component_clause,[],[f233])).
% 0.23/0.51  fof(f269,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),X0) | ~r1_tarski(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(X1,sK3,X0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | ~spl8_38),
% 0.23/0.51    inference(avatar_component_clause,[],[f268])).
% 0.23/0.51  fof(f270,plain,(
% 0.23/0.51    spl8_16 | spl8_38 | ~spl8_9 | ~spl8_29 | ~spl8_37),
% 0.23/0.51    inference(avatar_split_clause,[],[f265,f261,f204,f105,f268,f133])).
% 0.23/0.51  fof(f204,plain,(
% 0.23/0.51    spl8_29 <=> k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.23/0.51  fof(f261,plain,(
% 0.23/0.51    spl8_37 <=> ! [X1,X0,X2] : (~m1_connsp_2(X0,sK3,X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~r1_tmap_1(X2,sK1,k2_tmap_1(sK3,sK1,sK4,X2),X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X2)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.23/0.51  fof(f265,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | v2_struct_0(sK2) | ~m1_connsp_2(X1,sK3,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tarski(X1,u1_struct_0(sK2))) ) | (~spl8_9 | ~spl8_29 | ~spl8_37)),
% 0.23/0.51    inference(forward_demodulation,[],[f264,f205])).
% 0.23/0.51  fof(f205,plain,(
% 0.23/0.51    k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) | ~spl8_29),
% 0.23/0.51    inference(avatar_component_clause,[],[f204])).
% 0.23/0.51  fof(f264,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tmap_1(sK3,sK1,sK4,X0) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),X0) | v2_struct_0(sK2) | ~m1_connsp_2(X1,sK3,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tarski(X1,u1_struct_0(sK2))) ) | (~spl8_9 | ~spl8_37)),
% 0.23/0.51    inference(resolution,[],[f262,f106])).
% 0.23/0.51  fof(f106,plain,(
% 0.23/0.51    m1_pre_topc(sK2,sK3) | ~spl8_9),
% 0.23/0.51    inference(avatar_component_clause,[],[f105])).
% 0.23/0.51  fof(f262,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,sK3) | r1_tmap_1(sK3,sK1,sK4,X1) | ~r1_tmap_1(X2,sK1,k2_tmap_1(sK3,sK1,sK4,X2),X1) | v2_struct_0(X2) | ~m1_connsp_2(X0,sK3,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X2))) ) | ~spl8_37),
% 0.23/0.51    inference(avatar_component_clause,[],[f261])).
% 0.23/0.51  fof(f263,plain,(
% 0.23/0.51    spl8_19 | ~spl8_18 | ~spl8_17 | spl8_14 | ~spl8_25 | ~spl8_26 | ~spl8_10 | spl8_37 | ~spl8_11 | ~spl8_12),
% 0.23/0.51    inference(avatar_split_clause,[],[f259,f117,f113,f261,f109,f177,f174,f125,f137,f141,f145])).
% 0.23/0.51  fof(f145,plain,(
% 0.23/0.51    spl8_19 <=> v2_struct_0(sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.23/0.51  fof(f141,plain,(
% 0.23/0.51    spl8_18 <=> v2_pre_topc(sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.23/0.51  % (11172)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.51  fof(f137,plain,(
% 0.23/0.51    spl8_17 <=> l1_pre_topc(sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.23/0.51  fof(f125,plain,(
% 0.23/0.51    spl8_14 <=> v2_struct_0(sK3)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.23/0.51  fof(f174,plain,(
% 0.23/0.51    spl8_25 <=> v2_pre_topc(sK3)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.23/0.51  fof(f177,plain,(
% 0.23/0.51    spl8_26 <=> l1_pre_topc(sK3)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.23/0.51  fof(f109,plain,(
% 0.23/0.51    spl8_10 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.23/0.51  fof(f113,plain,(
% 0.23/0.51    spl8_11 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.23/0.51  fof(f117,plain,(
% 0.23/0.51    spl8_12 <=> v1_funct_1(sK4)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.23/0.51  % (11159)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.23/0.51  fof(f259,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK3,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | v2_struct_0(X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r1_tmap_1(X2,sK1,k2_tmap_1(sK3,sK1,sK4,X2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | (~spl8_11 | ~spl8_12)),
% 0.23/0.51    inference(resolution,[],[f248,f114])).
% 0.23/0.51  fof(f114,plain,(
% 0.23/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl8_11),
% 0.23/0.51    inference(avatar_component_clause,[],[f113])).
% 0.23/0.51  fof(f248,plain,(
% 0.23/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_connsp_2(X4,X2,X3) | ~r1_tarski(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3) | r1_tmap_1(X2,X1,sK4,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl8_12),
% 0.23/0.51    inference(resolution,[],[f68,f118])).
% 0.23/0.51  fof(f118,plain,(
% 0.23/0.51    v1_funct_1(sK4) | ~spl8_12),
% 0.23/0.51    inference(avatar_component_clause,[],[f117])).
% 0.23/0.51  fof(f68,plain,(
% 0.23/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | r1_tmap_1(X1,X0,X2,X6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.51    inference(equality_resolution,[],[f64])).
% 0.23/0.51  fof(f64,plain,(
% 0.23/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f36])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.51    inference(nnf_transformation,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.51    inference(flattening,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.23/0.51  fof(f254,plain,(
% 0.23/0.51    ~spl8_7 | spl8_36 | ~spl8_1 | ~spl8_35),
% 0.23/0.51    inference(avatar_split_clause,[],[f249,f245,f71,f252,f97])).
% 0.23/0.51  fof(f245,plain,(
% 0.23/0.51    spl8_35 <=> ! [X1,X0,X2] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X0) | ~m1_pre_topc(X0,X2) | r1_tmap_1(X0,sK1,k3_tmap_1(X2,sK1,sK3,X0,sK4),X1) | ~r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.23/0.51  fof(f249,plain,(
% 0.23/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X1))) ) | (~spl8_1 | ~spl8_35)),
% 0.23/0.51    inference(resolution,[],[f246,f77])).
% 0.23/0.51  fof(f77,plain,(
% 0.23/0.51    r1_tmap_1(sK3,sK1,sK4,sK6) | ~spl8_1),
% 0.23/0.51    inference(avatar_component_clause,[],[f71])).
% 0.23/0.51  fof(f246,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_tmap_1(sK3,sK1,sK4,X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X0) | ~m1_pre_topc(X0,X2) | r1_tmap_1(X0,sK1,k3_tmap_1(X2,sK1,sK3,X0,sK4),X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0))) ) | ~spl8_35),
% 0.23/0.51    inference(avatar_component_clause,[],[f245])).
% 0.23/0.51  fof(f247,plain,(
% 0.23/0.51    spl8_19 | ~spl8_18 | ~spl8_17 | spl8_14 | ~spl8_10 | spl8_35 | ~spl8_11 | ~spl8_12),
% 0.23/0.51    inference(avatar_split_clause,[],[f243,f117,f113,f245,f109,f125,f137,f141,f145])).
% 0.23/0.51  fof(f243,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r1_tmap_1(sK3,sK1,sK4,X1) | r1_tmap_1(X0,sK1,k3_tmap_1(X2,sK1,sK3,X0,sK4),X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | (~spl8_11 | ~spl8_12)),
% 0.23/0.51    inference(resolution,[],[f242,f114])).
% 0.23/0.51  fof(f242,plain,(
% 0.23/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,u1_struct_0(X3)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,sK4,X2) | r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,sK4),X2) | ~m1_pre_topc(X3,X4) | v2_struct_0(X3) | ~m1_pre_topc(X0,X4) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) ) | ~spl8_12),
% 0.23/0.51    inference(resolution,[],[f67,f118])).
% 0.23/0.51  fof(f67,plain,(
% 0.23/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.51    inference(equality_resolution,[],[f61])).
% 0.23/0.51  fof(f61,plain,(
% 0.23/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.51    inference(flattening,[],[f15])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.23/0.51  fof(f239,plain,(
% 0.23/0.51    ~spl8_34 | spl8_2 | ~spl8_3 | ~spl8_33),
% 0.23/0.51    inference(avatar_split_clause,[],[f237,f228,f81,f74,f233])).
% 0.23/0.51  fof(f74,plain,(
% 0.23/0.51    spl8_2 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.23/0.51  fof(f81,plain,(
% 0.23/0.51    spl8_3 <=> sK6 = sK7),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.23/0.51  fof(f237,plain,(
% 0.23/0.51    ~r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK6) | (spl8_2 | ~spl8_3 | ~spl8_33)),
% 0.23/0.51    inference(forward_demodulation,[],[f236,f229])).
% 0.23/0.51  fof(f236,plain,(
% 0.23/0.51    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | (spl8_2 | ~spl8_3)),
% 0.23/0.51    inference(forward_demodulation,[],[f75,f82])).
% 0.23/0.51  fof(f82,plain,(
% 0.23/0.51    sK6 = sK7 | ~spl8_3),
% 0.23/0.51    inference(avatar_component_clause,[],[f81])).
% 0.23/0.51  fof(f75,plain,(
% 0.23/0.51    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | spl8_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f74])).
% 0.23/0.51  fof(f235,plain,(
% 0.23/0.51    spl8_34 | ~spl8_23 | ~spl8_33),
% 0.23/0.51    inference(avatar_split_clause,[],[f231,f228,f162,f233])).
% 0.23/0.51  fof(f162,plain,(
% 0.23/0.51    spl8_23 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.23/0.51  fof(f231,plain,(
% 0.23/0.51    r1_tmap_1(sK2,sK1,k7_relat_1(sK4,u1_struct_0(sK2)),sK6) | (~spl8_23 | ~spl8_33)),
% 0.23/0.51    inference(superposition,[],[f163,f229])).
% 0.23/0.51  fof(f163,plain,(
% 0.23/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~spl8_23),
% 0.23/0.51    inference(avatar_component_clause,[],[f162])).
% 0.23/0.51  fof(f230,plain,(
% 0.23/0.51    ~spl8_15 | spl8_33 | ~spl8_9 | ~spl8_28 | ~spl8_29 | ~spl8_32),
% 0.23/0.51    inference(avatar_split_clause,[],[f225,f219,f204,f197,f105,f228,f129])).
% 0.23/0.51  fof(f197,plain,(
% 0.23/0.51    spl8_28 <=> k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.23/0.51  fof(f219,plain,(
% 0.23/0.51    spl8_32 <=> ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | ~m1_pre_topc(X0,sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.23/0.51  fof(f225,plain,(
% 0.23/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | (~spl8_9 | ~spl8_28 | ~spl8_29 | ~spl8_32)),
% 0.23/0.51    inference(forward_demodulation,[],[f224,f205])).
% 0.23/0.51  fof(f224,plain,(
% 0.23/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) | ~m1_pre_topc(sK2,sK0) | (~spl8_9 | ~spl8_28 | ~spl8_32)),
% 0.23/0.51    inference(forward_demodulation,[],[f223,f198])).
% 0.23/0.51  fof(f198,plain,(
% 0.23/0.51    k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl8_28),
% 0.23/0.51    inference(avatar_component_clause,[],[f197])).
% 0.23/0.51  fof(f223,plain,(
% 0.23/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | (~spl8_9 | ~spl8_32)),
% 0.23/0.51    inference(resolution,[],[f220,f106])).
% 0.23/0.51  fof(f220,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | ~m1_pre_topc(X0,sK0)) ) | ~spl8_32),
% 0.23/0.51    inference(avatar_component_clause,[],[f219])).
% 0.23/0.51  fof(f222,plain,(
% 0.23/0.51    spl8_32 | ~spl8_20 | ~spl8_21 | spl8_22 | ~spl8_13 | ~spl8_31),
% 0.23/0.51    inference(avatar_split_clause,[],[f217,f214,f121,f157,f153,f149,f219])).
% 0.23/0.51  fof(f214,plain,(
% 0.23/0.51    spl8_31 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,X1) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.23/0.51  fof(f217,plain,(
% 0.23/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) ) | (~spl8_13 | ~spl8_31)),
% 0.23/0.51    inference(resolution,[],[f215,f122])).
% 0.23/0.51  fof(f215,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,X1) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)) ) | ~spl8_31),
% 0.23/0.51    inference(avatar_component_clause,[],[f214])).
% 0.23/0.51  fof(f216,plain,(
% 0.23/0.51    spl8_19 | ~spl8_18 | ~spl8_17 | spl8_31 | ~spl8_10 | ~spl8_11 | ~spl8_12),
% 0.23/0.51    inference(avatar_split_clause,[],[f212,f117,f113,f109,f214,f137,f141,f145])).
% 0.23/0.52  fof(f212,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl8_11 | ~spl8_12)),
% 0.23/0.52    inference(resolution,[],[f211,f114])).
% 0.23/0.52  fof(f211,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl8_12),
% 0.23/0.52    inference(resolution,[],[f60,f118])).
% 0.23/0.52  fof(f60,plain,(
% 0.23/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f14])).
% 0.23/0.52  fof(f14,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.52    inference(flattening,[],[f13])).
% 0.23/0.52  fof(f13,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.23/0.52  fof(f207,plain,(
% 0.23/0.52    ~spl8_12 | ~spl8_10 | spl8_29 | ~spl8_28),
% 0.23/0.52    inference(avatar_split_clause,[],[f201,f197,f204,f109,f117])).
% 0.23/0.52  fof(f201,plain,(
% 0.23/0.52    k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~spl8_28),
% 0.23/0.52    inference(superposition,[],[f66,f198])).
% 0.23/0.52  fof(f66,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f24])).
% 0.23/0.52  fof(f24,plain,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.23/0.52    inference(flattening,[],[f23])).
% 0.23/0.52  fof(f23,plain,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.23/0.52    inference(ennf_transformation,[],[f1])).
% 0.23/0.52  fof(f1,axiom,(
% 0.23/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.23/0.52  fof(f199,plain,(
% 0.23/0.52    spl8_28 | ~spl8_9 | ~spl8_27),
% 0.23/0.52    inference(avatar_split_clause,[],[f195,f183,f105,f197])).
% 0.23/0.52  fof(f183,plain,(
% 0.23/0.52    spl8_27 <=> ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.23/0.52  fof(f195,plain,(
% 0.23/0.52    k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl8_9 | ~spl8_27)),
% 0.23/0.52    inference(resolution,[],[f184,f106])).
% 0.23/0.52  fof(f184,plain,(
% 0.23/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl8_27),
% 0.23/0.52    inference(avatar_component_clause,[],[f183])).
% 0.23/0.52  fof(f194,plain,(
% 0.23/0.52    ~spl8_20 | ~spl8_13 | spl8_26),
% 0.23/0.52    inference(avatar_split_clause,[],[f193,f177,f121,f149])).
% 0.23/0.52  fof(f193,plain,(
% 0.23/0.52    ~l1_pre_topc(sK0) | (~spl8_13 | spl8_26)),
% 0.23/0.52    inference(resolution,[],[f192,f122])).
% 0.23/0.52  fof(f192,plain,(
% 0.23/0.52    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl8_26),
% 0.23/0.52    inference(resolution,[],[f178,f59])).
% 0.23/0.52  fof(f59,plain,(
% 0.23/0.52    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f12])).
% 0.23/0.52  fof(f12,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.52    inference(ennf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.23/0.52  fof(f178,plain,(
% 0.23/0.52    ~l1_pre_topc(sK3) | spl8_26),
% 0.23/0.52    inference(avatar_component_clause,[],[f177])).
% 0.23/0.52  fof(f191,plain,(
% 0.23/0.52    ~spl8_21 | ~spl8_20 | ~spl8_13 | spl8_25),
% 0.23/0.52    inference(avatar_split_clause,[],[f188,f174,f121,f149,f153])).
% 0.23/0.52  fof(f188,plain,(
% 0.23/0.52    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_13 | spl8_25)),
% 0.23/0.52    inference(resolution,[],[f187,f122])).
% 0.23/0.52  fof(f187,plain,(
% 0.23/0.52    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl8_25),
% 0.23/0.52    inference(resolution,[],[f175,f65])).
% 0.23/0.52  fof(f65,plain,(
% 0.23/0.52    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f22])).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.52    inference(flattening,[],[f21])).
% 0.23/0.52  fof(f21,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f2])).
% 0.23/0.52  fof(f2,axiom,(
% 0.23/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.23/0.52  fof(f175,plain,(
% 0.23/0.52    ~v2_pre_topc(sK3) | spl8_25),
% 0.23/0.52    inference(avatar_component_clause,[],[f174])).
% 0.23/0.52  fof(f186,plain,(
% 0.23/0.52    spl8_14 | ~spl8_25 | ~spl8_26 | spl8_19 | ~spl8_18 | ~spl8_17 | spl8_27 | ~spl8_10 | ~spl8_11 | ~spl8_12),
% 0.23/0.52    inference(avatar_split_clause,[],[f171,f117,f113,f109,f183,f137,f141,f145,f177,f174,f125])).
% 0.23/0.52  fof(f171,plain,(
% 0.23/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (~spl8_11 | ~spl8_12)),
% 0.23/0.52    inference(resolution,[],[f170,f114])).
% 0.23/0.52  fof(f170,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl8_12),
% 0.23/0.52    inference(resolution,[],[f62,f118])).
% 0.23/0.52  fof(f62,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f18])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.52    inference(flattening,[],[f17])).
% 0.23/0.52  fof(f17,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f4])).
% 0.23/0.52  fof(f4,axiom,(
% 0.23/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.23/0.52  fof(f169,plain,(
% 0.23/0.52    spl8_24 | ~spl8_3 | ~spl8_6),
% 0.23/0.52    inference(avatar_split_clause,[],[f165,f93,f81,f167])).
% 0.23/0.52  fof(f93,plain,(
% 0.23/0.52    spl8_6 <=> m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.23/0.52  fof(f165,plain,(
% 0.23/0.52    m1_subset_1(sK6,u1_struct_0(sK2)) | (~spl8_3 | ~spl8_6)),
% 0.23/0.52    inference(superposition,[],[f94,f82])).
% 0.23/0.52  fof(f94,plain,(
% 0.23/0.52    m1_subset_1(sK7,u1_struct_0(sK2)) | ~spl8_6),
% 0.23/0.52    inference(avatar_component_clause,[],[f93])).
% 0.23/0.52  fof(f164,plain,(
% 0.23/0.52    spl8_23 | ~spl8_2 | ~spl8_3),
% 0.23/0.52    inference(avatar_split_clause,[],[f160,f81,f74,f162])).
% 0.23/0.52  fof(f160,plain,(
% 0.23/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | (~spl8_2 | ~spl8_3)),
% 0.23/0.52    inference(forward_demodulation,[],[f78,f82])).
% 0.23/0.52  fof(f78,plain,(
% 0.23/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~spl8_2),
% 0.23/0.52    inference(avatar_component_clause,[],[f74])).
% 0.23/0.52  fof(f159,plain,(
% 0.23/0.52    ~spl8_22),
% 0.23/0.52    inference(avatar_split_clause,[],[f37,f157])).
% 0.23/0.52  fof(f37,plain,(
% 0.23/0.52    ~v2_struct_0(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f35,plain,(
% 0.23/0.52    ((((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = sK7 & m1_connsp_2(sK5,sK3,sK6) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f26,f34,f33,f32,f31,f30,f29,f28,f27])).
% 0.23/0.52  % (11160)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.52  fof(f27,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f28,plain,(
% 0.23/0.52    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f29,plain,(
% 0.23/0.52    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f30,plain,(
% 0.23/0.52    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,X4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,sK3,X6) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f31,plain,(
% 0.23/0.52    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,X4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,sK3,X6) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,X6)) & X6 = X7 & m1_connsp_2(X5,sK3,X6) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,X6)) & X6 = X7 & m1_connsp_2(X5,sK3,X6) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,X6)) & X6 = X7 & m1_connsp_2(sK5,sK3,X6) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  % (11176)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.23/0.52  fof(f33,plain,(
% 0.23/0.52    ? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,X6)) & X6 = X7 & m1_connsp_2(sK5,sK3,X6) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = X7 & m1_connsp_2(sK5,sK3,sK6) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f34,plain,(
% 0.23/0.52    ? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = X7 & m1_connsp_2(sK5,sK3,sK6) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(X7,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = sK7 & m1_connsp_2(sK5,sK3,sK6) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK7,u1_struct_0(sK2)))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f26,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.52    inference(flattening,[],[f25])).
% 0.23/0.52  fof(f25,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.52    inference(nnf_transformation,[],[f11])).
% 0.23/0.52  fof(f11,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.52    inference(flattening,[],[f10])).
% 0.23/0.52  fof(f10,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2)))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f9])).
% 0.23/0.52  fof(f9,negated_conjecture,(
% 0.23/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.23/0.52    inference(negated_conjecture,[],[f8])).
% 0.23/0.52  fof(f8,conjecture,(
% 0.23/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.23/0.52  fof(f155,plain,(
% 0.23/0.52    spl8_21),
% 0.23/0.52    inference(avatar_split_clause,[],[f38,f153])).
% 0.23/0.52  fof(f38,plain,(
% 0.23/0.52    v2_pre_topc(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f151,plain,(
% 0.23/0.52    spl8_20),
% 0.23/0.52    inference(avatar_split_clause,[],[f39,f149])).
% 0.23/0.52  fof(f39,plain,(
% 0.23/0.52    l1_pre_topc(sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f147,plain,(
% 0.23/0.52    ~spl8_19),
% 0.23/0.52    inference(avatar_split_clause,[],[f40,f145])).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    ~v2_struct_0(sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f143,plain,(
% 0.23/0.52    spl8_18),
% 0.23/0.52    inference(avatar_split_clause,[],[f41,f141])).
% 0.23/0.52  fof(f41,plain,(
% 0.23/0.52    v2_pre_topc(sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f139,plain,(
% 0.23/0.52    spl8_17),
% 0.23/0.52    inference(avatar_split_clause,[],[f42,f137])).
% 0.23/0.52  fof(f42,plain,(
% 0.23/0.52    l1_pre_topc(sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f135,plain,(
% 0.23/0.52    ~spl8_16),
% 0.23/0.52    inference(avatar_split_clause,[],[f43,f133])).
% 0.23/0.52  fof(f43,plain,(
% 0.23/0.52    ~v2_struct_0(sK2)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f131,plain,(
% 0.23/0.52    spl8_15),
% 0.23/0.52    inference(avatar_split_clause,[],[f44,f129])).
% 0.23/0.52  fof(f44,plain,(
% 0.23/0.52    m1_pre_topc(sK2,sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f127,plain,(
% 0.23/0.52    ~spl8_14),
% 0.23/0.52    inference(avatar_split_clause,[],[f45,f125])).
% 0.23/0.52  fof(f45,plain,(
% 0.23/0.52    ~v2_struct_0(sK3)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f123,plain,(
% 0.23/0.52    spl8_13),
% 0.23/0.52    inference(avatar_split_clause,[],[f46,f121])).
% 0.23/0.52  fof(f46,plain,(
% 0.23/0.52    m1_pre_topc(sK3,sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f119,plain,(
% 0.23/0.52    spl8_12),
% 0.23/0.52    inference(avatar_split_clause,[],[f47,f117])).
% 0.23/0.52  fof(f47,plain,(
% 0.23/0.52    v1_funct_1(sK4)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f115,plain,(
% 0.23/0.52    spl8_11),
% 0.23/0.52    inference(avatar_split_clause,[],[f48,f113])).
% 0.23/0.52  fof(f48,plain,(
% 0.23/0.52    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f111,plain,(
% 0.23/0.52    spl8_10),
% 0.23/0.52    inference(avatar_split_clause,[],[f49,f109])).
% 0.23/0.52  fof(f49,plain,(
% 0.23/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f107,plain,(
% 0.23/0.52    spl8_9),
% 0.23/0.52    inference(avatar_split_clause,[],[f50,f105])).
% 0.23/0.52  fof(f50,plain,(
% 0.23/0.52    m1_pre_topc(sK2,sK3)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f103,plain,(
% 0.23/0.52    spl8_8),
% 0.23/0.52    inference(avatar_split_clause,[],[f51,f101])).
% 0.23/0.52  fof(f51,plain,(
% 0.23/0.52    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f99,plain,(
% 0.23/0.52    spl8_7),
% 0.23/0.52    inference(avatar_split_clause,[],[f52,f97])).
% 0.23/0.52  fof(f52,plain,(
% 0.23/0.52    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  % (11158)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.52  fof(f95,plain,(
% 0.23/0.52    spl8_6),
% 0.23/0.52    inference(avatar_split_clause,[],[f53,f93])).
% 0.23/0.52  fof(f53,plain,(
% 0.23/0.52    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f91,plain,(
% 0.23/0.52    spl8_5),
% 0.23/0.52    inference(avatar_split_clause,[],[f54,f89])).
% 0.23/0.52  fof(f54,plain,(
% 0.23/0.52    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f87,plain,(
% 0.23/0.52    spl8_4),
% 0.23/0.52    inference(avatar_split_clause,[],[f55,f85])).
% 0.23/0.52  fof(f55,plain,(
% 0.23/0.52    m1_connsp_2(sK5,sK3,sK6)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f83,plain,(
% 0.23/0.52    spl8_3),
% 0.23/0.52    inference(avatar_split_clause,[],[f56,f81])).
% 0.23/0.52  fof(f56,plain,(
% 0.23/0.52    sK6 = sK7),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f79,plain,(
% 0.23/0.52    spl8_1 | spl8_2),
% 0.23/0.52    inference(avatar_split_clause,[],[f57,f74,f71])).
% 0.23/0.52  fof(f57,plain,(
% 0.23/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f76,plain,(
% 0.23/0.52    ~spl8_1 | ~spl8_2),
% 0.23/0.52    inference(avatar_split_clause,[],[f58,f74,f71])).
% 0.23/0.52  fof(f58,plain,(
% 0.23/0.52    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  % SZS output end Proof for theBenchmark
% 0.23/0.52  % (11163)------------------------------
% 0.23/0.52  % (11163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (11163)Termination reason: Refutation
% 0.23/0.52  
% 0.23/0.52  % (11163)Memory used [KB]: 11001
% 0.23/0.52  % (11163)Time elapsed: 0.048 s
% 0.23/0.52  % (11163)------------------------------
% 0.23/0.52  % (11163)------------------------------
% 0.23/0.52  % (11175)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.23/0.52  % (11156)Success in time 0.156 s
%------------------------------------------------------------------------------
