%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:13 EST 2020

% Result     : Theorem 2.36s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  332 ( 655 expanded)
%              Number of leaves         :   74 ( 288 expanded)
%              Depth                    :   13
%              Number of atoms          : 1835 (4085 expanded)
%              Number of equality atoms :   75 ( 291 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f99,f103,f107,f111,f115,f119,f123,f127,f135,f139,f143,f147,f151,f155,f159,f163,f167,f171,f175,f179,f183,f188,f192,f196,f209,f213,f217,f221,f234,f247,f276,f291,f299,f320,f375,f384,f403,f422,f444,f453,f482,f486,f500,f519,f526,f758,f780,f799,f823,f831,f854,f1162,f1174,f1194,f1225,f1315,f1434,f1449])).

fof(f1449,plain,
    ( ~ spl7_162
    | ~ spl7_74
    | ~ spl7_23
    | ~ spl7_75
    | ~ spl7_201 ),
    inference(avatar_split_clause,[],[f1443,f1432,f517,f181,f514,f1146])).

fof(f1146,plain,
    ( spl7_162
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f514,plain,
    ( spl7_74
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f181,plain,
    ( spl7_23
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f517,plain,
    ( spl7_75
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f1432,plain,
    ( spl7_201
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ v3_pre_topc(k2_struct_0(sK2),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_201])])).

fof(f1443,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_23
    | ~ spl7_75
    | ~ spl7_201 ),
    inference(subsumption_resolution,[],[f1442,f518])).

fof(f518,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f517])).

fof(f1442,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_23
    | ~ spl7_201 ),
    inference(duplicate_literal_removal,[],[f1440])).

fof(f1440,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_23
    | ~ spl7_201 ),
    inference(resolution,[],[f1433,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f181])).

fof(f1433,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k2_struct_0(sK2),X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_201 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f1434,plain,
    ( spl7_201
    | ~ spl7_40
    | ~ spl7_115
    | ~ spl7_169
    | spl7_185 ),
    inference(avatar_split_clause,[],[f1318,f1313,f1192,f852,f274,f1432])).

fof(f274,plain,
    ( spl7_40
  <=> ! [X3,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X2,X0)
        | ~ v3_pre_topc(X3,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | v3_pre_topc(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f852,plain,
    ( spl7_115
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f1192,plain,
    ( spl7_169
  <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_169])])).

fof(f1313,plain,
    ( spl7_185
  <=> v3_pre_topc(k2_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_185])])).

fof(f1318,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ v3_pre_topc(k2_struct_0(sK2),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_40
    | ~ spl7_115
    | ~ spl7_169
    | spl7_185 ),
    inference(subsumption_resolution,[],[f1317,f1193])).

fof(f1193,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ spl7_169 ),
    inference(avatar_component_clause,[],[f1192])).

fof(f1317,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X0)
        | ~ v3_pre_topc(k2_struct_0(sK2),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_40
    | ~ spl7_115
    | spl7_185 ),
    inference(forward_demodulation,[],[f1316,f853])).

fof(f853,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl7_115 ),
    inference(avatar_component_clause,[],[f852])).

fof(f1316,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ v3_pre_topc(k2_struct_0(sK2),X0)
        | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_40
    | spl7_185 ),
    inference(resolution,[],[f1314,f275])).

fof(f275,plain,
    ( ! [X2,X0,X3] :
        ( v3_pre_topc(X3,X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ v3_pre_topc(X3,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f274])).

fof(f1314,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK3)
    | spl7_185 ),
    inference(avatar_component_clause,[],[f1313])).

fof(f1315,plain,
    ( ~ spl7_185
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_65
    | ~ spl7_110
    | ~ spl7_112
    | ~ spl7_173 ),
    inference(avatar_split_clause,[],[f1241,f1223,f829,f821,f442,f165,f133,f125,f121,f117,f101,f1313])).

fof(f101,plain,
    ( spl7_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f117,plain,
    ( spl7_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f121,plain,
    ( spl7_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f125,plain,
    ( spl7_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f133,plain,
    ( spl7_11
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f165,plain,
    ( spl7_19
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f442,plain,
    ( spl7_65
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f821,plain,
    ( spl7_110
  <=> m1_subset_1(sK5,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f829,plain,
    ( spl7_112
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f1223,plain,
    ( spl7_173
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_173])])).

fof(f1241,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK3)
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_65
    | ~ spl7_110
    | ~ spl7_112
    | ~ spl7_173 ),
    inference(forward_demodulation,[],[f1240,f830])).

fof(f830,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_112 ),
    inference(avatar_component_clause,[],[f829])).

fof(f1240,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_65
    | ~ spl7_110
    | ~ spl7_112
    | ~ spl7_173 ),
    inference(subsumption_resolution,[],[f1239,f822])).

fof(f822,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2))
    | ~ spl7_110 ),
    inference(avatar_component_clause,[],[f821])).

fof(f1239,plain,
    ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_65
    | ~ spl7_112
    | ~ spl7_173 ),
    inference(forward_demodulation,[],[f1238,f830])).

fof(f1238,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_65
    | ~ spl7_173 ),
    inference(subsumption_resolution,[],[f1237,f126])).

fof(f126,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1237,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_65
    | ~ spl7_173 ),
    inference(subsumption_resolution,[],[f1236,f102])).

fof(f102,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1236,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_65
    | ~ spl7_173 ),
    inference(subsumption_resolution,[],[f1235,f443])).

fof(f443,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f442])).

fof(f1235,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_173 ),
    inference(subsumption_resolution,[],[f1234,f122])).

fof(f122,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f1234,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl7_7
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_173 ),
    inference(subsumption_resolution,[],[f1233,f118])).

fof(f118,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f1233,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl7_11
    | ~ spl7_19
    | ~ spl7_173 ),
    inference(subsumption_resolution,[],[f1230,f134])).

fof(f134,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1230,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl7_19
    | ~ spl7_173 ),
    inference(resolution,[],[f1224,f166])).

fof(f166,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f1224,plain,
    ( ! [X0,X1] :
        ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | ~ spl7_173 ),
    inference(avatar_component_clause,[],[f1223])).

fof(f1225,plain,
    ( spl7_173
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_28
    | ~ spl7_29
    | ~ spl7_30
    | ~ spl7_107 ),
    inference(avatar_split_clause,[],[f791,f778,f215,f211,f207,f149,f141,f113,f109,f105,f97,f1223])).

fof(f97,plain,
    ( spl7_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f105,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f109,plain,
    ( spl7_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f113,plain,
    ( spl7_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f141,plain,
    ( spl7_13
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f149,plain,
    ( spl7_15
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f207,plain,
    ( spl7_28
  <=> v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f211,plain,
    ( spl7_29
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f215,plain,
    ( spl7_30
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f778,plain,
    ( spl7_107
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4)
        | ~ v3_pre_topc(u1_struct_0(X2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f791,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_28
    | ~ spl7_29
    | ~ spl7_30
    | ~ spl7_107 ),
    inference(subsumption_resolution,[],[f790,f212])).

fof(f212,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f211])).

fof(f790,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_107 ),
    inference(forward_demodulation,[],[f789,f216])).

fof(f216,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f215])).

fof(f789,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_107 ),
    inference(subsumption_resolution,[],[f788,f208])).

fof(f208,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f207])).

fof(f788,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_30
    | ~ spl7_107 ),
    inference(forward_demodulation,[],[f787,f216])).

fof(f787,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_15
    | ~ spl7_107 ),
    inference(subsumption_resolution,[],[f786,f142])).

fof(f142,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f786,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_107 ),
    inference(subsumption_resolution,[],[f785,f98])).

fof(f98,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f785,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_107 ),
    inference(subsumption_resolution,[],[f784,f114])).

fof(f114,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f784,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | spl7_4
    | ~ spl7_5
    | spl7_15
    | ~ spl7_107 ),
    inference(subsumption_resolution,[],[f783,f110])).

fof(f110,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f783,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | spl7_4
    | spl7_15
    | ~ spl7_107 ),
    inference(subsumption_resolution,[],[f782,f106])).

fof(f106,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f782,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(u1_struct_0(X0),sK3) )
    | spl7_15
    | ~ spl7_107 ),
    inference(resolution,[],[f779,f150])).

fof(f150,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f779,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r1_tmap_1(X3,X1,sK4,X4)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | ~ l1_pre_topc(X0)
        | ~ v3_pre_topc(u1_struct_0(X2),X3) )
    | ~ spl7_107 ),
    inference(avatar_component_clause,[],[f778])).

fof(f1194,plain,
    ( spl7_169
    | ~ spl7_65
    | ~ spl7_112
    | ~ spl7_166 ),
    inference(avatar_split_clause,[],[f1182,f1172,f829,f442,f1192])).

fof(f1172,plain,
    ( spl7_166
  <=> ! [X0] :
        ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).

fof(f1182,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ spl7_65
    | ~ spl7_112
    | ~ spl7_166 ),
    inference(forward_demodulation,[],[f1179,f830])).

fof(f1179,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ spl7_65
    | ~ spl7_166 ),
    inference(resolution,[],[f1173,f443])).

fof(f1173,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) )
    | ~ spl7_166 ),
    inference(avatar_component_clause,[],[f1172])).

fof(f1174,plain,
    ( ~ spl7_67
    | spl7_166
    | ~ spl7_26
    | ~ spl7_115 ),
    inference(avatar_split_clause,[],[f859,f852,f194,f1172,f465])).

fof(f465,plain,
    ( spl7_67
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f194,plain,
    ( spl7_26
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f859,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK3) )
    | ~ spl7_26
    | ~ spl7_115 ),
    inference(superposition,[],[f195,f853])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f194])).

fof(f1162,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_24
    | spl7_162 ),
    inference(avatar_contradiction_clause,[],[f1160])).

fof(f1160,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_24
    | spl7_162 ),
    inference(unit_resulting_resolution,[],[f122,f126,f138,f1147,f187])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl7_24
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f1147,plain,
    ( ~ v2_pre_topc(sK2)
    | spl7_162 ),
    inference(avatar_component_clause,[],[f1146])).

fof(f138,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f854,plain,
    ( spl7_115
    | ~ spl7_11
    | ~ spl7_109 ),
    inference(avatar_split_clause,[],[f806,f797,f133,f852])).

fof(f797,plain,
    ( spl7_109
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | u1_struct_0(X1) = k2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).

fof(f806,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl7_11
    | ~ spl7_109 ),
    inference(resolution,[],[f798,f134])).

fof(f798,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | u1_struct_0(X1) = k2_struct_0(X1) )
    | ~ spl7_109 ),
    inference(avatar_component_clause,[],[f797])).

fof(f831,plain,
    ( spl7_112
    | ~ spl7_12
    | ~ spl7_109 ),
    inference(avatar_split_clause,[],[f805,f797,f137,f829])).

fof(f805,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_12
    | ~ spl7_109 ),
    inference(resolution,[],[f798,f138])).

fof(f823,plain,
    ( spl7_110
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_109 ),
    inference(avatar_split_clause,[],[f815,f797,f145,f137,f821])).

fof(f145,plain,
    ( spl7_14
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f815,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2))
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_109 ),
    inference(backward_demodulation,[],[f146,f805])).

fof(f146,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f799,plain,
    ( spl7_109
    | ~ spl7_9
    | ~ spl7_103 ),
    inference(avatar_split_clause,[],[f764,f756,f125,f797])).

fof(f756,plain,
    ( spl7_103
  <=> ! [X1,X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f764,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | u1_struct_0(X1) = k2_struct_0(X1) )
    | ~ spl7_9
    | ~ spl7_103 ),
    inference(resolution,[],[f757,f126])).

fof(f757,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,X1)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl7_103 ),
    inference(avatar_component_clause,[],[f756])).

fof(f780,plain,
    ( spl7_107
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_34
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f492,f484,f245,f186,f177,f778])).

fof(f177,plain,
    ( spl7_22
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f245,plain,
    ( spl7_34
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v3_pre_topc(u1_struct_0(X1),X0)
        | v1_tsep_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f484,plain,
    ( spl7_70
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f492,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4)
        | ~ v3_pre_topc(u1_struct_0(X2),X3) )
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_34
    | ~ spl7_70 ),
    inference(subsumption_resolution,[],[f491,f187])).

fof(f491,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4)
        | ~ v3_pre_topc(u1_struct_0(X2),X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl7_22
    | ~ spl7_34
    | ~ spl7_70 ),
    inference(subsumption_resolution,[],[f490,f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f177])).

fof(f490,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4)
        | ~ l1_pre_topc(X3)
        | ~ v3_pre_topc(u1_struct_0(X2),X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl7_34
    | ~ spl7_70 ),
    inference(duplicate_literal_removal,[],[f489])).

fof(f489,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ v3_pre_topc(u1_struct_0(X2),X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl7_34
    | ~ spl7_70 ),
    inference(resolution,[],[f485,f246])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( v1_tsep_1(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v3_pre_topc(u1_struct_0(X1),X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f245])).

fof(f485,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_tsep_1(X2,X3)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) )
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f484])).

fof(f758,plain,
    ( spl7_103
    | ~ spl7_22
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f203,f190,f177,f756])).

fof(f190,plain,
    ( spl7_25
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl7_22
    | ~ spl7_25 ),
    inference(resolution,[],[f191,f178])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f190])).

fof(f526,plain,
    ( ~ spl7_9
    | ~ spl7_12
    | ~ spl7_22
    | spl7_74 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_22
    | spl7_74 ),
    inference(unit_resulting_resolution,[],[f126,f138,f515,f178])).

fof(f515,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_74 ),
    inference(avatar_component_clause,[],[f514])).

fof(f519,plain,
    ( ~ spl7_74
    | spl7_75
    | ~ spl7_17
    | ~ spl7_31
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f505,f498,f219,f157,f517,f514])).

fof(f157,plain,
    ( spl7_17
  <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f219,plain,
    ( spl7_31
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f498,plain,
    ( spl7_72
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f505,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl7_17
    | ~ spl7_31
    | ~ spl7_72 ),
    inference(forward_demodulation,[],[f504,f158])).

fof(f158,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f157])).

fof(f504,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | ~ spl7_31
    | ~ spl7_72 ),
    inference(resolution,[],[f499,f220])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f219])).

fof(f499,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f498])).

fof(f500,plain,
    ( spl7_72
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f463,f451,f420,f137,f125,f121,f117,f101,f498])).

fof(f420,plain,
    ( spl7_62
  <=> sK3 = k1_tsep_1(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f451,plain,
    ( spl7_66
  <=> ! [X1,X0] :
        ( sK3 != k1_tsep_1(X0,X1,sK2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | m1_pre_topc(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f463,plain,
    ( m1_pre_topc(sK2,sK2)
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f462,f118])).

fof(f462,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2)
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f461,f138])).

fof(f461,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2)
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f460,f102])).

fof(f460,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2)
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f459,f126])).

fof(f459,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2)
    | ~ spl7_8
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f458,f122])).

fof(f458,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2)
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(trivial_inequality_removal,[],[f457])).

fof(f457,plain,
    ( sK3 != sK3
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2)
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(duplicate_literal_removal,[],[f456])).

fof(f456,plain,
    ( sK3 != sK3
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK2)
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(superposition,[],[f452,f421])).

fof(f421,plain,
    ( sK3 = k1_tsep_1(sK0,sK2,sK2)
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f420])).

fof(f452,plain,
    ( ! [X0,X1] :
        ( sK3 != k1_tsep_1(X0,X1,sK2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | m1_pre_topc(X1,sK2) )
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f451])).

fof(f486,plain,
    ( spl7_70
    | ~ spl7_1
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f385,f382,f93,f484])).

fof(f93,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f382,plain,
    ( spl7_57
  <=> ! [X1,X3,X0,X2,X4,X6] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f385,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) )
    | ~ spl7_1
    | ~ spl7_57 ),
    inference(resolution,[],[f383,f94])).

fof(f94,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f383,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( ~ v1_funct_1(X4)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) )
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f382])).

fof(f482,plain,
    ( ~ spl7_9
    | ~ spl7_11
    | ~ spl7_22
    | spl7_67 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_22
    | spl7_67 ),
    inference(unit_resulting_resolution,[],[f126,f134,f466,f178])).

fof(f466,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_67 ),
    inference(avatar_component_clause,[],[f465])).

fof(f453,plain,
    ( spl7_66
    | spl7_3
    | ~ spl7_17
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f352,f318,f157,f101,f451])).

fof(f318,plain,
    ( spl7_47
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | m1_pre_topc(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( sK3 != k1_tsep_1(X0,X1,sK2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | m1_pre_topc(X1,sK2) )
    | spl7_3
    | ~ spl7_17
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f349,f102])).

fof(f349,plain,
    ( ! [X0,X1] :
        ( sK3 != k1_tsep_1(X0,X1,sK2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | m1_pre_topc(X1,sK2) )
    | ~ spl7_17
    | ~ spl7_47 ),
    inference(superposition,[],[f319,f158])).

fof(f319,plain,
    ( ! [X2,X0,X1] :
        ( k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0)
        | m1_pre_topc(X1,X2) )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f318])).

fof(f444,plain,
    ( spl7_65
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_44
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f436,f420,f297,f137,f125,f121,f117,f101,f442])).

fof(f297,plain,
    ( spl7_44
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f436,plain,
    ( m1_pre_topc(sK2,sK3)
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_44
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f435,f118])).

fof(f435,plain,
    ( m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_44
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f434,f138])).

fof(f434,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_44
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f433,f102])).

fof(f433,plain,
    ( m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_44
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f432,f126])).

fof(f432,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_8
    | ~ spl7_44
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f431,f122])).

fof(f431,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_44
    | ~ spl7_62 ),
    inference(duplicate_literal_removal,[],[f430])).

fof(f430,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_44
    | ~ spl7_62 ),
    inference(superposition,[],[f298,f421])).

fof(f298,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f297])).

fof(f422,plain,
    ( spl7_62
    | spl7_3
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f410,f401,f157,f137,f101,f420])).

fof(f401,plain,
    ( spl7_60
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f410,plain,
    ( sK3 = k1_tsep_1(sK0,sK2,sK2)
    | spl7_3
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_60 ),
    inference(forward_demodulation,[],[f409,f158])).

fof(f409,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | spl7_3
    | ~ spl7_12
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f406,f138])).

fof(f406,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | spl7_3
    | ~ spl7_60 ),
    inference(resolution,[],[f402,f102])).

fof(f402,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X1,X1) )
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f401])).

fof(f403,plain,
    ( spl7_60
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f308,f289,f125,f121,f117,f401])).

fof(f289,plain,
    ( spl7_42
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f308,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X1,X1) )
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f307,f118])).

fof(f307,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X1,X1) )
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f303,f122])).

fof(f303,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X1,X1) )
    | ~ spl7_9
    | ~ spl7_42 ),
    inference(resolution,[],[f290,f126])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) )
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f289])).

fof(f384,plain,
    ( spl7_57
    | ~ spl7_33
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f376,f373,f232,f382])).

fof(f232,plain,
    ( spl7_33
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X1)
        | m1_pre_topc(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f373,plain,
    ( spl7_55
  <=> ! [X1,X3,X0,X2,X4,X6] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f376,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) )
    | ~ spl7_33
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f374,f233])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f232])).

fof(f374,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ m1_subset_1(X6,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
        | r1_tmap_1(X3,X1,X4,X6) )
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f373])).

fof(f375,plain,(
    spl7_55 ),
    inference(avatar_split_clause,[],[f84,f373])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f320,plain,(
    spl7_47 ),
    inference(avatar_split_clause,[],[f75,f318])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | m1_pre_topc(X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f299,plain,(
    spl7_44 ),
    inference(avatar_split_clause,[],[f74,f297])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f291,plain,(
    spl7_42 ),
    inference(avatar_split_clause,[],[f73,f289])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f276,plain,(
    spl7_40 ),
    inference(avatar_split_clause,[],[f89,f274])).

fof(f89,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(subsumption_resolution,[],[f82,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f82,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f247,plain,(
    spl7_34 ),
    inference(avatar_split_clause,[],[f90,f245])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f85,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f234,plain,(
    spl7_33 ),
    inference(avatar_split_clause,[],[f79,f232])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f221,plain,(
    spl7_31 ),
    inference(avatar_split_clause,[],[f68,f219])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f217,plain,
    ( spl7_30
    | ~ spl7_6
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f201,f190,f113,f215])).

fof(f201,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl7_6
    | ~ spl7_25 ),
    inference(resolution,[],[f191,f114])).

fof(f213,plain,
    ( spl7_29
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f204,f190,f161,f113,f211])).

fof(f161,plain,
    ( spl7_18
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f204,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
    | ~ spl7_6
    | ~ spl7_18
    | ~ spl7_25 ),
    inference(backward_demodulation,[],[f162,f201])).

fof(f162,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f209,plain,
    ( spl7_28
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f205,f190,f153,f113,f207])).

fof(f153,plain,
    ( spl7_16
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f205,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
    | ~ spl7_6
    | ~ spl7_16
    | ~ spl7_25 ),
    inference(backward_demodulation,[],[f154,f201])).

fof(f154,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f196,plain,(
    spl7_26 ),
    inference(avatar_split_clause,[],[f66,f194])).

fof(f192,plain,
    ( spl7_25
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f184,f173,f169,f190])).

fof(f169,plain,
    ( spl7_20
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f173,plain,
    ( spl7_21
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f184,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(resolution,[],[f174,f170])).

fof(f170,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f169])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f173])).

fof(f188,plain,(
    spl7_24 ),
    inference(avatar_split_clause,[],[f78,f186])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f183,plain,(
    spl7_23 ),
    inference(avatar_split_clause,[],[f77,f181])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f179,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f65,f177])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f175,plain,(
    spl7_21 ),
    inference(avatar_split_clause,[],[f63,f173])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f171,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f64,f169])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f167,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f87,f165])).

fof(f87,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f46,f45])).

fof(f45,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f46,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f19])).

fof(f163,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f51,f161])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f159,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f52,f157])).

fof(f52,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f155,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f50,f153])).

fof(f50,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f151,plain,(
    ~ spl7_15 ),
    inference(avatar_split_clause,[],[f47,f149])).

fof(f47,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f147,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f88,f145])).

fof(f88,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f44,f45])).

fof(f44,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f143,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f48,f141])).

fof(f48,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f139,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f56,f137])).

fof(f56,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f135,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f54,f133])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f127,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f62,f125])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f123,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f61,f121])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f60,f117])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f115,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f59,f113])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f58,f109])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f107,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f103,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f55,f101])).

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f53,f97])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f95,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f49,f93])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:57:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (1226)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (1234)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (1220)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (1215)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (1229)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (1228)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (1221)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (1222)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (1230)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.53  % (1224)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.53  % (1216)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (1231)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.54  % (1217)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.54  % (1235)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.54  % (1225)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.55  % (1223)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.55  % (1215)Refutation not found, incomplete strategy% (1215)------------------------------
% 0.22/0.55  % (1215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1219)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.56  % (1218)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (1215)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (1215)Memory used [KB]: 6652
% 0.22/0.56  % (1215)Time elapsed: 0.106 s
% 0.22/0.56  % (1215)------------------------------
% 0.22/0.56  % (1215)------------------------------
% 0.22/0.56  % (1232)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.58/0.58  % (1233)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.58/0.58  % (1227)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.36/0.67  % (1224)Refutation found. Thanks to Tanya!
% 2.36/0.67  % SZS status Theorem for theBenchmark
% 2.36/0.67  % SZS output start Proof for theBenchmark
% 2.36/0.67  fof(f1450,plain,(
% 2.36/0.67    $false),
% 2.36/0.67    inference(avatar_sat_refutation,[],[f95,f99,f103,f107,f111,f115,f119,f123,f127,f135,f139,f143,f147,f151,f155,f159,f163,f167,f171,f175,f179,f183,f188,f192,f196,f209,f213,f217,f221,f234,f247,f276,f291,f299,f320,f375,f384,f403,f422,f444,f453,f482,f486,f500,f519,f526,f758,f780,f799,f823,f831,f854,f1162,f1174,f1194,f1225,f1315,f1434,f1449])).
% 2.36/0.67  fof(f1449,plain,(
% 2.36/0.67    ~spl7_162 | ~spl7_74 | ~spl7_23 | ~spl7_75 | ~spl7_201),
% 2.36/0.67    inference(avatar_split_clause,[],[f1443,f1432,f517,f181,f514,f1146])).
% 2.36/0.67  fof(f1146,plain,(
% 2.36/0.67    spl7_162 <=> v2_pre_topc(sK2)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).
% 2.36/0.67  fof(f514,plain,(
% 2.36/0.67    spl7_74 <=> l1_pre_topc(sK2)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).
% 2.36/0.67  fof(f181,plain,(
% 2.36/0.67    spl7_23 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.36/0.67  fof(f517,plain,(
% 2.36/0.67    spl7_75 <=> m1_pre_topc(sK3,sK2)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).
% 2.36/0.67  fof(f1432,plain,(
% 2.36/0.67    spl7_201 <=> ! [X0] : (~m1_pre_topc(sK3,X0) | ~v3_pre_topc(k2_struct_0(sK2),X0) | ~l1_pre_topc(X0))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_201])])).
% 2.36/0.67  fof(f1443,plain,(
% 2.36/0.67    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl7_23 | ~spl7_75 | ~spl7_201)),
% 2.36/0.67    inference(subsumption_resolution,[],[f1442,f518])).
% 2.36/0.67  fof(f518,plain,(
% 2.36/0.67    m1_pre_topc(sK3,sK2) | ~spl7_75),
% 2.36/0.67    inference(avatar_component_clause,[],[f517])).
% 2.36/0.67  fof(f1442,plain,(
% 2.36/0.67    ~m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl7_23 | ~spl7_201)),
% 2.36/0.67    inference(duplicate_literal_removal,[],[f1440])).
% 2.36/0.67  fof(f1440,plain,(
% 2.36/0.67    ~m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl7_23 | ~spl7_201)),
% 2.36/0.67    inference(resolution,[],[f1433,f182])).
% 2.36/0.67  fof(f182,plain,(
% 2.36/0.67    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl7_23),
% 2.36/0.67    inference(avatar_component_clause,[],[f181])).
% 2.36/0.67  fof(f1433,plain,(
% 2.36/0.67    ( ! [X0] : (~v3_pre_topc(k2_struct_0(sK2),X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | ~spl7_201),
% 2.36/0.67    inference(avatar_component_clause,[],[f1432])).
% 2.36/0.67  fof(f1434,plain,(
% 2.36/0.67    spl7_201 | ~spl7_40 | ~spl7_115 | ~spl7_169 | spl7_185),
% 2.36/0.67    inference(avatar_split_clause,[],[f1318,f1313,f1192,f852,f274,f1432])).
% 2.36/0.67  fof(f274,plain,(
% 2.36/0.67    spl7_40 <=> ! [X3,X0,X2] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 2.36/0.67  fof(f852,plain,(
% 2.36/0.67    spl7_115 <=> u1_struct_0(sK3) = k2_struct_0(sK3)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).
% 2.36/0.67  fof(f1192,plain,(
% 2.36/0.67    spl7_169 <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_169])])).
% 2.36/0.67  fof(f1313,plain,(
% 2.36/0.67    spl7_185 <=> v3_pre_topc(k2_struct_0(sK2),sK3)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_185])])).
% 2.36/0.67  fof(f1318,plain,(
% 2.36/0.67    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~v3_pre_topc(k2_struct_0(sK2),X0) | ~l1_pre_topc(X0)) ) | (~spl7_40 | ~spl7_115 | ~spl7_169 | spl7_185)),
% 2.36/0.67    inference(subsumption_resolution,[],[f1317,f1193])).
% 2.36/0.67  fof(f1193,plain,(
% 2.36/0.67    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) | ~spl7_169),
% 2.36/0.67    inference(avatar_component_clause,[],[f1192])).
% 2.36/0.67  fof(f1317,plain,(
% 2.36/0.67    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_pre_topc(sK3,X0) | ~v3_pre_topc(k2_struct_0(sK2),X0) | ~l1_pre_topc(X0)) ) | (~spl7_40 | ~spl7_115 | spl7_185)),
% 2.36/0.67    inference(forward_demodulation,[],[f1316,f853])).
% 2.36/0.67  fof(f853,plain,(
% 2.36/0.67    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl7_115),
% 2.36/0.67    inference(avatar_component_clause,[],[f852])).
% 2.36/0.67  fof(f1316,plain,(
% 2.36/0.67    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~v3_pre_topc(k2_struct_0(sK2),X0) | ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(X0)) ) | (~spl7_40 | spl7_185)),
% 2.36/0.67    inference(resolution,[],[f1314,f275])).
% 2.36/0.67  fof(f275,plain,(
% 2.36/0.67    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X0)) ) | ~spl7_40),
% 2.36/0.67    inference(avatar_component_clause,[],[f274])).
% 2.36/0.67  fof(f1314,plain,(
% 2.36/0.67    ~v3_pre_topc(k2_struct_0(sK2),sK3) | spl7_185),
% 2.36/0.67    inference(avatar_component_clause,[],[f1313])).
% 2.36/0.67  fof(f1315,plain,(
% 2.36/0.67    ~spl7_185 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_65 | ~spl7_110 | ~spl7_112 | ~spl7_173),
% 2.36/0.67    inference(avatar_split_clause,[],[f1241,f1223,f829,f821,f442,f165,f133,f125,f121,f117,f101,f1313])).
% 2.36/0.67  fof(f101,plain,(
% 2.36/0.67    spl7_3 <=> v2_struct_0(sK2)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.36/0.67  fof(f117,plain,(
% 2.36/0.67    spl7_7 <=> v2_struct_0(sK0)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.36/0.67  fof(f121,plain,(
% 2.36/0.67    spl7_8 <=> v2_pre_topc(sK0)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.36/0.67  fof(f125,plain,(
% 2.36/0.67    spl7_9 <=> l1_pre_topc(sK0)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.36/0.67  fof(f133,plain,(
% 2.36/0.67    spl7_11 <=> m1_pre_topc(sK3,sK0)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 2.36/0.67  fof(f165,plain,(
% 2.36/0.67    spl7_19 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 2.36/0.67  fof(f442,plain,(
% 2.36/0.67    spl7_65 <=> m1_pre_topc(sK2,sK3)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).
% 2.36/0.67  fof(f821,plain,(
% 2.36/0.67    spl7_110 <=> m1_subset_1(sK5,k2_struct_0(sK2))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).
% 2.36/0.67  fof(f829,plain,(
% 2.36/0.67    spl7_112 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).
% 2.36/0.67  fof(f1223,plain,(
% 2.36/0.67    spl7_173 <=> ! [X1,X0] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_173])])).
% 2.36/0.67  fof(f1241,plain,(
% 2.36/0.67    ~v3_pre_topc(k2_struct_0(sK2),sK3) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_65 | ~spl7_110 | ~spl7_112 | ~spl7_173)),
% 2.36/0.67    inference(forward_demodulation,[],[f1240,f830])).
% 2.36/0.67  fof(f830,plain,(
% 2.36/0.67    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl7_112),
% 2.36/0.67    inference(avatar_component_clause,[],[f829])).
% 2.36/0.67  fof(f1240,plain,(
% 2.36/0.67    ~v3_pre_topc(u1_struct_0(sK2),sK3) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_65 | ~spl7_110 | ~spl7_112 | ~spl7_173)),
% 2.36/0.67    inference(subsumption_resolution,[],[f1239,f822])).
% 2.36/0.67  fof(f822,plain,(
% 2.36/0.67    m1_subset_1(sK5,k2_struct_0(sK2)) | ~spl7_110),
% 2.36/0.67    inference(avatar_component_clause,[],[f821])).
% 2.36/0.67  fof(f1239,plain,(
% 2.36/0.67    ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_65 | ~spl7_112 | ~spl7_173)),
% 2.36/0.67    inference(forward_demodulation,[],[f1238,f830])).
% 2.36/0.67  fof(f1238,plain,(
% 2.36/0.67    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_19 | ~spl7_65 | ~spl7_173)),
% 2.36/0.67    inference(subsumption_resolution,[],[f1237,f126])).
% 2.36/0.67  fof(f126,plain,(
% 2.36/0.67    l1_pre_topc(sK0) | ~spl7_9),
% 2.36/0.67    inference(avatar_component_clause,[],[f125])).
% 2.36/0.67  fof(f1237,plain,(
% 2.36/0.67    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_11 | ~spl7_19 | ~spl7_65 | ~spl7_173)),
% 2.36/0.67    inference(subsumption_resolution,[],[f1236,f102])).
% 2.36/0.67  fof(f102,plain,(
% 2.36/0.67    ~v2_struct_0(sK2) | spl7_3),
% 2.36/0.67    inference(avatar_component_clause,[],[f101])).
% 2.36/0.67  fof(f1236,plain,(
% 2.36/0.67    ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (spl7_7 | ~spl7_8 | ~spl7_11 | ~spl7_19 | ~spl7_65 | ~spl7_173)),
% 2.36/0.67    inference(subsumption_resolution,[],[f1235,f443])).
% 2.36/0.67  fof(f443,plain,(
% 2.36/0.67    m1_pre_topc(sK2,sK3) | ~spl7_65),
% 2.36/0.67    inference(avatar_component_clause,[],[f442])).
% 2.36/0.67  fof(f1235,plain,(
% 2.36/0.67    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (spl7_7 | ~spl7_8 | ~spl7_11 | ~spl7_19 | ~spl7_173)),
% 2.36/0.67    inference(subsumption_resolution,[],[f1234,f122])).
% 2.36/0.67  fof(f122,plain,(
% 2.36/0.67    v2_pre_topc(sK0) | ~spl7_8),
% 2.36/0.67    inference(avatar_component_clause,[],[f121])).
% 2.36/0.67  fof(f1234,plain,(
% 2.36/0.67    ~v2_pre_topc(sK0) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (spl7_7 | ~spl7_11 | ~spl7_19 | ~spl7_173)),
% 2.36/0.67    inference(subsumption_resolution,[],[f1233,f118])).
% 2.36/0.67  fof(f118,plain,(
% 2.36/0.67    ~v2_struct_0(sK0) | spl7_7),
% 2.36/0.67    inference(avatar_component_clause,[],[f117])).
% 2.36/0.67  fof(f1233,plain,(
% 2.36/0.67    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl7_11 | ~spl7_19 | ~spl7_173)),
% 2.36/0.67    inference(subsumption_resolution,[],[f1230,f134])).
% 2.36/0.67  fof(f134,plain,(
% 2.36/0.67    m1_pre_topc(sK3,sK0) | ~spl7_11),
% 2.36/0.67    inference(avatar_component_clause,[],[f133])).
% 2.36/0.67  fof(f1230,plain,(
% 2.36/0.67    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl7_19 | ~spl7_173)),
% 2.36/0.67    inference(resolution,[],[f1224,f166])).
% 2.36/0.67  fof(f166,plain,(
% 2.36/0.67    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl7_19),
% 2.36/0.67    inference(avatar_component_clause,[],[f165])).
% 2.36/0.67  fof(f1224,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | ~spl7_173),
% 2.36/0.67    inference(avatar_component_clause,[],[f1223])).
% 2.36/0.67  fof(f1225,plain,(
% 2.36/0.67    spl7_173 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_28 | ~spl7_29 | ~spl7_30 | ~spl7_107),
% 2.36/0.67    inference(avatar_split_clause,[],[f791,f778,f215,f211,f207,f149,f141,f113,f109,f105,f97,f1223])).
% 2.36/0.67  fof(f97,plain,(
% 2.36/0.67    spl7_2 <=> v2_struct_0(sK3)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.36/0.67  fof(f105,plain,(
% 2.36/0.67    spl7_4 <=> v2_struct_0(sK1)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.36/0.67  fof(f109,plain,(
% 2.36/0.67    spl7_5 <=> v2_pre_topc(sK1)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.36/0.67  fof(f113,plain,(
% 2.36/0.67    spl7_6 <=> l1_pre_topc(sK1)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.36/0.67  fof(f141,plain,(
% 2.36/0.67    spl7_13 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.36/0.67  fof(f149,plain,(
% 2.36/0.67    spl7_15 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.36/0.67  fof(f207,plain,(
% 2.36/0.67    spl7_28 <=> v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 2.36/0.67  fof(f211,plain,(
% 2.36/0.67    spl7_29 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 2.36/0.67  fof(f215,plain,(
% 2.36/0.67    spl7_30 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 2.36/0.67  fof(f778,plain,(
% 2.36/0.67    spl7_107 <=> ! [X1,X3,X0,X2,X4] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4) | ~v3_pre_topc(u1_struct_0(X2),X3))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).
% 2.36/0.67  fof(f791,plain,(
% 2.36/0.67    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_28 | ~spl7_29 | ~spl7_30 | ~spl7_107)),
% 2.36/0.67    inference(subsumption_resolution,[],[f790,f212])).
% 2.36/0.67  fof(f212,plain,(
% 2.36/0.67    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | ~spl7_29),
% 2.36/0.67    inference(avatar_component_clause,[],[f211])).
% 2.36/0.67  fof(f790,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_28 | ~spl7_30 | ~spl7_107)),
% 2.36/0.67    inference(forward_demodulation,[],[f789,f216])).
% 2.36/0.67  fof(f216,plain,(
% 2.36/0.67    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl7_30),
% 2.36/0.67    inference(avatar_component_clause,[],[f215])).
% 2.36/0.67  fof(f789,plain,(
% 2.36/0.67    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_28 | ~spl7_30 | ~spl7_107)),
% 2.36/0.67    inference(subsumption_resolution,[],[f788,f208])).
% 2.36/0.67  fof(f208,plain,(
% 2.36/0.67    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | ~spl7_28),
% 2.36/0.67    inference(avatar_component_clause,[],[f207])).
% 2.36/0.67  fof(f788,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_30 | ~spl7_107)),
% 2.36/0.67    inference(forward_demodulation,[],[f787,f216])).
% 2.36/0.67  fof(f787,plain,(
% 2.36/0.67    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_15 | ~spl7_107)),
% 2.36/0.67    inference(subsumption_resolution,[],[f786,f142])).
% 2.36/0.67  fof(f142,plain,(
% 2.36/0.67    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl7_13),
% 2.36/0.67    inference(avatar_component_clause,[],[f141])).
% 2.36/0.67  fof(f786,plain,(
% 2.36/0.67    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_107)),
% 2.36/0.67    inference(subsumption_resolution,[],[f785,f98])).
% 2.36/0.67  fof(f98,plain,(
% 2.36/0.67    ~v2_struct_0(sK3) | spl7_2),
% 2.36/0.67    inference(avatar_component_clause,[],[f97])).
% 2.36/0.67  fof(f785,plain,(
% 2.36/0.67    ( ! [X0,X1] : (v2_struct_0(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_107)),
% 2.36/0.67    inference(subsumption_resolution,[],[f784,f114])).
% 2.36/0.67  fof(f114,plain,(
% 2.36/0.67    l1_pre_topc(sK1) | ~spl7_6),
% 2.36/0.67    inference(avatar_component_clause,[],[f113])).
% 2.36/0.67  fof(f784,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | (spl7_4 | ~spl7_5 | spl7_15 | ~spl7_107)),
% 2.36/0.67    inference(subsumption_resolution,[],[f783,f110])).
% 2.36/0.67  fof(f110,plain,(
% 2.36/0.67    v2_pre_topc(sK1) | ~spl7_5),
% 2.36/0.67    inference(avatar_component_clause,[],[f109])).
% 2.36/0.67  fof(f783,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | (spl7_4 | spl7_15 | ~spl7_107)),
% 2.36/0.67    inference(subsumption_resolution,[],[f782,f106])).
% 2.36/0.67  fof(f106,plain,(
% 2.36/0.67    ~v2_struct_0(sK1) | spl7_4),
% 2.36/0.67    inference(avatar_component_clause,[],[f105])).
% 2.36/0.67  fof(f782,plain,(
% 2.36/0.67    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~l1_pre_topc(X1) | ~v3_pre_topc(u1_struct_0(X0),sK3)) ) | (spl7_15 | ~spl7_107)),
% 2.36/0.67    inference(resolution,[],[f779,f150])).
% 2.36/0.67  fof(f150,plain,(
% 2.36/0.67    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl7_15),
% 2.36/0.67    inference(avatar_component_clause,[],[f149])).
% 2.36/0.67  fof(f779,plain,(
% 2.36/0.67    ( ! [X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,sK4,X4) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | ~l1_pre_topc(X0) | ~v3_pre_topc(u1_struct_0(X2),X3)) ) | ~spl7_107),
% 2.36/0.67    inference(avatar_component_clause,[],[f778])).
% 2.36/0.67  fof(f1194,plain,(
% 2.36/0.67    spl7_169 | ~spl7_65 | ~spl7_112 | ~spl7_166),
% 2.36/0.67    inference(avatar_split_clause,[],[f1182,f1172,f829,f442,f1192])).
% 2.36/0.67  fof(f1172,plain,(
% 2.36/0.67    spl7_166 <=> ! [X0] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_pre_topc(X0,sK3))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).
% 2.36/0.67  fof(f1182,plain,(
% 2.36/0.67    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) | (~spl7_65 | ~spl7_112 | ~spl7_166)),
% 2.36/0.67    inference(forward_demodulation,[],[f1179,f830])).
% 2.36/0.67  fof(f1179,plain,(
% 2.36/0.67    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) | (~spl7_65 | ~spl7_166)),
% 2.36/0.67    inference(resolution,[],[f1173,f443])).
% 2.36/0.67  fof(f1173,plain,(
% 2.36/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))) ) | ~spl7_166),
% 2.36/0.67    inference(avatar_component_clause,[],[f1172])).
% 2.36/0.67  fof(f1174,plain,(
% 2.36/0.67    ~spl7_67 | spl7_166 | ~spl7_26 | ~spl7_115),
% 2.36/0.67    inference(avatar_split_clause,[],[f859,f852,f194,f1172,f465])).
% 2.36/0.67  fof(f465,plain,(
% 2.36/0.67    spl7_67 <=> l1_pre_topc(sK3)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).
% 2.36/0.67  fof(f194,plain,(
% 2.36/0.67    spl7_26 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.36/0.67  fof(f859,plain,(
% 2.36/0.67    ( ! [X0] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3)) ) | (~spl7_26 | ~spl7_115)),
% 2.36/0.67    inference(superposition,[],[f195,f853])).
% 2.36/0.67  fof(f195,plain,(
% 2.36/0.67    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl7_26),
% 2.36/0.67    inference(avatar_component_clause,[],[f194])).
% 2.36/0.67  fof(f1162,plain,(
% 2.36/0.67    ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_24 | spl7_162),
% 2.36/0.67    inference(avatar_contradiction_clause,[],[f1160])).
% 2.36/0.67  fof(f1160,plain,(
% 2.36/0.67    $false | (~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_24 | spl7_162)),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f122,f126,f138,f1147,f187])).
% 2.36/0.67  fof(f187,plain,(
% 2.36/0.67    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) ) | ~spl7_24),
% 2.36/0.67    inference(avatar_component_clause,[],[f186])).
% 2.36/0.67  fof(f186,plain,(
% 2.36/0.67    spl7_24 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.36/0.67  fof(f1147,plain,(
% 2.36/0.67    ~v2_pre_topc(sK2) | spl7_162),
% 2.36/0.67    inference(avatar_component_clause,[],[f1146])).
% 2.36/0.67  fof(f138,plain,(
% 2.36/0.67    m1_pre_topc(sK2,sK0) | ~spl7_12),
% 2.36/0.67    inference(avatar_component_clause,[],[f137])).
% 2.36/0.67  fof(f137,plain,(
% 2.36/0.67    spl7_12 <=> m1_pre_topc(sK2,sK0)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.36/0.67  fof(f854,plain,(
% 2.36/0.67    spl7_115 | ~spl7_11 | ~spl7_109),
% 2.36/0.67    inference(avatar_split_clause,[],[f806,f797,f133,f852])).
% 2.36/0.67  fof(f797,plain,(
% 2.36/0.67    spl7_109 <=> ! [X1] : (~m1_pre_topc(X1,sK0) | u1_struct_0(X1) = k2_struct_0(X1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).
% 2.36/0.67  fof(f806,plain,(
% 2.36/0.67    u1_struct_0(sK3) = k2_struct_0(sK3) | (~spl7_11 | ~spl7_109)),
% 2.36/0.67    inference(resolution,[],[f798,f134])).
% 2.36/0.67  fof(f798,plain,(
% 2.36/0.67    ( ! [X1] : (~m1_pre_topc(X1,sK0) | u1_struct_0(X1) = k2_struct_0(X1)) ) | ~spl7_109),
% 2.36/0.67    inference(avatar_component_clause,[],[f797])).
% 2.36/0.67  fof(f831,plain,(
% 2.36/0.67    spl7_112 | ~spl7_12 | ~spl7_109),
% 2.36/0.67    inference(avatar_split_clause,[],[f805,f797,f137,f829])).
% 2.36/0.67  fof(f805,plain,(
% 2.36/0.67    u1_struct_0(sK2) = k2_struct_0(sK2) | (~spl7_12 | ~spl7_109)),
% 2.36/0.67    inference(resolution,[],[f798,f138])).
% 2.36/0.67  fof(f823,plain,(
% 2.36/0.67    spl7_110 | ~spl7_12 | ~spl7_14 | ~spl7_109),
% 2.36/0.67    inference(avatar_split_clause,[],[f815,f797,f145,f137,f821])).
% 2.36/0.67  fof(f145,plain,(
% 2.36/0.67    spl7_14 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.36/0.67  fof(f815,plain,(
% 2.36/0.67    m1_subset_1(sK5,k2_struct_0(sK2)) | (~spl7_12 | ~spl7_14 | ~spl7_109)),
% 2.36/0.67    inference(backward_demodulation,[],[f146,f805])).
% 2.36/0.67  fof(f146,plain,(
% 2.36/0.67    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl7_14),
% 2.36/0.67    inference(avatar_component_clause,[],[f145])).
% 2.36/0.67  fof(f799,plain,(
% 2.36/0.67    spl7_109 | ~spl7_9 | ~spl7_103),
% 2.36/0.67    inference(avatar_split_clause,[],[f764,f756,f125,f797])).
% 2.36/0.67  fof(f756,plain,(
% 2.36/0.67    spl7_103 <=> ! [X1,X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).
% 2.36/0.67  fof(f764,plain,(
% 2.36/0.67    ( ! [X1] : (~m1_pre_topc(X1,sK0) | u1_struct_0(X1) = k2_struct_0(X1)) ) | (~spl7_9 | ~spl7_103)),
% 2.36/0.67    inference(resolution,[],[f757,f126])).
% 2.36/0.67  fof(f757,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl7_103),
% 2.36/0.67    inference(avatar_component_clause,[],[f756])).
% 2.36/0.67  fof(f780,plain,(
% 2.36/0.67    spl7_107 | ~spl7_22 | ~spl7_24 | ~spl7_34 | ~spl7_70),
% 2.36/0.67    inference(avatar_split_clause,[],[f492,f484,f245,f186,f177,f778])).
% 2.36/0.67  fof(f177,plain,(
% 2.36/0.67    spl7_22 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 2.36/0.67  fof(f245,plain,(
% 2.36/0.67    spl7_34 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 2.36/0.67  fof(f484,plain,(
% 2.36/0.67    spl7_70 <=> ! [X1,X3,X0,X2,X4] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 2.36/0.67  fof(f492,plain,(
% 2.36/0.67    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4) | ~v3_pre_topc(u1_struct_0(X2),X3)) ) | (~spl7_22 | ~spl7_24 | ~spl7_34 | ~spl7_70)),
% 2.36/0.67    inference(subsumption_resolution,[],[f491,f187])).
% 2.36/0.67  fof(f491,plain,(
% 2.36/0.67    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4) | ~v3_pre_topc(u1_struct_0(X2),X3) | ~v2_pre_topc(X3)) ) | (~spl7_22 | ~spl7_34 | ~spl7_70)),
% 2.36/0.67    inference(subsumption_resolution,[],[f490,f178])).
% 2.36/0.67  fof(f178,plain,(
% 2.36/0.67    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl7_22),
% 2.36/0.67    inference(avatar_component_clause,[],[f177])).
% 2.36/0.67  fof(f490,plain,(
% 2.36/0.67    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4) | ~l1_pre_topc(X3) | ~v3_pre_topc(u1_struct_0(X2),X3) | ~v2_pre_topc(X3)) ) | (~spl7_34 | ~spl7_70)),
% 2.36/0.67    inference(duplicate_literal_removal,[],[f489])).
% 2.36/0.67  fof(f489,plain,(
% 2.36/0.67    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4) | ~l1_pre_topc(X3) | ~m1_pre_topc(X2,X3) | ~v3_pre_topc(u1_struct_0(X2),X3) | ~v2_pre_topc(X3)) ) | (~spl7_34 | ~spl7_70)),
% 2.36/0.67    inference(resolution,[],[f485,f246])).
% 2.36/0.67  fof(f246,plain,(
% 2.36/0.67    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0)) ) | ~spl7_34),
% 2.36/0.67    inference(avatar_component_clause,[],[f245])).
% 2.36/0.67  fof(f485,plain,(
% 2.36/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_tsep_1(X2,X3) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) ) | ~spl7_70),
% 2.36/0.67    inference(avatar_component_clause,[],[f484])).
% 2.36/0.67  fof(f758,plain,(
% 2.36/0.67    spl7_103 | ~spl7_22 | ~spl7_25),
% 2.36/0.67    inference(avatar_split_clause,[],[f203,f190,f177,f756])).
% 2.36/0.67  fof(f190,plain,(
% 2.36/0.67    spl7_25 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.36/0.67  fof(f203,plain,(
% 2.36/0.67    ( ! [X0,X1] : (k2_struct_0(X0) = u1_struct_0(X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) ) | (~spl7_22 | ~spl7_25)),
% 2.36/0.67    inference(resolution,[],[f191,f178])).
% 2.36/0.67  fof(f191,plain,(
% 2.36/0.67    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl7_25),
% 2.36/0.67    inference(avatar_component_clause,[],[f190])).
% 2.36/0.67  fof(f526,plain,(
% 2.36/0.67    ~spl7_9 | ~spl7_12 | ~spl7_22 | spl7_74),
% 2.36/0.67    inference(avatar_contradiction_clause,[],[f524])).
% 2.36/0.67  fof(f524,plain,(
% 2.36/0.67    $false | (~spl7_9 | ~spl7_12 | ~spl7_22 | spl7_74)),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f126,f138,f515,f178])).
% 2.36/0.67  fof(f515,plain,(
% 2.36/0.67    ~l1_pre_topc(sK2) | spl7_74),
% 2.36/0.67    inference(avatar_component_clause,[],[f514])).
% 2.36/0.67  fof(f519,plain,(
% 2.36/0.67    ~spl7_74 | spl7_75 | ~spl7_17 | ~spl7_31 | ~spl7_72),
% 2.36/0.67    inference(avatar_split_clause,[],[f505,f498,f219,f157,f517,f514])).
% 2.36/0.67  fof(f157,plain,(
% 2.36/0.67    spl7_17 <=> sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.36/0.67  fof(f219,plain,(
% 2.36/0.67    spl7_31 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 2.36/0.67  fof(f498,plain,(
% 2.36/0.67    spl7_72 <=> m1_pre_topc(sK2,sK2)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 2.36/0.67  fof(f505,plain,(
% 2.36/0.67    m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2) | (~spl7_17 | ~spl7_31 | ~spl7_72)),
% 2.36/0.67    inference(forward_demodulation,[],[f504,f158])).
% 2.36/0.67  fof(f158,plain,(
% 2.36/0.67    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~spl7_17),
% 2.36/0.67    inference(avatar_component_clause,[],[f157])).
% 2.36/0.67  fof(f504,plain,(
% 2.36/0.67    ~l1_pre_topc(sK2) | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) | (~spl7_31 | ~spl7_72)),
% 2.36/0.67    inference(resolution,[],[f499,f220])).
% 2.36/0.67  fof(f220,plain,(
% 2.36/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)) ) | ~spl7_31),
% 2.36/0.67    inference(avatar_component_clause,[],[f219])).
% 2.36/0.67  fof(f499,plain,(
% 2.36/0.67    m1_pre_topc(sK2,sK2) | ~spl7_72),
% 2.36/0.67    inference(avatar_component_clause,[],[f498])).
% 2.36/0.67  fof(f500,plain,(
% 2.36/0.67    spl7_72 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_62 | ~spl7_66),
% 2.36/0.67    inference(avatar_split_clause,[],[f463,f451,f420,f137,f125,f121,f117,f101,f498])).
% 2.36/0.67  fof(f420,plain,(
% 2.36/0.67    spl7_62 <=> sK3 = k1_tsep_1(sK0,sK2,sK2)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 2.36/0.67  fof(f451,plain,(
% 2.36/0.67    spl7_66 <=> ! [X1,X0] : (sK3 != k1_tsep_1(X0,X1,sK2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,sK2))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 2.36/0.67  fof(f463,plain,(
% 2.36/0.67    m1_pre_topc(sK2,sK2) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_62 | ~spl7_66)),
% 2.36/0.67    inference(subsumption_resolution,[],[f462,f118])).
% 2.36/0.67  fof(f462,plain,(
% 2.36/0.67    v2_struct_0(sK0) | m1_pre_topc(sK2,sK2) | (spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_62 | ~spl7_66)),
% 2.36/0.67    inference(subsumption_resolution,[],[f461,f138])).
% 2.36/0.67  fof(f461,plain,(
% 2.36/0.67    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2) | (spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_62 | ~spl7_66)),
% 2.36/0.67    inference(subsumption_resolution,[],[f460,f102])).
% 2.36/0.67  fof(f460,plain,(
% 2.36/0.67    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2) | (~spl7_8 | ~spl7_9 | ~spl7_62 | ~spl7_66)),
% 2.36/0.67    inference(subsumption_resolution,[],[f459,f126])).
% 2.36/0.67  fof(f459,plain,(
% 2.36/0.67    ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2) | (~spl7_8 | ~spl7_62 | ~spl7_66)),
% 2.36/0.67    inference(subsumption_resolution,[],[f458,f122])).
% 2.36/0.67  fof(f458,plain,(
% 2.36/0.67    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2) | (~spl7_62 | ~spl7_66)),
% 2.36/0.67    inference(trivial_inequality_removal,[],[f457])).
% 2.36/0.67  fof(f457,plain,(
% 2.36/0.67    sK3 != sK3 | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2) | (~spl7_62 | ~spl7_66)),
% 2.36/0.67    inference(duplicate_literal_removal,[],[f456])).
% 2.36/0.67  fof(f456,plain,(
% 2.36/0.67    sK3 != sK3 | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK2) | (~spl7_62 | ~spl7_66)),
% 2.36/0.67    inference(superposition,[],[f452,f421])).
% 2.36/0.67  fof(f421,plain,(
% 2.36/0.67    sK3 = k1_tsep_1(sK0,sK2,sK2) | ~spl7_62),
% 2.36/0.67    inference(avatar_component_clause,[],[f420])).
% 2.36/0.67  fof(f452,plain,(
% 2.36/0.67    ( ! [X0,X1] : (sK3 != k1_tsep_1(X0,X1,sK2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,sK2)) ) | ~spl7_66),
% 2.36/0.67    inference(avatar_component_clause,[],[f451])).
% 2.36/0.67  fof(f486,plain,(
% 2.36/0.67    spl7_70 | ~spl7_1 | ~spl7_57),
% 2.36/0.67    inference(avatar_split_clause,[],[f385,f382,f93,f484])).
% 2.36/0.67  fof(f93,plain,(
% 2.36/0.67    spl7_1 <=> v1_funct_1(sK4)),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.36/0.67  fof(f382,plain,(
% 2.36/0.67    spl7_57 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 2.36/0.67  fof(f385,plain,(
% 2.36/0.67    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4)) ) | (~spl7_1 | ~spl7_57)),
% 2.36/0.67    inference(resolution,[],[f383,f94])).
% 2.36/0.67  fof(f94,plain,(
% 2.36/0.67    v1_funct_1(sK4) | ~spl7_1),
% 2.36/0.67    inference(avatar_component_clause,[],[f93])).
% 2.36/0.67  fof(f383,plain,(
% 2.36/0.67    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) ) | ~spl7_57),
% 2.36/0.67    inference(avatar_component_clause,[],[f382])).
% 2.36/0.67  fof(f482,plain,(
% 2.36/0.67    ~spl7_9 | ~spl7_11 | ~spl7_22 | spl7_67),
% 2.36/0.67    inference(avatar_contradiction_clause,[],[f480])).
% 2.36/0.67  fof(f480,plain,(
% 2.36/0.67    $false | (~spl7_9 | ~spl7_11 | ~spl7_22 | spl7_67)),
% 2.36/0.67    inference(unit_resulting_resolution,[],[f126,f134,f466,f178])).
% 2.36/0.67  fof(f466,plain,(
% 2.36/0.67    ~l1_pre_topc(sK3) | spl7_67),
% 2.36/0.67    inference(avatar_component_clause,[],[f465])).
% 2.36/0.67  fof(f453,plain,(
% 2.36/0.67    spl7_66 | spl7_3 | ~spl7_17 | ~spl7_47),
% 2.36/0.67    inference(avatar_split_clause,[],[f352,f318,f157,f101,f451])).
% 2.36/0.67  fof(f318,plain,(
% 2.36/0.67    spl7_47 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | m1_pre_topc(X1,X2))),
% 2.36/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 2.36/0.67  fof(f352,plain,(
% 2.36/0.67    ( ! [X0,X1] : (sK3 != k1_tsep_1(X0,X1,sK2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,sK2)) ) | (spl7_3 | ~spl7_17 | ~spl7_47)),
% 2.36/0.67    inference(subsumption_resolution,[],[f349,f102])).
% 2.36/0.67  fof(f349,plain,(
% 2.36/0.67    ( ! [X0,X1] : (sK3 != k1_tsep_1(X0,X1,sK2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,sK2)) ) | (~spl7_17 | ~spl7_47)),
% 2.36/0.67    inference(superposition,[],[f319,f158])).
% 2.36/0.69  fof(f319,plain,(
% 2.36/0.69    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,X2)) ) | ~spl7_47),
% 2.36/0.69    inference(avatar_component_clause,[],[f318])).
% 2.36/0.69  fof(f444,plain,(
% 2.36/0.69    spl7_65 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_44 | ~spl7_62),
% 2.36/0.69    inference(avatar_split_clause,[],[f436,f420,f297,f137,f125,f121,f117,f101,f442])).
% 2.36/0.69  fof(f297,plain,(
% 2.36/0.69    spl7_44 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))),
% 2.36/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 2.36/0.69  fof(f436,plain,(
% 2.36/0.69    m1_pre_topc(sK2,sK3) | (spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_44 | ~spl7_62)),
% 2.36/0.69    inference(subsumption_resolution,[],[f435,f118])).
% 2.36/0.69  fof(f435,plain,(
% 2.36/0.69    m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | (spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_44 | ~spl7_62)),
% 2.36/0.69    inference(subsumption_resolution,[],[f434,f138])).
% 2.36/0.69  fof(f434,plain,(
% 2.36/0.69    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_44 | ~spl7_62)),
% 2.36/0.69    inference(subsumption_resolution,[],[f433,f102])).
% 2.36/0.69  fof(f433,plain,(
% 2.36/0.69    m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl7_8 | ~spl7_9 | ~spl7_44 | ~spl7_62)),
% 2.36/0.69    inference(subsumption_resolution,[],[f432,f126])).
% 2.36/0.69  fof(f432,plain,(
% 2.36/0.69    m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl7_8 | ~spl7_44 | ~spl7_62)),
% 2.36/0.69    inference(subsumption_resolution,[],[f431,f122])).
% 2.36/0.69  fof(f431,plain,(
% 2.36/0.69    m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl7_44 | ~spl7_62)),
% 2.36/0.69    inference(duplicate_literal_removal,[],[f430])).
% 2.36/0.69  fof(f430,plain,(
% 2.36/0.69    m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl7_44 | ~spl7_62)),
% 2.36/0.69    inference(superposition,[],[f298,f421])).
% 2.36/0.69  fof(f298,plain,(
% 2.36/0.69    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl7_44),
% 2.36/0.69    inference(avatar_component_clause,[],[f297])).
% 2.36/0.69  fof(f422,plain,(
% 2.36/0.69    spl7_62 | spl7_3 | ~spl7_12 | ~spl7_17 | ~spl7_60),
% 2.36/0.69    inference(avatar_split_clause,[],[f410,f401,f157,f137,f101,f420])).
% 2.36/0.69  fof(f401,plain,(
% 2.36/0.69    spl7_60 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X1,X1))),
% 2.36/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 2.36/0.69  fof(f410,plain,(
% 2.36/0.69    sK3 = k1_tsep_1(sK0,sK2,sK2) | (spl7_3 | ~spl7_12 | ~spl7_17 | ~spl7_60)),
% 2.36/0.69    inference(forward_demodulation,[],[f409,f158])).
% 2.36/0.69  fof(f409,plain,(
% 2.36/0.69    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) | (spl7_3 | ~spl7_12 | ~spl7_60)),
% 2.36/0.69    inference(subsumption_resolution,[],[f406,f138])).
% 2.36/0.69  fof(f406,plain,(
% 2.36/0.69    ~m1_pre_topc(sK2,sK0) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) | (spl7_3 | ~spl7_60)),
% 2.36/0.69    inference(resolution,[],[f402,f102])).
% 2.36/0.69  fof(f402,plain,(
% 2.36/0.69    ( ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X1,X1)) ) | ~spl7_60),
% 2.36/0.70    inference(avatar_component_clause,[],[f401])).
% 2.36/0.70  fof(f403,plain,(
% 2.36/0.70    spl7_60 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_42),
% 2.36/0.70    inference(avatar_split_clause,[],[f308,f289,f125,f121,f117,f401])).
% 2.36/0.70  fof(f289,plain,(
% 2.36/0.70    spl7_42 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1))),
% 2.36/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 2.36/0.70  fof(f308,plain,(
% 2.36/0.70    ( ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X1,X1)) ) | (spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_42)),
% 2.36/0.70    inference(subsumption_resolution,[],[f307,f118])).
% 2.36/0.70  fof(f307,plain,(
% 2.36/0.70    ( ! [X1] : (v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X1,X1)) ) | (~spl7_8 | ~spl7_9 | ~spl7_42)),
% 2.36/0.70    inference(subsumption_resolution,[],[f303,f122])).
% 2.36/0.70  fof(f303,plain,(
% 2.36/0.70    ( ! [X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X1,X1)) ) | (~spl7_9 | ~spl7_42)),
% 2.36/0.70    inference(resolution,[],[f290,f126])).
% 2.36/0.70  fof(f290,plain,(
% 2.36/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)) ) | ~spl7_42),
% 2.36/0.70    inference(avatar_component_clause,[],[f289])).
% 2.36/0.70  fof(f384,plain,(
% 2.36/0.70    spl7_57 | ~spl7_33 | ~spl7_55),
% 2.36/0.70    inference(avatar_split_clause,[],[f376,f373,f232,f382])).
% 2.36/0.70  fof(f232,plain,(
% 2.36/0.70    spl7_33 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0))),
% 2.36/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 2.36/0.70  fof(f373,plain,(
% 2.36/0.70    spl7_55 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6))),
% 2.36/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 2.36/0.70  fof(f376,plain,(
% 2.36/0.70    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) ) | (~spl7_33 | ~spl7_55)),
% 2.36/0.70    inference(subsumption_resolution,[],[f374,f233])).
% 2.36/0.70  fof(f233,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | ~v2_pre_topc(X0)) ) | ~spl7_33),
% 2.36/0.70    inference(avatar_component_clause,[],[f232])).
% 2.36/0.70  fof(f374,plain,(
% 2.36/0.70    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) ) | ~spl7_55),
% 2.36/0.70    inference(avatar_component_clause,[],[f373])).
% 2.36/0.70  fof(f375,plain,(
% 2.36/0.70    spl7_55),
% 2.36/0.70    inference(avatar_split_clause,[],[f84,f373])).
% 2.36/0.70  fof(f84,plain,(
% 2.36/0.70    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6)) )),
% 2.36/0.70    inference(equality_resolution,[],[f71])).
% 2.36/0.70  fof(f71,plain,(
% 2.36/0.70    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f29])).
% 2.36/0.70  fof(f29,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/0.70    inference(flattening,[],[f28])).
% 2.36/0.70  fof(f28,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/0.70    inference(ennf_transformation,[],[f15])).
% 2.36/0.70  fof(f15,axiom,(
% 2.36/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 2.36/0.70  fof(f320,plain,(
% 2.36/0.70    spl7_47),
% 2.36/0.70    inference(avatar_split_clause,[],[f75,f318])).
% 2.36/0.70  fof(f75,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | m1_pre_topc(X1,X2)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f35])).
% 2.36/0.70  fof(f35,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/0.70    inference(flattening,[],[f34])).
% 2.36/0.70  fof(f34,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/0.70    inference(ennf_transformation,[],[f12])).
% 2.36/0.70  fof(f12,axiom,(
% 2.36/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).
% 2.36/0.70  fof(f299,plain,(
% 2.36/0.70    spl7_44),
% 2.36/0.70    inference(avatar_split_clause,[],[f74,f297])).
% 2.36/0.70  fof(f74,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))) )),
% 2.36/0.70    inference(cnf_transformation,[],[f33])).
% 2.36/0.70  fof(f33,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/0.70    inference(flattening,[],[f32])).
% 2.36/0.70  fof(f32,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/0.70    inference(ennf_transformation,[],[f11])).
% 2.36/0.70  fof(f11,axiom,(
% 2.36/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).
% 2.36/0.70  fof(f291,plain,(
% 2.36/0.70    spl7_42),
% 2.36/0.70    inference(avatar_split_clause,[],[f73,f289])).
% 2.36/0.70  fof(f73,plain,(
% 2.36/0.70    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f31])).
% 2.36/0.70  fof(f31,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/0.70    inference(flattening,[],[f30])).
% 2.36/0.70  fof(f30,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/0.70    inference(ennf_transformation,[],[f13])).
% 2.36/0.70  fof(f13,axiom,(
% 2.36/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 2.36/0.70  fof(f276,plain,(
% 2.36/0.70    spl7_40),
% 2.36/0.70    inference(avatar_split_clause,[],[f89,f274])).
% 2.36/0.70  fof(f89,plain,(
% 2.36/0.70    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 2.36/0.70    inference(subsumption_resolution,[],[f82,f69])).
% 2.36/0.70  fof(f69,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.36/0.70    inference(cnf_transformation,[],[f25])).
% 2.36/0.70  fof(f25,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.36/0.70    inference(ennf_transformation,[],[f5])).
% 2.36/0.70  fof(f5,axiom,(
% 2.36/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 2.36/0.70  fof(f82,plain,(
% 2.36/0.70    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 2.36/0.70    inference(equality_resolution,[],[f70])).
% 2.36/0.70  fof(f70,plain,(
% 2.36/0.70    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v3_pre_topc(X3,X2)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f27])).
% 2.36/0.70  fof(f27,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.70    inference(flattening,[],[f26])).
% 2.36/0.70  fof(f26,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.70    inference(ennf_transformation,[],[f7])).
% 2.36/0.70  fof(f7,axiom,(
% 2.36/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 2.36/0.70  fof(f247,plain,(
% 2.36/0.70    spl7_34),
% 2.36/0.70    inference(avatar_split_clause,[],[f90,f245])).
% 2.36/0.70  fof(f90,plain,(
% 2.36/0.70    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 2.36/0.70    inference(subsumption_resolution,[],[f85,f66])).
% 2.36/0.70  fof(f66,plain,(
% 2.36/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.36/0.70    inference(cnf_transformation,[],[f23])).
% 2.36/0.70  fof(f23,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.36/0.70    inference(ennf_transformation,[],[f10])).
% 2.36/0.70  fof(f10,axiom,(
% 2.36/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.36/0.70  fof(f85,plain,(
% 2.36/0.70    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 2.36/0.70    inference(equality_resolution,[],[f81])).
% 2.36/0.70  fof(f81,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f43])).
% 2.36/0.70  fof(f43,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/0.70    inference(flattening,[],[f42])).
% 2.36/0.70  fof(f42,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.36/0.70    inference(ennf_transformation,[],[f9])).
% 2.36/0.70  fof(f9,axiom,(
% 2.36/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 2.36/0.70  fof(f234,plain,(
% 2.36/0.70    spl7_33),
% 2.36/0.70    inference(avatar_split_clause,[],[f79,f232])).
% 2.36/0.70  fof(f79,plain,(
% 2.36/0.70    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f41])).
% 2.36/0.70  fof(f41,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/0.70    inference(flattening,[],[f40])).
% 2.36/0.70  fof(f40,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.36/0.70    inference(ennf_transformation,[],[f14])).
% 2.36/0.70  fof(f14,axiom,(
% 2.36/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.36/0.70  fof(f221,plain,(
% 2.36/0.70    spl7_31),
% 2.36/0.70    inference(avatar_split_clause,[],[f68,f219])).
% 2.36/0.70  fof(f68,plain,(
% 2.36/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f24])).
% 2.36/0.70  fof(f24,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.36/0.70    inference(ennf_transformation,[],[f8])).
% 2.36/0.70  fof(f8,axiom,(
% 2.36/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 2.36/0.70  fof(f217,plain,(
% 2.36/0.70    spl7_30 | ~spl7_6 | ~spl7_25),
% 2.36/0.70    inference(avatar_split_clause,[],[f201,f190,f113,f215])).
% 2.36/0.70  fof(f201,plain,(
% 2.36/0.70    u1_struct_0(sK1) = k2_struct_0(sK1) | (~spl7_6 | ~spl7_25)),
% 2.36/0.70    inference(resolution,[],[f191,f114])).
% 2.36/0.70  fof(f213,plain,(
% 2.36/0.70    spl7_29 | ~spl7_6 | ~spl7_18 | ~spl7_25),
% 2.36/0.70    inference(avatar_split_clause,[],[f204,f190,f161,f113,f211])).
% 2.36/0.70  fof(f161,plain,(
% 2.36/0.70    spl7_18 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.36/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.36/0.70  fof(f204,plain,(
% 2.36/0.70    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | (~spl7_6 | ~spl7_18 | ~spl7_25)),
% 2.36/0.70    inference(backward_demodulation,[],[f162,f201])).
% 2.36/0.70  fof(f162,plain,(
% 2.36/0.70    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl7_18),
% 2.36/0.70    inference(avatar_component_clause,[],[f161])).
% 2.36/0.70  fof(f209,plain,(
% 2.36/0.70    spl7_28 | ~spl7_6 | ~spl7_16 | ~spl7_25),
% 2.36/0.70    inference(avatar_split_clause,[],[f205,f190,f153,f113,f207])).
% 2.36/0.70  fof(f153,plain,(
% 2.36/0.70    spl7_16 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.36/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.36/0.70  fof(f205,plain,(
% 2.36/0.70    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | (~spl7_6 | ~spl7_16 | ~spl7_25)),
% 2.36/0.70    inference(backward_demodulation,[],[f154,f201])).
% 2.36/0.70  fof(f154,plain,(
% 2.36/0.70    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl7_16),
% 2.36/0.70    inference(avatar_component_clause,[],[f153])).
% 2.36/0.70  fof(f196,plain,(
% 2.36/0.70    spl7_26),
% 2.36/0.70    inference(avatar_split_clause,[],[f66,f194])).
% 2.36/0.70  fof(f192,plain,(
% 2.36/0.70    spl7_25 | ~spl7_20 | ~spl7_21),
% 2.36/0.70    inference(avatar_split_clause,[],[f184,f173,f169,f190])).
% 2.36/0.70  fof(f169,plain,(
% 2.36/0.70    spl7_20 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 2.36/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 2.36/0.70  fof(f173,plain,(
% 2.36/0.70    spl7_21 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 2.36/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 2.36/0.70  fof(f184,plain,(
% 2.36/0.70    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0)) ) | (~spl7_20 | ~spl7_21)),
% 2.36/0.70    inference(resolution,[],[f174,f170])).
% 2.36/0.70  fof(f170,plain,(
% 2.36/0.70    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl7_20),
% 2.36/0.70    inference(avatar_component_clause,[],[f169])).
% 2.36/0.70  fof(f174,plain,(
% 2.36/0.70    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl7_21),
% 2.36/0.70    inference(avatar_component_clause,[],[f173])).
% 2.36/0.70  fof(f188,plain,(
% 2.36/0.70    spl7_24),
% 2.36/0.70    inference(avatar_split_clause,[],[f78,f186])).
% 2.36/0.70  fof(f78,plain,(
% 2.36/0.70    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f39])).
% 2.36/0.70  fof(f39,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/0.70    inference(flattening,[],[f38])).
% 2.36/0.70  fof(f38,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.36/0.70    inference(ennf_transformation,[],[f1])).
% 2.36/0.70  fof(f1,axiom,(
% 2.36/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.36/0.70  fof(f183,plain,(
% 2.36/0.70    spl7_23),
% 2.36/0.70    inference(avatar_split_clause,[],[f77,f181])).
% 2.36/0.70  fof(f77,plain,(
% 2.36/0.70    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f37])).
% 2.36/0.70  fof(f37,plain,(
% 2.36/0.70    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/0.70    inference(flattening,[],[f36])).
% 2.36/0.70  fof(f36,plain,(
% 2.36/0.70    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.36/0.70    inference(ennf_transformation,[],[f6])).
% 2.36/0.70  fof(f6,axiom,(
% 2.36/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 2.36/0.70  fof(f179,plain,(
% 2.36/0.70    spl7_22),
% 2.36/0.70    inference(avatar_split_clause,[],[f65,f177])).
% 2.36/0.70  fof(f65,plain,(
% 2.36/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f22])).
% 2.36/0.70  fof(f22,plain,(
% 2.36/0.70    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.36/0.70    inference(ennf_transformation,[],[f4])).
% 2.36/0.70  fof(f4,axiom,(
% 2.36/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.36/0.70  fof(f175,plain,(
% 2.36/0.70    spl7_21),
% 2.36/0.70    inference(avatar_split_clause,[],[f63,f173])).
% 2.36/0.70  fof(f63,plain,(
% 2.36/0.70    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f20])).
% 2.36/0.70  fof(f20,plain,(
% 2.36/0.70    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.36/0.70    inference(ennf_transformation,[],[f2])).
% 2.36/0.70  fof(f2,axiom,(
% 2.36/0.70    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.36/0.70  fof(f171,plain,(
% 2.36/0.70    spl7_20),
% 2.36/0.70    inference(avatar_split_clause,[],[f64,f169])).
% 2.36/0.70  fof(f64,plain,(
% 2.36/0.70    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.36/0.70    inference(cnf_transformation,[],[f21])).
% 2.36/0.70  fof(f21,plain,(
% 2.36/0.70    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.36/0.70    inference(ennf_transformation,[],[f3])).
% 2.36/0.70  fof(f3,axiom,(
% 2.36/0.70    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.36/0.70  fof(f167,plain,(
% 2.36/0.70    spl7_19),
% 2.36/0.70    inference(avatar_split_clause,[],[f87,f165])).
% 2.36/0.70  fof(f87,plain,(
% 2.36/0.70    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 2.36/0.70    inference(backward_demodulation,[],[f46,f45])).
% 2.36/0.70  fof(f45,plain,(
% 2.36/0.70    sK5 = sK6),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f19,plain,(
% 2.36/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.36/0.70    inference(flattening,[],[f18])).
% 2.36/0.70  fof(f18,plain,(
% 2.36/0.70    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.36/0.70    inference(ennf_transformation,[],[f17])).
% 2.36/0.70  fof(f17,negated_conjecture,(
% 2.36/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.36/0.70    inference(negated_conjecture,[],[f16])).
% 2.36/0.70  fof(f16,conjecture,(
% 2.36/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.36/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 2.36/0.70  fof(f46,plain,(
% 2.36/0.70    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f163,plain,(
% 2.36/0.70    spl7_18),
% 2.36/0.70    inference(avatar_split_clause,[],[f51,f161])).
% 2.36/0.70  fof(f51,plain,(
% 2.36/0.70    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f159,plain,(
% 2.36/0.70    spl7_17),
% 2.36/0.70    inference(avatar_split_clause,[],[f52,f157])).
% 2.36/0.70  fof(f52,plain,(
% 2.36/0.70    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f155,plain,(
% 2.36/0.70    spl7_16),
% 2.36/0.70    inference(avatar_split_clause,[],[f50,f153])).
% 2.36/0.70  fof(f50,plain,(
% 2.36/0.70    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f151,plain,(
% 2.36/0.70    ~spl7_15),
% 2.36/0.70    inference(avatar_split_clause,[],[f47,f149])).
% 2.36/0.70  fof(f47,plain,(
% 2.36/0.70    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f147,plain,(
% 2.36/0.70    spl7_14),
% 2.36/0.70    inference(avatar_split_clause,[],[f88,f145])).
% 2.36/0.70  fof(f88,plain,(
% 2.36/0.70    m1_subset_1(sK5,u1_struct_0(sK2))),
% 2.36/0.70    inference(forward_demodulation,[],[f44,f45])).
% 2.36/0.70  fof(f44,plain,(
% 2.36/0.70    m1_subset_1(sK6,u1_struct_0(sK2))),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f143,plain,(
% 2.36/0.70    spl7_13),
% 2.36/0.70    inference(avatar_split_clause,[],[f48,f141])).
% 2.36/0.70  fof(f48,plain,(
% 2.36/0.70    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f139,plain,(
% 2.36/0.70    spl7_12),
% 2.36/0.70    inference(avatar_split_clause,[],[f56,f137])).
% 2.36/0.70  fof(f56,plain,(
% 2.36/0.70    m1_pre_topc(sK2,sK0)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f135,plain,(
% 2.36/0.70    spl7_11),
% 2.36/0.70    inference(avatar_split_clause,[],[f54,f133])).
% 2.36/0.70  fof(f54,plain,(
% 2.36/0.70    m1_pre_topc(sK3,sK0)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f127,plain,(
% 2.36/0.70    spl7_9),
% 2.36/0.70    inference(avatar_split_clause,[],[f62,f125])).
% 2.36/0.70  fof(f62,plain,(
% 2.36/0.70    l1_pre_topc(sK0)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f123,plain,(
% 2.36/0.70    spl7_8),
% 2.36/0.70    inference(avatar_split_clause,[],[f61,f121])).
% 2.36/0.70  fof(f61,plain,(
% 2.36/0.70    v2_pre_topc(sK0)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f119,plain,(
% 2.36/0.70    ~spl7_7),
% 2.36/0.70    inference(avatar_split_clause,[],[f60,f117])).
% 2.36/0.70  fof(f60,plain,(
% 2.36/0.70    ~v2_struct_0(sK0)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f115,plain,(
% 2.36/0.70    spl7_6),
% 2.36/0.70    inference(avatar_split_clause,[],[f59,f113])).
% 2.36/0.70  fof(f59,plain,(
% 2.36/0.70    l1_pre_topc(sK1)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f111,plain,(
% 2.36/0.70    spl7_5),
% 2.36/0.70    inference(avatar_split_clause,[],[f58,f109])).
% 2.36/0.70  fof(f58,plain,(
% 2.36/0.70    v2_pre_topc(sK1)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f107,plain,(
% 2.36/0.70    ~spl7_4),
% 2.36/0.70    inference(avatar_split_clause,[],[f57,f105])).
% 2.36/0.70  fof(f57,plain,(
% 2.36/0.70    ~v2_struct_0(sK1)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f103,plain,(
% 2.36/0.70    ~spl7_3),
% 2.36/0.70    inference(avatar_split_clause,[],[f55,f101])).
% 2.36/0.70  fof(f55,plain,(
% 2.36/0.70    ~v2_struct_0(sK2)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f99,plain,(
% 2.36/0.70    ~spl7_2),
% 2.36/0.70    inference(avatar_split_clause,[],[f53,f97])).
% 2.36/0.70  fof(f53,plain,(
% 2.36/0.70    ~v2_struct_0(sK3)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  fof(f95,plain,(
% 2.36/0.70    spl7_1),
% 2.36/0.70    inference(avatar_split_clause,[],[f49,f93])).
% 2.36/0.70  fof(f49,plain,(
% 2.36/0.70    v1_funct_1(sK4)),
% 2.36/0.70    inference(cnf_transformation,[],[f19])).
% 2.36/0.70  % SZS output end Proof for theBenchmark
% 2.36/0.70  % (1224)------------------------------
% 2.36/0.70  % (1224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.70  % (1224)Termination reason: Refutation
% 2.36/0.70  
% 2.36/0.70  % (1224)Memory used [KB]: 11769
% 2.36/0.70  % (1224)Time elapsed: 0.265 s
% 2.36/0.70  % (1224)------------------------------
% 2.36/0.70  % (1224)------------------------------
% 2.36/0.70  % (1214)Success in time 0.328 s
%------------------------------------------------------------------------------
