%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 258 expanded)
%              Number of leaves         :   43 ( 133 expanded)
%              Depth                    :    6
%              Number of atoms          :  401 ( 740 expanded)
%              Number of equality atoms :   32 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f576,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f57,f61,f65,f69,f73,f77,f81,f85,f89,f94,f100,f107,f112,f128,f136,f141,f213,f305,f330,f408,f422,f447,f454,f472,f485,f516,f541,f555])).

fof(f555,plain,
    ( spl3_15
    | ~ spl3_16
    | ~ spl3_85 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | spl3_15
    | ~ spl3_16
    | ~ spl3_85 ),
    inference(subsumption_resolution,[],[f548,f106])).

fof(f106,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_16
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f548,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl3_15
    | ~ spl3_85 ),
    inference(resolution,[],[f540,f99])).

fof(f99,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_15
  <=> r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f540,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl3_85 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl3_85
  <=> ! [X0] :
        ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f541,plain,
    ( spl3_85
    | ~ spl3_52
    | ~ spl3_82 ),
    inference(avatar_split_clause,[],[f520,f513,f327,f539])).

fof(f327,plain,
    ( spl3_52
  <=> ! [X1,X0] :
        ( r1_tarski(X1,k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),X0))
        | ~ r1_tarski(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f513,plain,
    ( spl3_82
  <=> k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f520,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl3_52
    | ~ spl3_82 ),
    inference(superposition,[],[f328,f515])).

fof(f515,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_82 ),
    inference(avatar_component_clause,[],[f513])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),X0))
        | ~ r1_tarski(X1,sK2) )
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f327])).

fof(f516,plain,
    ( spl3_82
    | ~ spl3_20
    | ~ spl3_76 ),
    inference(avatar_split_clause,[],[f497,f482,f126,f513])).

fof(f126,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k1_zfmisc_1(X1) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f482,plain,
    ( spl3_76
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f497,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_20
    | ~ spl3_76 ),
    inference(resolution,[],[f484,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_zfmisc_1(X1) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f126])).

fof(f484,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f482])).

fof(f485,plain,
    ( spl3_76
    | ~ spl3_16
    | ~ spl3_75 ),
    inference(avatar_split_clause,[],[f479,f470,f105,f482])).

fof(f470,plain,
    ( spl3_75
  <=> ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f479,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl3_16
    | ~ spl3_75 ),
    inference(resolution,[],[f471,f106])).

fof(f471,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK1))
        | r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f470])).

fof(f472,plain,
    ( spl3_75
    | ~ spl3_22
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f459,f451,f138,f470])).

fof(f138,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X2,k2_xboole_0(X1,X0))
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f451,plain,
    ( spl3_73
  <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f459,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,u1_struct_0(sK1)) )
    | ~ spl3_22
    | ~ spl3_73 ),
    inference(superposition,[],[f139,f453])).

fof(f453,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f451])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X2,k2_xboole_0(X1,X0))
        | ~ r1_tarski(X2,X1) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f138])).

fof(f454,plain,
    ( spl3_73
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f449,f445,f50,f45,f451])).

fof(f45,plain,
    ( spl3_3
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f445,plain,
    ( spl3_72
  <=> ! [X11,X10] :
        ( ~ l1_pre_topc(X10)
        | ~ m1_pre_topc(X11,X10)
        | u1_struct_0(X10) = k2_xboole_0(u1_struct_0(X11),u1_struct_0(X10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f449,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_72 ),
    inference(subsumption_resolution,[],[f448,f52])).

fof(f52,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f448,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_72 ),
    inference(resolution,[],[f446,f47])).

fof(f47,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f446,plain,
    ( ! [X10,X11] :
        ( ~ m1_pre_topc(X11,X10)
        | ~ l1_pre_topc(X10)
        | u1_struct_0(X10) = k2_xboole_0(u1_struct_0(X11),u1_struct_0(X10)) )
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f445])).

fof(f447,plain,
    ( spl3_72
    | ~ spl3_9
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f427,f420,f71,f445])).

fof(f71,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f420,plain,
    ( spl3_67
  <=> ! [X3,X4] :
        ( ~ m1_pre_topc(X3,X4)
        | ~ l1_pre_topc(X4)
        | r1_tarski(u1_struct_0(X3),u1_struct_0(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f427,plain,
    ( ! [X10,X11] :
        ( ~ l1_pre_topc(X10)
        | ~ m1_pre_topc(X11,X10)
        | u1_struct_0(X10) = k2_xboole_0(u1_struct_0(X11),u1_struct_0(X10)) )
    | ~ spl3_9
    | ~ spl3_67 ),
    inference(resolution,[],[f421,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f421,plain,
    ( ! [X4,X3] :
        ( r1_tarski(u1_struct_0(X3),u1_struct_0(X4))
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(X3,X4) )
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f420])).

fof(f422,plain,
    ( spl3_67
    | ~ spl3_12
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f414,f406,f83,f420])).

fof(f83,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f406,plain,
    ( spl3_64
  <=> ! [X1,X0] :
        ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f414,plain,
    ( ! [X4,X3] :
        ( ~ m1_pre_topc(X3,X4)
        | ~ l1_pre_topc(X4)
        | r1_tarski(u1_struct_0(X3),u1_struct_0(X4)) )
    | ~ spl3_12
    | ~ spl3_64 ),
    inference(resolution,[],[f407,f84])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f407,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f406])).

fof(f408,plain,
    ( spl3_64
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f403,f92,f63,f406])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f92,plain,
    ( spl3_14
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f403,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(resolution,[],[f64,f93])).

fof(f93,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f330,plain,
    ( spl3_52
    | ~ spl3_8
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f311,f303,f67,f327])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f303,plain,
    ( spl3_48
  <=> ! [X3,X2] :
        ( r1_tarski(X3,k2_xboole_0(X2,k1_zfmisc_1(u1_struct_0(sK1))))
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f311,plain,
    ( ! [X2,X3] :
        ( r1_tarski(X3,k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),X2))
        | ~ r1_tarski(X3,sK2) )
    | ~ spl3_8
    | ~ spl3_48 ),
    inference(superposition,[],[f304,f68])).

fof(f68,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f304,plain,
    ( ! [X2,X3] :
        ( r1_tarski(X3,k2_xboole_0(X2,k1_zfmisc_1(u1_struct_0(sK1))))
        | ~ r1_tarski(X3,sK2) )
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f303])).

fof(f305,plain,
    ( spl3_48
    | ~ spl3_22
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f300,f211,f138,f303])).

fof(f211,plain,
    ( spl3_35
  <=> ! [X12] : k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))) = k2_xboole_0(sK2,k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f300,plain,
    ( ! [X2,X3] :
        ( r1_tarski(X3,k2_xboole_0(X2,k1_zfmisc_1(u1_struct_0(sK1))))
        | ~ r1_tarski(X3,sK2) )
    | ~ spl3_22
    | ~ spl3_35 ),
    inference(superposition,[],[f139,f212])).

fof(f212,plain,
    ( ! [X12] : k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))) = k2_xboole_0(sK2,k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
    ( spl3_35
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f192,f134,f109,f211])).

fof(f109,plain,
    ( spl3_17
  <=> r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f134,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X2,X1) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f192,plain,
    ( ! [X12] : k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))) = k2_xboole_0(sK2,k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(resolution,[],[f135,f111])).

fof(f111,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f109])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X2,X1) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f134])).

fof(f141,plain,
    ( spl3_22
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f131,f87,f67,f138])).

fof(f87,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k2_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f131,plain,
    ( ! [X4,X5,X3] :
        ( r1_tarski(X5,k2_xboole_0(X4,X3))
        | ~ r1_tarski(X5,X4) )
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(superposition,[],[f88,f68])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k2_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f136,plain,
    ( spl3_21
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f129,f87,f71,f134])).

fof(f129,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X2,X1) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) )
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(resolution,[],[f88,f72])).

fof(f128,plain,
    ( spl3_20
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f124,f75,f71,f126])).

fof(f75,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_zfmisc_1(X1) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) )
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(resolution,[],[f76,f72])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f112,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f103,f83,f40,f109])).

fof(f40,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f103,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f84,f42])).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f107,plain,
    ( spl3_16
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f101,f92,f83,f105])).

fof(f101,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(resolution,[],[f84,f93])).

fof(f100,plain,
    ( ~ spl3_15
    | spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f95,f79,f35,f97])).

fof(f35,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f95,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1
    | ~ spl3_11 ),
    inference(resolution,[],[f80,f37])).

fof(f37,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f94,plain,
    ( spl3_14
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f90,f59,f55,f92])).

fof(f55,plain,
    ( spl3_5
  <=> ! [X0] : k2_subset_1(X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f59,plain,
    ( spl3_6
  <=> ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f90,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f60,f56])).

fof(f56,plain,
    ( ! [X0] : k2_subset_1(X0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f60,plain,
    ( ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f89,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f33,f87])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f85,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f31,f83])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f81,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f73,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f61,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f57,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f35])).

fof(f24,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (23712)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.42  % (23711)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.42  % (23715)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (23718)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (23721)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.43  % (23720)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.44  % (23713)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.44  % (23710)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (23716)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.44  % (23720)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f576,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f57,f61,f65,f69,f73,f77,f81,f85,f89,f94,f100,f107,f112,f128,f136,f141,f213,f305,f330,f408,f422,f447,f454,f472,f485,f516,f541,f555])).
% 0.21/0.44  fof(f555,plain,(
% 0.21/0.44    spl3_15 | ~spl3_16 | ~spl3_85),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f554])).
% 0.21/0.44  fof(f554,plain,(
% 0.21/0.44    $false | (spl3_15 | ~spl3_16 | ~spl3_85)),
% 0.21/0.44    inference(subsumption_resolution,[],[f548,f106])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f105])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    spl3_16 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.44  fof(f548,plain,(
% 0.21/0.44    ~r1_tarski(sK2,sK2) | (spl3_15 | ~spl3_85)),
% 0.21/0.44    inference(resolution,[],[f540,f99])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    ~r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f97])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    spl3_15 <=> r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.44  fof(f540,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2)) ) | ~spl3_85),
% 0.21/0.44    inference(avatar_component_clause,[],[f539])).
% 0.21/0.44  fof(f539,plain,(
% 0.21/0.44    spl3_85 <=> ! [X0] : (r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 0.21/0.44  fof(f541,plain,(
% 0.21/0.44    spl3_85 | ~spl3_52 | ~spl3_82),
% 0.21/0.44    inference(avatar_split_clause,[],[f520,f513,f327,f539])).
% 0.21/0.44  fof(f327,plain,(
% 0.21/0.44    spl3_52 <=> ! [X1,X0] : (r1_tarski(X1,k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),X0)) | ~r1_tarski(X1,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.44  fof(f513,plain,(
% 0.21/0.44    spl3_82 <=> k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 0.21/0.44  fof(f520,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2)) ) | (~spl3_52 | ~spl3_82)),
% 0.21/0.44    inference(superposition,[],[f328,f515])).
% 0.21/0.44  fof(f515,plain,(
% 0.21/0.44    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_82),
% 0.21/0.44    inference(avatar_component_clause,[],[f513])).
% 0.21/0.44  fof(f328,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(X1,k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),X0)) | ~r1_tarski(X1,sK2)) ) | ~spl3_52),
% 0.21/0.44    inference(avatar_component_clause,[],[f327])).
% 0.21/0.44  fof(f516,plain,(
% 0.21/0.44    spl3_82 | ~spl3_20 | ~spl3_76),
% 0.21/0.44    inference(avatar_split_clause,[],[f497,f482,f126,f513])).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    spl3_20 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k1_zfmisc_1(X1) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.44  fof(f482,plain,(
% 0.21/0.44    spl3_76 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 0.21/0.44  fof(f497,plain,(
% 0.21/0.44    k1_zfmisc_1(u1_struct_0(sK0)) = k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_20 | ~spl3_76)),
% 0.21/0.44    inference(resolution,[],[f484,f127])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_zfmisc_1(X1) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))) ) | ~spl3_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f126])).
% 0.21/0.44  fof(f484,plain,(
% 0.21/0.44    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl3_76),
% 0.21/0.44    inference(avatar_component_clause,[],[f482])).
% 0.21/0.44  fof(f485,plain,(
% 0.21/0.44    spl3_76 | ~spl3_16 | ~spl3_75),
% 0.21/0.44    inference(avatar_split_clause,[],[f479,f470,f105,f482])).
% 0.21/0.44  fof(f470,plain,(
% 0.21/0.44    spl3_75 <=> ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,u1_struct_0(sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 0.21/0.44  fof(f479,plain,(
% 0.21/0.44    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl3_16 | ~spl3_75)),
% 0.21/0.44    inference(resolution,[],[f471,f106])).
% 0.21/0.44  fof(f471,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK1)) | r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl3_75),
% 0.21/0.44    inference(avatar_component_clause,[],[f470])).
% 0.21/0.44  fof(f472,plain,(
% 0.21/0.44    spl3_75 | ~spl3_22 | ~spl3_73),
% 0.21/0.44    inference(avatar_split_clause,[],[f459,f451,f138,f470])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    spl3_22 <=> ! [X1,X0,X2] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.44  fof(f451,plain,(
% 0.21/0.44    spl3_73 <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.21/0.44  fof(f459,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,u1_struct_0(sK1))) ) | (~spl3_22 | ~spl3_73)),
% 0.21/0.44    inference(superposition,[],[f139,f453])).
% 0.21/0.44  fof(f453,plain,(
% 0.21/0.44    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl3_73),
% 0.21/0.44    inference(avatar_component_clause,[],[f451])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1)) ) | ~spl3_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f138])).
% 0.21/0.44  fof(f454,plain,(
% 0.21/0.44    spl3_73 | ~spl3_3 | ~spl3_4 | ~spl3_72),
% 0.21/0.44    inference(avatar_split_clause,[],[f449,f445,f50,f45,f451])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl3_3 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f445,plain,(
% 0.21/0.45    spl3_72 <=> ! [X11,X10] : (~l1_pre_topc(X10) | ~m1_pre_topc(X11,X10) | u1_struct_0(X10) = k2_xboole_0(u1_struct_0(X11),u1_struct_0(X10)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.21/0.45  fof(f449,plain,(
% 0.21/0.45    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl3_3 | ~spl3_4 | ~spl3_72)),
% 0.21/0.45    inference(subsumption_resolution,[],[f448,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f50])).
% 0.21/0.45  fof(f448,plain,(
% 0.21/0.45    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl3_3 | ~spl3_72)),
% 0.21/0.45    inference(resolution,[],[f446,f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    m1_pre_topc(sK1,sK0) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f45])).
% 0.21/0.45  fof(f446,plain,(
% 0.21/0.45    ( ! [X10,X11] : (~m1_pre_topc(X11,X10) | ~l1_pre_topc(X10) | u1_struct_0(X10) = k2_xboole_0(u1_struct_0(X11),u1_struct_0(X10))) ) | ~spl3_72),
% 0.21/0.45    inference(avatar_component_clause,[],[f445])).
% 0.21/0.45  fof(f447,plain,(
% 0.21/0.45    spl3_72 | ~spl3_9 | ~spl3_67),
% 0.21/0.45    inference(avatar_split_clause,[],[f427,f420,f71,f445])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    spl3_9 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.45  fof(f420,plain,(
% 0.21/0.45    spl3_67 <=> ! [X3,X4] : (~m1_pre_topc(X3,X4) | ~l1_pre_topc(X4) | r1_tarski(u1_struct_0(X3),u1_struct_0(X4)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.21/0.45  fof(f427,plain,(
% 0.21/0.45    ( ! [X10,X11] : (~l1_pre_topc(X10) | ~m1_pre_topc(X11,X10) | u1_struct_0(X10) = k2_xboole_0(u1_struct_0(X11),u1_struct_0(X10))) ) | (~spl3_9 | ~spl3_67)),
% 0.21/0.45    inference(resolution,[],[f421,f72])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f71])).
% 0.21/0.45  fof(f421,plain,(
% 0.21/0.45    ( ! [X4,X3] : (r1_tarski(u1_struct_0(X3),u1_struct_0(X4)) | ~l1_pre_topc(X4) | ~m1_pre_topc(X3,X4)) ) | ~spl3_67),
% 0.21/0.45    inference(avatar_component_clause,[],[f420])).
% 0.21/0.45  fof(f422,plain,(
% 0.21/0.45    spl3_67 | ~spl3_12 | ~spl3_64),
% 0.21/0.45    inference(avatar_split_clause,[],[f414,f406,f83,f420])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    spl3_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.45  fof(f406,plain,(
% 0.21/0.45    spl3_64 <=> ! [X1,X0] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.45  fof(f414,plain,(
% 0.21/0.45    ( ! [X4,X3] : (~m1_pre_topc(X3,X4) | ~l1_pre_topc(X4) | r1_tarski(u1_struct_0(X3),u1_struct_0(X4))) ) | (~spl3_12 | ~spl3_64)),
% 0.21/0.45    inference(resolution,[],[f407,f84])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl3_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f83])).
% 0.21/0.45  fof(f407,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) ) | ~spl3_64),
% 0.21/0.45    inference(avatar_component_clause,[],[f406])).
% 0.21/0.45  fof(f408,plain,(
% 0.21/0.45    spl3_64 | ~spl3_7 | ~spl3_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f403,f92,f63,f406])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    spl3_7 <=> ! [X1,X0,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    spl3_14 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.45  fof(f403,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) ) | (~spl3_7 | ~spl3_14)),
% 0.21/0.45    inference(resolution,[],[f64,f93])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f92])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f63])).
% 0.21/0.45  fof(f330,plain,(
% 0.21/0.45    spl3_52 | ~spl3_8 | ~spl3_48),
% 0.21/0.45    inference(avatar_split_clause,[],[f311,f303,f67,f327])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl3_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.45  fof(f303,plain,(
% 0.21/0.45    spl3_48 <=> ! [X3,X2] : (r1_tarski(X3,k2_xboole_0(X2,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r1_tarski(X3,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.45  fof(f311,plain,(
% 0.21/0.45    ( ! [X2,X3] : (r1_tarski(X3,k2_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)),X2)) | ~r1_tarski(X3,sK2)) ) | (~spl3_8 | ~spl3_48)),
% 0.21/0.45    inference(superposition,[],[f304,f68])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f67])).
% 0.21/0.45  fof(f304,plain,(
% 0.21/0.45    ( ! [X2,X3] : (r1_tarski(X3,k2_xboole_0(X2,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r1_tarski(X3,sK2)) ) | ~spl3_48),
% 0.21/0.45    inference(avatar_component_clause,[],[f303])).
% 0.21/0.45  fof(f305,plain,(
% 0.21/0.45    spl3_48 | ~spl3_22 | ~spl3_35),
% 0.21/0.45    inference(avatar_split_clause,[],[f300,f211,f138,f303])).
% 0.21/0.45  fof(f211,plain,(
% 0.21/0.45    spl3_35 <=> ! [X12] : k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))) = k2_xboole_0(sK2,k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.45  fof(f300,plain,(
% 0.21/0.45    ( ! [X2,X3] : (r1_tarski(X3,k2_xboole_0(X2,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r1_tarski(X3,sK2)) ) | (~spl3_22 | ~spl3_35)),
% 0.21/0.45    inference(superposition,[],[f139,f212])).
% 0.21/0.45  fof(f212,plain,(
% 0.21/0.45    ( ! [X12] : (k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))) = k2_xboole_0(sK2,k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))))) ) | ~spl3_35),
% 0.21/0.45    inference(avatar_component_clause,[],[f211])).
% 0.21/0.45  fof(f213,plain,(
% 0.21/0.45    spl3_35 | ~spl3_17 | ~spl3_21),
% 0.21/0.45    inference(avatar_split_clause,[],[f192,f134,f109,f211])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    spl3_17 <=> r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    spl3_21 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | k2_xboole_0(X2,X1) = k2_xboole_0(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.45  fof(f192,plain,(
% 0.21/0.45    ( ! [X12] : (k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))) = k2_xboole_0(sK2,k2_xboole_0(X12,k1_zfmisc_1(u1_struct_0(sK1))))) ) | (~spl3_17 | ~spl3_21)),
% 0.21/0.45    inference(resolution,[],[f135,f111])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl3_17),
% 0.21/0.45    inference(avatar_component_clause,[],[f109])).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X2,X1) = k2_xboole_0(X0,k2_xboole_0(X2,X1))) ) | ~spl3_21),
% 0.21/0.45    inference(avatar_component_clause,[],[f134])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    spl3_22 | ~spl3_8 | ~spl3_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f131,f87,f67,f138])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    spl3_13 <=> ! [X1,X0,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    ( ! [X4,X5,X3] : (r1_tarski(X5,k2_xboole_0(X4,X3)) | ~r1_tarski(X5,X4)) ) | (~spl3_8 | ~spl3_13)),
% 0.21/0.45    inference(superposition,[],[f88,f68])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f87])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    spl3_21 | ~spl3_9 | ~spl3_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f129,f87,f71,f134])).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X2,X1) = k2_xboole_0(X0,k2_xboole_0(X2,X1))) ) | (~spl3_9 | ~spl3_13)),
% 0.21/0.45    inference(resolution,[],[f88,f72])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    spl3_20 | ~spl3_9 | ~spl3_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f124,f75,f71,f126])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    spl3_10 <=> ! [X1,X0] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_zfmisc_1(X1) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))) ) | (~spl3_9 | ~spl3_10)),
% 0.21/0.45    inference(resolution,[],[f76,f72])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f75])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    spl3_17 | ~spl3_2 | ~spl3_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f103,f83,f40,f109])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | (~spl3_2 | ~spl3_12)),
% 0.21/0.45    inference(resolution,[],[f84,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f40])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    spl3_16 | ~spl3_12 | ~spl3_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f101,f92,f83,f105])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl3_12 | ~spl3_14)),
% 0.21/0.45    inference(resolution,[],[f84,f93])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    ~spl3_15 | spl3_1 | ~spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f95,f79,f35,f97])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    spl3_11 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ~r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_1 | ~spl3_11)),
% 0.21/0.45    inference(resolution,[],[f80,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f35])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f79])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    spl3_14 | ~spl3_5 | ~spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f90,f59,f55,f92])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    spl3_5 <=> ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl3_6 <=> ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl3_5 | ~spl3_6)),
% 0.21/0.45    inference(backward_demodulation,[],[f60,f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X0] : (k2_subset_1(X0) = X0) ) | ~spl3_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f55])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) ) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f59])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    spl3_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f33,f87])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl3_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f31,f83])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.45    inference(nnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f79])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    spl3_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f30,f75])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f71])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl3_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f67])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f59])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f55])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    l1_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ((~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17,f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,sK0)) => (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_pre_topc(sK1,sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) => (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f9])).
% 0.21/0.45  fof(f9,conjecture,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f45])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    m1_pre_topc(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f40])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f35])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (23720)------------------------------
% 0.21/0.45  % (23720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (23720)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (23720)Memory used [KB]: 6524
% 0.21/0.45  % (23720)Time elapsed: 0.046 s
% 0.21/0.45  % (23720)------------------------------
% 0.21/0.45  % (23720)------------------------------
% 0.21/0.45  % (23709)Success in time 0.1 s
%------------------------------------------------------------------------------
