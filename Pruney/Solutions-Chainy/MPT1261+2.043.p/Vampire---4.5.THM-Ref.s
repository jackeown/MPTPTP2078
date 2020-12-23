%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:54 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 339 expanded)
%              Number of leaves         :   52 ( 161 expanded)
%              Depth                    :   10
%              Number of atoms          :  546 (1095 expanded)
%              Number of equality atoms :  123 ( 258 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f91,f93,f101,f105,f113,f121,f133,f137,f147,f151,f171,f180,f193,f202,f215,f243,f258,f292,f350,f362,f367,f370,f405,f415,f423,f452,f521,f551,f841,f1601,f1894,f1947,f2259,f2413])).

fof(f2413,plain,
    ( spl2_30
    | ~ spl2_68
    | ~ spl2_170 ),
    inference(avatar_contradiction_clause,[],[f2412])).

fof(f2412,plain,
    ( $false
    | spl2_30
    | ~ spl2_68
    | ~ spl2_170 ),
    inference(subsumption_resolution,[],[f291,f2401])).

fof(f2401,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_68
    | ~ spl2_170 ),
    inference(superposition,[],[f2258,f840])).

fof(f840,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f838])).

fof(f838,plain,
    ( spl2_68
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f2258,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_170 ),
    inference(avatar_component_clause,[],[f2256])).

fof(f2256,plain,
    ( spl2_170
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_170])])).

fof(f291,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_30 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl2_30
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f2259,plain,
    ( spl2_170
    | ~ spl2_148
    | ~ spl2_161 ),
    inference(avatar_split_clause,[],[f2083,f1944,f1599,f2256])).

fof(f1599,plain,
    ( spl2_148
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_148])])).

fof(f1944,plain,
    ( spl2_161
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_161])])).

fof(f2083,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_148
    | ~ spl2_161 ),
    inference(superposition,[],[f1946,f1600])).

fof(f1600,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl2_148 ),
    inference(avatar_component_clause,[],[f1599])).

fof(f1946,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_161 ),
    inference(avatar_component_clause,[],[f1944])).

fof(f1947,plain,
    ( spl2_161
    | ~ spl2_43
    | ~ spl2_51
    | ~ spl2_156 ),
    inference(avatar_split_clause,[],[f1902,f1892,f518,f402,f1944])).

fof(f402,plain,
    ( spl2_43
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f518,plain,
    ( spl2_51
  <=> m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f1892,plain,
    ( spl2_156
  <=> ! [X3,X2] :
        ( k2_xboole_0(X2,X3) = X3
        | ~ m1_subset_1(k3_subset_1(X3,X2),k1_zfmisc_1(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_156])])).

fof(f1902,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_43
    | ~ spl2_51
    | ~ spl2_156 ),
    inference(unit_resulting_resolution,[],[f404,f520,f1893])).

fof(f1893,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k3_subset_1(X3,X2),k1_zfmisc_1(X3))
        | k2_xboole_0(X2,X3) = X3
        | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) )
    | ~ spl2_156 ),
    inference(avatar_component_clause,[],[f1892])).

fof(f520,plain,
    ( m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f518])).

fof(f404,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f402])).

fof(f1894,plain,
    ( spl2_156
    | ~ spl2_46
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f556,f549,f450,f1892])).

fof(f450,plain,
    ( spl2_46
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f549,plain,
    ( spl2_55
  <=> ! [X1,X0] :
        ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
        | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f556,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(X2,X3) = X3
        | ~ m1_subset_1(k3_subset_1(X3,X2),k1_zfmisc_1(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) )
    | ~ spl2_46
    | ~ spl2_55 ),
    inference(superposition,[],[f451,f550])).

fof(f550,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
        | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f549])).

fof(f451,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f450])).

fof(f1601,plain,
    ( spl2_148
    | ~ spl2_12
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f418,f413,f119,f1599])).

fof(f119,plain,
    ( spl2_12
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f413,plain,
    ( spl2_44
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f418,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl2_12
    | ~ spl2_44 ),
    inference(superposition,[],[f414,f120])).

fof(f120,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f414,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f413])).

fof(f841,plain,
    ( spl2_68
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_25
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f276,f255,f213,f191,f79,f74,f838])).

fof(f74,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f79,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f191,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f213,plain,
    ( spl2_25
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f255,plain,
    ( spl2_28
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f276,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_25
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f270,f233])).

fof(f233,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f76,f81,f214])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f213])).

fof(f81,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f76,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f270,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f81,f257,f192])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f191])).

fof(f257,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f255])).

fof(f551,plain,
    ( spl2_55
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f210,f191,f149,f549])).

fof(f149,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
        | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
        | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(superposition,[],[f192,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f521,plain,
    ( spl2_51
    | ~ spl2_37
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f445,f421,f347,f518])).

fof(f347,plain,
    ( spl2_37
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f421,plain,
    ( spl2_45
  <=> ! [X1,X0] : m1_subset_1(k3_subset_1(X0,k4_xboole_0(X0,X1)),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f445,plain,
    ( m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_37
    | ~ spl2_45 ),
    inference(superposition,[],[f422,f349])).

fof(f349,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f347])).

fof(f422,plain,
    ( ! [X0,X1] : m1_subset_1(k3_subset_1(X0,k4_xboole_0(X0,X1)),k1_zfmisc_1(X0))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f421])).

fof(f452,plain,
    ( spl2_46
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f152,f135,f99,f450])).

fof(f99,plain,
    ( spl2_7
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f135,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f152,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(superposition,[],[f136,f100])).

fof(f100,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f136,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f423,plain,
    ( spl2_45
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f143,f131,f103,f421])).

fof(f103,plain,
    ( spl2_8
  <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f131,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f143,plain,
    ( ! [X0,X1] : m1_subset_1(k3_subset_1(X0,k4_xboole_0(X0,X1)),k1_zfmisc_1(X0))
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f104,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f104,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f415,plain,
    ( spl2_44
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f128,f119,f111,f413])).

fof(f111,plain,
    ( spl2_10
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f128,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(superposition,[],[f120,f112])).

fof(f112,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f405,plain,
    ( spl2_43
    | ~ spl2_8
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f380,f347,f103,f402])).

fof(f380,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_8
    | ~ spl2_37 ),
    inference(superposition,[],[f104,f349])).

fof(f370,plain,
    ( spl2_5
    | ~ spl2_30
    | ~ spl2_38 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | spl2_5
    | ~ spl2_30
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f89,f368])).

fof(f368,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_30
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f366,f290])).

fof(f290,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f289])).

fof(f366,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl2_38
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f89,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f367,plain,
    ( spl2_38
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f244,f241,f79,f74,f364])).

fof(f241,plain,
    ( spl2_26
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f244,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f76,f81,f242])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f241])).

fof(f362,plain,
    ( ~ spl2_2
    | spl2_30
    | ~ spl2_4
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f197,f178,f79,f84,f289,f74])).

fof(f84,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f178,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f197,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(resolution,[],[f179,f81])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1
        | ~ l1_pre_topc(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f178])).

fof(f350,plain,
    ( ~ spl2_3
    | spl2_37
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f160,f145,f88,f347,f79])).

fof(f145,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f160,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(superposition,[],[f146,f90])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f292,plain,
    ( ~ spl2_30
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f232,f200,f84,f79,f74,f69,f289])).

fof(f69,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f200,plain,
    ( spl2_24
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f232,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f76,f71,f85,f81,f201])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f200])).

fof(f85,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f71,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f258,plain,
    ( spl2_28
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f186,f169,f79,f74,f255])).

fof(f169,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f186,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f76,f81,f170])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f169])).

fof(f243,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f49,f241])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f215,plain,(
    spl2_25 ),
    inference(avatar_split_clause,[],[f48,f213])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f202,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f51,f200])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f193,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f65,f191])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f180,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f50,f178])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f171,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f62,f169])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f151,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f67,f149])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f60,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f147,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f64,f145])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f137,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f63,f135])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f133,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f59,f131])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f121,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f57,f119])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f113,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f55,f111])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f105,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f66,f103])).

fof(f66,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f53,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f101,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f52,f99])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f93,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f92,f88,f84])).

fof(f92,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f46,f90])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f91,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f45,f88,f84])).

fof(f45,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f43,f74])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f42,f69])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n019.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 15:38:07 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.11/0.32  % (13961)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.11/0.32  % (13958)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.11/0.34  % (13957)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.11/0.34  % (13962)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.11/0.34  % (13949)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.11/0.35  % (13960)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.11/0.35  % (13954)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.11/0.35  % (13948)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.11/0.35  % (13950)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.11/0.36  % (13955)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.11/0.36  % (13959)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.11/0.36  % (13953)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.11/0.36  % (13963)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.11/0.37  % (13951)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.11/0.37  % (13952)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.11/0.40  % (13965)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.11/0.40  % (13956)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.11/0.41  % (13964)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.11/0.51  % (13953)Refutation found. Thanks to Tanya!
% 0.11/0.51  % SZS status Theorem for theBenchmark
% 0.11/0.51  % SZS output start Proof for theBenchmark
% 0.11/0.51  fof(f2419,plain,(
% 0.11/0.51    $false),
% 0.11/0.51    inference(avatar_sat_refutation,[],[f72,f77,f82,f91,f93,f101,f105,f113,f121,f133,f137,f147,f151,f171,f180,f193,f202,f215,f243,f258,f292,f350,f362,f367,f370,f405,f415,f423,f452,f521,f551,f841,f1601,f1894,f1947,f2259,f2413])).
% 0.11/0.51  fof(f2413,plain,(
% 0.11/0.51    spl2_30 | ~spl2_68 | ~spl2_170),
% 0.11/0.51    inference(avatar_contradiction_clause,[],[f2412])).
% 0.11/0.51  fof(f2412,plain,(
% 0.11/0.51    $false | (spl2_30 | ~spl2_68 | ~spl2_170)),
% 0.11/0.51    inference(subsumption_resolution,[],[f291,f2401])).
% 0.11/0.51  fof(f2401,plain,(
% 0.11/0.51    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_68 | ~spl2_170)),
% 0.11/0.51    inference(superposition,[],[f2258,f840])).
% 0.11/0.51  fof(f840,plain,(
% 0.11/0.51    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_68),
% 0.11/0.51    inference(avatar_component_clause,[],[f838])).
% 0.11/0.51  fof(f838,plain,(
% 0.11/0.51    spl2_68 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 0.11/0.51  fof(f2258,plain,(
% 0.11/0.51    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_170),
% 0.11/0.51    inference(avatar_component_clause,[],[f2256])).
% 0.11/0.51  fof(f2256,plain,(
% 0.11/0.51    spl2_170 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_170])])).
% 0.11/0.51  fof(f291,plain,(
% 0.11/0.51    sK1 != k2_pre_topc(sK0,sK1) | spl2_30),
% 0.11/0.51    inference(avatar_component_clause,[],[f289])).
% 0.11/0.51  fof(f289,plain,(
% 0.11/0.51    spl2_30 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.11/0.51  fof(f2259,plain,(
% 0.11/0.51    spl2_170 | ~spl2_148 | ~spl2_161),
% 0.11/0.51    inference(avatar_split_clause,[],[f2083,f1944,f1599,f2256])).
% 0.11/0.51  fof(f1599,plain,(
% 0.11/0.51    spl2_148 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_148])])).
% 0.11/0.51  fof(f1944,plain,(
% 0.11/0.51    spl2_161 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_161])])).
% 0.11/0.51  fof(f2083,plain,(
% 0.11/0.51    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_148 | ~spl2_161)),
% 0.11/0.51    inference(superposition,[],[f1946,f1600])).
% 0.11/0.51  fof(f1600,plain,(
% 0.11/0.51    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | ~spl2_148),
% 0.11/0.51    inference(avatar_component_clause,[],[f1599])).
% 0.11/0.51  fof(f1946,plain,(
% 0.11/0.51    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_161),
% 0.11/0.51    inference(avatar_component_clause,[],[f1944])).
% 0.11/0.51  fof(f1947,plain,(
% 0.11/0.51    spl2_161 | ~spl2_43 | ~spl2_51 | ~spl2_156),
% 0.11/0.51    inference(avatar_split_clause,[],[f1902,f1892,f518,f402,f1944])).
% 0.11/0.51  fof(f402,plain,(
% 0.11/0.51    spl2_43 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.11/0.51  fof(f518,plain,(
% 0.11/0.51    spl2_51 <=> m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.11/0.51  fof(f1892,plain,(
% 0.11/0.51    spl2_156 <=> ! [X3,X2] : (k2_xboole_0(X2,X3) = X3 | ~m1_subset_1(k3_subset_1(X3,X2),k1_zfmisc_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X3)))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_156])])).
% 0.11/0.51  fof(f1902,plain,(
% 0.11/0.51    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | (~spl2_43 | ~spl2_51 | ~spl2_156)),
% 0.11/0.51    inference(unit_resulting_resolution,[],[f404,f520,f1893])).
% 0.11/0.51  fof(f1893,plain,(
% 0.11/0.51    ( ! [X2,X3] : (~m1_subset_1(k3_subset_1(X3,X2),k1_zfmisc_1(X3)) | k2_xboole_0(X2,X3) = X3 | ~m1_subset_1(X2,k1_zfmisc_1(X3))) ) | ~spl2_156),
% 0.11/0.51    inference(avatar_component_clause,[],[f1892])).
% 0.11/0.51  fof(f520,plain,(
% 0.11/0.51    m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl2_51),
% 0.11/0.51    inference(avatar_component_clause,[],[f518])).
% 0.11/0.51  fof(f404,plain,(
% 0.11/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_43),
% 0.11/0.51    inference(avatar_component_clause,[],[f402])).
% 0.11/0.51  fof(f1894,plain,(
% 0.11/0.51    spl2_156 | ~spl2_46 | ~spl2_55),
% 0.11/0.51    inference(avatar_split_clause,[],[f556,f549,f450,f1892])).
% 0.11/0.51  fof(f450,plain,(
% 0.11/0.51    spl2_46 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.11/0.51  fof(f549,plain,(
% 0.11/0.51    spl2_55 <=> ! [X1,X0] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 0.11/0.51  fof(f556,plain,(
% 0.11/0.51    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X3 | ~m1_subset_1(k3_subset_1(X3,X2),k1_zfmisc_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X3))) ) | (~spl2_46 | ~spl2_55)),
% 0.11/0.51    inference(superposition,[],[f451,f550])).
% 0.11/0.51  fof(f550,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_55),
% 0.11/0.51    inference(avatar_component_clause,[],[f549])).
% 0.11/0.51  fof(f451,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl2_46),
% 0.11/0.51    inference(avatar_component_clause,[],[f450])).
% 0.11/0.51  fof(f1601,plain,(
% 0.11/0.51    spl2_148 | ~spl2_12 | ~spl2_44),
% 0.11/0.51    inference(avatar_split_clause,[],[f418,f413,f119,f1599])).
% 0.11/0.51  fof(f119,plain,(
% 0.11/0.51    spl2_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.11/0.51  fof(f413,plain,(
% 0.11/0.51    spl2_44 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.11/0.51  fof(f418,plain,(
% 0.11/0.51    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | (~spl2_12 | ~spl2_44)),
% 0.11/0.51    inference(superposition,[],[f414,f120])).
% 0.11/0.51  fof(f120,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) ) | ~spl2_12),
% 0.11/0.51    inference(avatar_component_clause,[],[f119])).
% 0.11/0.51  fof(f414,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) ) | ~spl2_44),
% 0.11/0.51    inference(avatar_component_clause,[],[f413])).
% 0.11/0.51  fof(f841,plain,(
% 0.11/0.51    spl2_68 | ~spl2_2 | ~spl2_3 | ~spl2_23 | ~spl2_25 | ~spl2_28),
% 0.11/0.51    inference(avatar_split_clause,[],[f276,f255,f213,f191,f79,f74,f838])).
% 0.11/0.51  fof(f74,plain,(
% 0.11/0.51    spl2_2 <=> l1_pre_topc(sK0)),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.11/0.51  fof(f79,plain,(
% 0.11/0.51    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.11/0.51  fof(f191,plain,(
% 0.11/0.51    spl2_23 <=> ! [X1,X0,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.11/0.51  fof(f213,plain,(
% 0.11/0.51    spl2_25 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.11/0.51  fof(f255,plain,(
% 0.11/0.51    spl2_28 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.11/0.51  fof(f276,plain,(
% 0.11/0.51    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_23 | ~spl2_25 | ~spl2_28)),
% 0.11/0.51    inference(forward_demodulation,[],[f270,f233])).
% 0.11/0.51  fof(f233,plain,(
% 0.11/0.51    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_25)),
% 0.11/0.51    inference(unit_resulting_resolution,[],[f76,f81,f214])).
% 0.11/0.51  fof(f214,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_25),
% 0.11/0.51    inference(avatar_component_clause,[],[f213])).
% 0.11/0.51  fof(f81,plain,(
% 0.11/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.11/0.51    inference(avatar_component_clause,[],[f79])).
% 0.11/0.51  fof(f76,plain,(
% 0.11/0.51    l1_pre_topc(sK0) | ~spl2_2),
% 0.11/0.51    inference(avatar_component_clause,[],[f74])).
% 0.11/0.51  fof(f270,plain,(
% 0.11/0.51    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_23 | ~spl2_28)),
% 0.11/0.51    inference(unit_resulting_resolution,[],[f81,f257,f192])).
% 0.11/0.51  fof(f192,plain,(
% 0.11/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_23),
% 0.11/0.51    inference(avatar_component_clause,[],[f191])).
% 0.11/0.51  fof(f257,plain,(
% 0.11/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_28),
% 0.11/0.51    inference(avatar_component_clause,[],[f255])).
% 0.11/0.51  fof(f551,plain,(
% 0.11/0.51    spl2_55 | ~spl2_18 | ~spl2_23),
% 0.11/0.51    inference(avatar_split_clause,[],[f210,f191,f149,f549])).
% 0.11/0.51  fof(f149,plain,(
% 0.11/0.51    spl2_18 <=> ! [X1,X0] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.11/0.51  fof(f210,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_18 | ~spl2_23)),
% 0.11/0.51    inference(duplicate_literal_removal,[],[f207])).
% 0.11/0.51  fof(f207,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_18 | ~spl2_23)),
% 0.11/0.51    inference(superposition,[],[f192,f150])).
% 0.11/0.51  fof(f150,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_18),
% 0.11/0.51    inference(avatar_component_clause,[],[f149])).
% 0.11/0.51  fof(f521,plain,(
% 0.11/0.51    spl2_51 | ~spl2_37 | ~spl2_45),
% 0.11/0.51    inference(avatar_split_clause,[],[f445,f421,f347,f518])).
% 0.11/0.51  fof(f347,plain,(
% 0.11/0.51    spl2_37 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.11/0.51  fof(f421,plain,(
% 0.11/0.51    spl2_45 <=> ! [X1,X0] : m1_subset_1(k3_subset_1(X0,k4_xboole_0(X0,X1)),k1_zfmisc_1(X0))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.11/0.51  fof(f445,plain,(
% 0.11/0.51    m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | (~spl2_37 | ~spl2_45)),
% 0.11/0.51    inference(superposition,[],[f422,f349])).
% 0.11/0.51  fof(f349,plain,(
% 0.11/0.51    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_37),
% 0.11/0.51    inference(avatar_component_clause,[],[f347])).
% 0.11/0.51  fof(f422,plain,(
% 0.11/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,k4_xboole_0(X0,X1)),k1_zfmisc_1(X0))) ) | ~spl2_45),
% 0.11/0.51    inference(avatar_component_clause,[],[f421])).
% 0.11/0.51  fof(f452,plain,(
% 0.11/0.51    spl2_46 | ~spl2_7 | ~spl2_15),
% 0.11/0.51    inference(avatar_split_clause,[],[f152,f135,f99,f450])).
% 0.11/0.51  fof(f99,plain,(
% 0.11/0.51    spl2_7 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.11/0.51  fof(f135,plain,(
% 0.11/0.51    spl2_15 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.11/0.51  fof(f152,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) ) | (~spl2_7 | ~spl2_15)),
% 0.11/0.51    inference(superposition,[],[f136,f100])).
% 0.11/0.51  fof(f100,plain,(
% 0.11/0.51    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl2_7),
% 0.11/0.51    inference(avatar_component_clause,[],[f99])).
% 0.11/0.51  fof(f136,plain,(
% 0.11/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_15),
% 0.11/0.51    inference(avatar_component_clause,[],[f135])).
% 0.11/0.51  fof(f423,plain,(
% 0.11/0.51    spl2_45 | ~spl2_8 | ~spl2_14),
% 0.11/0.51    inference(avatar_split_clause,[],[f143,f131,f103,f421])).
% 0.11/0.51  fof(f103,plain,(
% 0.11/0.51    spl2_8 <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.11/0.51  fof(f131,plain,(
% 0.11/0.51    spl2_14 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.11/0.51  fof(f143,plain,(
% 0.11/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,k4_xboole_0(X0,X1)),k1_zfmisc_1(X0))) ) | (~spl2_8 | ~spl2_14)),
% 0.11/0.51    inference(unit_resulting_resolution,[],[f104,f132])).
% 0.11/0.51  fof(f132,plain,(
% 0.11/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_14),
% 0.11/0.51    inference(avatar_component_clause,[],[f131])).
% 0.11/0.51  fof(f104,plain,(
% 0.11/0.51    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_8),
% 0.11/0.51    inference(avatar_component_clause,[],[f103])).
% 0.11/0.51  fof(f415,plain,(
% 0.11/0.51    spl2_44 | ~spl2_10 | ~spl2_12),
% 0.11/0.51    inference(avatar_split_clause,[],[f128,f119,f111,f413])).
% 0.11/0.51  fof(f111,plain,(
% 0.11/0.51    spl2_10 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.11/0.51  fof(f128,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) ) | (~spl2_10 | ~spl2_12)),
% 0.11/0.51    inference(superposition,[],[f120,f112])).
% 0.11/0.51  fof(f112,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_10),
% 0.11/0.51    inference(avatar_component_clause,[],[f111])).
% 0.11/0.51  fof(f405,plain,(
% 0.11/0.51    spl2_43 | ~spl2_8 | ~spl2_37),
% 0.11/0.51    inference(avatar_split_clause,[],[f380,f347,f103,f402])).
% 0.11/0.51  fof(f380,plain,(
% 0.11/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_8 | ~spl2_37)),
% 0.11/0.51    inference(superposition,[],[f104,f349])).
% 0.11/0.51  fof(f370,plain,(
% 0.11/0.51    spl2_5 | ~spl2_30 | ~spl2_38),
% 0.11/0.51    inference(avatar_contradiction_clause,[],[f369])).
% 0.11/0.51  fof(f369,plain,(
% 0.11/0.51    $false | (spl2_5 | ~spl2_30 | ~spl2_38)),
% 0.11/0.51    inference(subsumption_resolution,[],[f89,f368])).
% 0.11/0.51  fof(f368,plain,(
% 0.11/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_30 | ~spl2_38)),
% 0.11/0.51    inference(forward_demodulation,[],[f366,f290])).
% 0.11/0.51  fof(f290,plain,(
% 0.11/0.51    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_30),
% 0.11/0.51    inference(avatar_component_clause,[],[f289])).
% 0.11/0.51  fof(f366,plain,(
% 0.11/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_38),
% 0.11/0.51    inference(avatar_component_clause,[],[f364])).
% 0.11/0.51  fof(f364,plain,(
% 0.11/0.51    spl2_38 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.11/0.51  fof(f89,plain,(
% 0.11/0.51    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_5),
% 0.11/0.51    inference(avatar_component_clause,[],[f88])).
% 0.11/0.51  fof(f88,plain,(
% 0.11/0.51    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.11/0.51  fof(f367,plain,(
% 0.11/0.51    spl2_38 | ~spl2_2 | ~spl2_3 | ~spl2_26),
% 0.11/0.51    inference(avatar_split_clause,[],[f244,f241,f79,f74,f364])).
% 0.11/0.51  fof(f241,plain,(
% 0.11/0.51    spl2_26 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.11/0.51  fof(f244,plain,(
% 0.11/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_26)),
% 0.11/0.51    inference(unit_resulting_resolution,[],[f76,f81,f242])).
% 0.11/0.51  fof(f242,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_26),
% 0.11/0.51    inference(avatar_component_clause,[],[f241])).
% 0.11/0.51  fof(f362,plain,(
% 0.11/0.51    ~spl2_2 | spl2_30 | ~spl2_4 | ~spl2_3 | ~spl2_22),
% 0.11/0.51    inference(avatar_split_clause,[],[f197,f178,f79,f84,f289,f74])).
% 0.11/0.51  fof(f84,plain,(
% 0.11/0.51    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.11/0.51  fof(f178,plain,(
% 0.11/0.51    spl2_22 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.11/0.51  fof(f197,plain,(
% 0.11/0.51    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_22)),
% 0.11/0.51    inference(resolution,[],[f179,f81])).
% 0.11/0.51  fof(f179,plain,(
% 0.11/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) ) | ~spl2_22),
% 0.11/0.51    inference(avatar_component_clause,[],[f178])).
% 0.11/0.51  fof(f350,plain,(
% 0.11/0.51    ~spl2_3 | spl2_37 | ~spl2_5 | ~spl2_17),
% 0.11/0.51    inference(avatar_split_clause,[],[f160,f145,f88,f347,f79])).
% 0.11/0.51  fof(f145,plain,(
% 0.11/0.51    spl2_17 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.11/0.51  fof(f160,plain,(
% 0.11/0.51    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | ~spl2_17)),
% 0.11/0.51    inference(superposition,[],[f146,f90])).
% 0.11/0.51  fof(f90,plain,(
% 0.11/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 0.11/0.51    inference(avatar_component_clause,[],[f88])).
% 0.11/0.51  fof(f146,plain,(
% 0.11/0.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_17),
% 0.11/0.51    inference(avatar_component_clause,[],[f145])).
% 0.11/0.51  fof(f292,plain,(
% 0.11/0.51    ~spl2_30 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_24),
% 0.11/0.51    inference(avatar_split_clause,[],[f232,f200,f84,f79,f74,f69,f289])).
% 0.11/0.51  fof(f69,plain,(
% 0.11/0.51    spl2_1 <=> v2_pre_topc(sK0)),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.11/0.51  fof(f200,plain,(
% 0.11/0.51    spl2_24 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.11/0.51  fof(f232,plain,(
% 0.11/0.51    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_24)),
% 0.11/0.51    inference(unit_resulting_resolution,[],[f76,f71,f85,f81,f201])).
% 0.11/0.51  fof(f201,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_24),
% 0.11/0.51    inference(avatar_component_clause,[],[f200])).
% 0.11/0.51  fof(f85,plain,(
% 0.11/0.51    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 0.11/0.51    inference(avatar_component_clause,[],[f84])).
% 0.11/0.51  fof(f71,plain,(
% 0.11/0.51    v2_pre_topc(sK0) | ~spl2_1),
% 0.11/0.51    inference(avatar_component_clause,[],[f69])).
% 0.11/0.51  fof(f258,plain,(
% 0.11/0.51    spl2_28 | ~spl2_2 | ~spl2_3 | ~spl2_20),
% 0.11/0.51    inference(avatar_split_clause,[],[f186,f169,f79,f74,f255])).
% 0.11/0.51  fof(f169,plain,(
% 0.11/0.51    spl2_20 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.11/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.11/0.51  fof(f186,plain,(
% 0.11/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3 | ~spl2_20)),
% 0.11/0.51    inference(unit_resulting_resolution,[],[f76,f81,f170])).
% 0.11/0.51  fof(f170,plain,(
% 0.11/0.51    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_20),
% 0.11/0.51    inference(avatar_component_clause,[],[f169])).
% 0.11/0.51  fof(f243,plain,(
% 0.11/0.51    spl2_26),
% 0.11/0.51    inference(avatar_split_clause,[],[f49,f241])).
% 0.11/0.51  fof(f49,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.11/0.51    inference(cnf_transformation,[],[f25])).
% 0.11/0.51  fof(f25,plain,(
% 0.11/0.51    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.11/0.51    inference(ennf_transformation,[],[f17])).
% 0.11/0.51  fof(f17,axiom,(
% 0.11/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.11/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.11/0.51  fof(f215,plain,(
% 0.11/0.51    spl2_25),
% 0.11/0.51    inference(avatar_split_clause,[],[f48,f213])).
% 0.11/0.51  fof(f48,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.11/0.51    inference(cnf_transformation,[],[f24])).
% 0.11/0.51  fof(f24,plain,(
% 0.11/0.51    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.11/0.51    inference(ennf_transformation,[],[f18])).
% 0.11/0.51  fof(f18,axiom,(
% 0.11/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.11/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.11/0.51  fof(f202,plain,(
% 0.11/0.51    spl2_24),
% 0.11/0.51    inference(avatar_split_clause,[],[f51,f200])).
% 0.11/0.51  fof(f51,plain,(
% 0.11/0.51    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.11/0.51    inference(cnf_transformation,[],[f27])).
% 0.11/0.51  fof(f27,plain,(
% 0.11/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.11/0.51    inference(flattening,[],[f26])).
% 0.11/0.51  fof(f26,plain,(
% 0.11/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.11/0.51    inference(ennf_transformation,[],[f14])).
% 0.11/0.51  fof(f14,axiom,(
% 0.11/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.11/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.11/0.51  fof(f193,plain,(
% 0.11/0.51    spl2_23),
% 0.11/0.51    inference(avatar_split_clause,[],[f65,f191])).
% 0.11/0.51  fof(f65,plain,(
% 0.11/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.51    inference(cnf_transformation,[],[f36])).
% 0.11/0.51  fof(f36,plain,(
% 0.11/0.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.51    inference(flattening,[],[f35])).
% 0.11/0.51  fof(f35,plain,(
% 0.11/0.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.11/0.51    inference(ennf_transformation,[],[f9])).
% 0.11/0.51  fof(f9,axiom,(
% 0.11/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.11/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.11/0.51  fof(f180,plain,(
% 0.11/0.51    spl2_22),
% 0.11/0.51    inference(avatar_split_clause,[],[f50,f178])).
% 0.11/0.51  fof(f50,plain,(
% 0.11/0.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.11/0.52    inference(cnf_transformation,[],[f27])).
% 0.11/0.52  fof(f171,plain,(
% 0.11/0.52    spl2_20),
% 0.11/0.52    inference(avatar_split_clause,[],[f62,f169])).
% 0.11/0.52  fof(f62,plain,(
% 0.11/0.52    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.11/0.52    inference(cnf_transformation,[],[f33])).
% 0.11/0.52  fof(f33,plain,(
% 0.11/0.52    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.11/0.52    inference(flattening,[],[f32])).
% 0.11/0.52  fof(f32,plain,(
% 0.11/0.52    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.11/0.52    inference(ennf_transformation,[],[f15])).
% 0.11/0.52  fof(f15,axiom,(
% 0.11/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.11/0.52  fof(f151,plain,(
% 0.11/0.52    spl2_18),
% 0.11/0.52    inference(avatar_split_clause,[],[f67,f149])).
% 0.11/0.52  fof(f67,plain,(
% 0.11/0.52    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.52    inference(forward_demodulation,[],[f60,f47])).
% 0.11/0.52  fof(f47,plain,(
% 0.11/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.11/0.52    inference(cnf_transformation,[],[f6])).
% 0.11/0.52  fof(f6,axiom,(
% 0.11/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.11/0.52  fof(f60,plain,(
% 0.11/0.52    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.52    inference(cnf_transformation,[],[f29])).
% 0.11/0.52  fof(f29,plain,(
% 0.11/0.52    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.52    inference(ennf_transformation,[],[f12])).
% 0.11/0.52  fof(f12,axiom,(
% 0.11/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 0.11/0.52  fof(f147,plain,(
% 0.11/0.52    spl2_17),
% 0.11/0.52    inference(avatar_split_clause,[],[f64,f145])).
% 0.11/0.52  fof(f64,plain,(
% 0.11/0.52    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.52    inference(cnf_transformation,[],[f34])).
% 0.11/0.52  fof(f34,plain,(
% 0.11/0.52    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.52    inference(ennf_transformation,[],[f11])).
% 0.11/0.52  fof(f11,axiom,(
% 0.11/0.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.11/0.52  fof(f137,plain,(
% 0.11/0.52    spl2_15),
% 0.11/0.52    inference(avatar_split_clause,[],[f63,f135])).
% 0.11/0.52  fof(f63,plain,(
% 0.11/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.11/0.52    inference(cnf_transformation,[],[f3])).
% 0.11/0.52  fof(f3,axiom,(
% 0.11/0.52    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.11/0.52  fof(f133,plain,(
% 0.11/0.52    spl2_14),
% 0.11/0.52    inference(avatar_split_clause,[],[f59,f131])).
% 0.11/0.52  fof(f59,plain,(
% 0.11/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.52    inference(cnf_transformation,[],[f28])).
% 0.11/0.52  fof(f28,plain,(
% 0.11/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.52    inference(ennf_transformation,[],[f7])).
% 0.11/0.52  fof(f7,axiom,(
% 0.11/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.11/0.52  fof(f121,plain,(
% 0.11/0.52    spl2_12),
% 0.11/0.52    inference(avatar_split_clause,[],[f57,f119])).
% 0.11/0.52  fof(f57,plain,(
% 0.11/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.11/0.52    inference(cnf_transformation,[],[f5])).
% 0.11/0.52  fof(f5,axiom,(
% 0.11/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.11/0.52  fof(f113,plain,(
% 0.11/0.52    spl2_10),
% 0.11/0.52    inference(avatar_split_clause,[],[f55,f111])).
% 0.11/0.52  fof(f55,plain,(
% 0.11/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.11/0.52    inference(cnf_transformation,[],[f4])).
% 0.11/0.52  fof(f4,axiom,(
% 0.11/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.11/0.52  fof(f105,plain,(
% 0.11/0.52    spl2_8),
% 0.11/0.52    inference(avatar_split_clause,[],[f66,f103])).
% 0.11/0.52  fof(f66,plain,(
% 0.11/0.52    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.11/0.52    inference(forward_demodulation,[],[f53,f54])).
% 0.11/0.52  fof(f54,plain,(
% 0.11/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.11/0.52    inference(cnf_transformation,[],[f10])).
% 0.11/0.52  fof(f10,axiom,(
% 0.11/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.11/0.52  fof(f53,plain,(
% 0.11/0.52    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.11/0.52    inference(cnf_transformation,[],[f8])).
% 0.11/0.52  fof(f8,axiom,(
% 0.11/0.52    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.11/0.52  fof(f101,plain,(
% 0.11/0.52    spl2_7),
% 0.11/0.52    inference(avatar_split_clause,[],[f52,f99])).
% 0.11/0.52  fof(f52,plain,(
% 0.11/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.11/0.52    inference(cnf_transformation,[],[f21])).
% 0.11/0.52  fof(f21,plain,(
% 0.11/0.52    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.11/0.52    inference(rectify,[],[f1])).
% 0.11/0.52  fof(f1,axiom,(
% 0.11/0.52    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.11/0.52  fof(f93,plain,(
% 0.11/0.52    ~spl2_4 | ~spl2_5),
% 0.11/0.52    inference(avatar_split_clause,[],[f92,f88,f84])).
% 0.11/0.52  fof(f92,plain,(
% 0.11/0.52    ~v4_pre_topc(sK1,sK0) | ~spl2_5),
% 0.11/0.52    inference(subsumption_resolution,[],[f46,f90])).
% 0.11/0.52  fof(f46,plain,(
% 0.11/0.52    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.11/0.52    inference(cnf_transformation,[],[f41])).
% 0.11/0.52  fof(f41,plain,(
% 0.11/0.52    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.11/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.11/0.52  fof(f39,plain,(
% 0.11/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.11/0.52    introduced(choice_axiom,[])).
% 0.11/0.52  fof(f40,plain,(
% 0.11/0.52    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.11/0.52    introduced(choice_axiom,[])).
% 0.11/0.52  fof(f38,plain,(
% 0.11/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.11/0.52    inference(flattening,[],[f37])).
% 0.11/0.52  fof(f37,plain,(
% 0.11/0.52    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.11/0.52    inference(nnf_transformation,[],[f23])).
% 0.11/0.52  fof(f23,plain,(
% 0.11/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.11/0.52    inference(flattening,[],[f22])).
% 0.11/0.52  fof(f22,plain,(
% 0.11/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.11/0.52    inference(ennf_transformation,[],[f20])).
% 0.11/0.52  fof(f20,negated_conjecture,(
% 0.11/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.11/0.52    inference(negated_conjecture,[],[f19])).
% 0.11/0.52  fof(f19,conjecture,(
% 0.11/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.11/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.11/0.52  fof(f91,plain,(
% 0.11/0.52    spl2_4 | spl2_5),
% 0.11/0.52    inference(avatar_split_clause,[],[f45,f88,f84])).
% 0.11/0.52  fof(f45,plain,(
% 0.11/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.11/0.52    inference(cnf_transformation,[],[f41])).
% 0.11/0.52  fof(f82,plain,(
% 0.11/0.52    spl2_3),
% 0.11/0.52    inference(avatar_split_clause,[],[f44,f79])).
% 0.11/0.52  fof(f44,plain,(
% 0.11/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.11/0.52    inference(cnf_transformation,[],[f41])).
% 0.11/0.52  fof(f77,plain,(
% 0.11/0.52    spl2_2),
% 0.11/0.52    inference(avatar_split_clause,[],[f43,f74])).
% 0.11/0.52  fof(f43,plain,(
% 0.11/0.52    l1_pre_topc(sK0)),
% 0.11/0.52    inference(cnf_transformation,[],[f41])).
% 0.11/0.52  fof(f72,plain,(
% 0.11/0.52    spl2_1),
% 0.11/0.52    inference(avatar_split_clause,[],[f42,f69])).
% 0.11/0.52  fof(f42,plain,(
% 0.11/0.52    v2_pre_topc(sK0)),
% 0.11/0.52    inference(cnf_transformation,[],[f41])).
% 0.11/0.52  % SZS output end Proof for theBenchmark
% 0.11/0.52  % (13953)------------------------------
% 0.11/0.52  % (13953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.52  % (13953)Termination reason: Refutation
% 0.11/0.52  
% 0.11/0.52  % (13953)Memory used [KB]: 8827
% 0.11/0.52  % (13953)Time elapsed: 0.199 s
% 0.11/0.52  % (13953)------------------------------
% 0.11/0.52  % (13953)------------------------------
% 0.11/0.52  % (13947)Success in time 0.253 s
%------------------------------------------------------------------------------
