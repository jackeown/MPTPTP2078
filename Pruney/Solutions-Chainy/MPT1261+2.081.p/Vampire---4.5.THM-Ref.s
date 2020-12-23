%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 322 expanded)
%              Number of leaves         :   47 ( 151 expanded)
%              Depth                    :   10
%              Number of atoms          :  503 (1030 expanded)
%              Number of equality atoms :  125 ( 270 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f675,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f76,f78,f82,f86,f94,f102,f106,f110,f122,f129,f133,f137,f142,f149,f155,f167,f175,f192,f219,f227,f240,f248,f254,f310,f312,f324,f344,f442,f509,f564,f635,f674])).

fof(f674,plain,
    ( spl2_23
    | ~ spl2_38
    | ~ spl2_72 ),
    inference(avatar_contradiction_clause,[],[f673])).

fof(f673,plain,
    ( $false
    | spl2_23
    | ~ spl2_38
    | ~ spl2_72 ),
    inference(subsumption_resolution,[],[f191,f668])).

fof(f668,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_38
    | ~ spl2_72 ),
    inference(superposition,[],[f634,f343])).

fof(f343,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl2_38
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f634,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f632])).

fof(f632,plain,
    ( spl2_72
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f191,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_23 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl2_23
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f635,plain,
    ( spl2_72
    | ~ spl2_52
    | ~ spl2_62 ),
    inference(avatar_split_clause,[],[f599,f561,f440,f632])).

fof(f440,plain,
    ( spl2_52
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f561,plain,
    ( spl2_62
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).

fof(f599,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_52
    | ~ spl2_62 ),
    inference(superposition,[],[f563,f441])).

fof(f441,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f440])).

fof(f563,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_62 ),
    inference(avatar_component_clause,[],[f561])).

fof(f564,plain,
    ( spl2_62
    | ~ spl2_12
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f532,f506,f104,f561])).

fof(f104,plain,
    ( spl2_12
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f506,plain,
    ( spl2_58
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f532,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_12
    | ~ spl2_58 ),
    inference(superposition,[],[f105,f508])).

fof(f508,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f506])).

fof(f105,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f509,plain,
    ( spl2_58
    | ~ spl2_37
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f444,f440,f307,f506])).

fof(f307,plain,
    ( spl2_37
  <=> sK1 = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f444,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_37
    | ~ spl2_52 ),
    inference(superposition,[],[f441,f309])).

fof(f309,plain,
    ( sK1 = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f307])).

fof(f442,plain,
    ( spl2_52
    | ~ spl2_9
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f243,f238,f92,f440])).

fof(f92,plain,
    ( spl2_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f238,plain,
    ( spl2_30
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f243,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl2_9
    | ~ spl2_30 ),
    inference(superposition,[],[f239,f93])).

fof(f93,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f239,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f238])).

fof(f344,plain,
    ( spl2_38
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_20
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f186,f172,f153,f140,f64,f59,f341])).

fof(f59,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f64,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f140,plain,
    ( spl2_18
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f153,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f172,plain,
    ( spl2_22
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f186,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_20
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f181,f159])).

fof(f159,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f61,f66,f154])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f61,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f181,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f66,f174,f141])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f174,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f172])).

fof(f324,plain,
    ( spl2_5
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl2_5
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f74,f317])).

fof(f317,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(superposition,[],[f218,f190])).

fof(f190,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f189])).

fof(f218,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl2_27
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f74,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f312,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_17
    | spl2_23 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_17
    | spl2_23 ),
    inference(subsumption_resolution,[],[f193,f71])).

fof(f71,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f193,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_17
    | spl2_23 ),
    inference(unit_resulting_resolution,[],[f61,f66,f191,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1
        | ~ l1_pre_topc(X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f310,plain,
    ( spl2_37
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f256,f252,f211,f307])).

fof(f211,plain,
    ( spl2_26
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f252,plain,
    ( spl2_32
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f256,plain,
    ( sK1 = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(superposition,[],[f253,f213])).

fof(f213,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f211])).

fof(f253,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f252])).

fof(f254,plain,
    ( spl2_32
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f250,f246,f238,f92,f84,f252])).

fof(f84,plain,
    ( spl2_7
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f246,plain,
    ( spl2_31
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f250,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f249,f85])).

fof(f85,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f249,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl2_9
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f247,f243])).

fof(f247,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f246])).

fof(f248,plain,
    ( spl2_31
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f117,f108,f100,f246])).

fof(f100,plain,
    ( spl2_11
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f108,plain,
    ( spl2_13
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f117,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(superposition,[],[f109,f101])).

fof(f101,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f109,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f240,plain,
    ( spl2_30
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f113,f92,f80,f238])).

fof(f80,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f113,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(superposition,[],[f93,f81])).

fof(f81,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f227,plain,
    ( spl2_26
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f156,f127,f73,f211])).

fof(f127,plain,
    ( spl2_15
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f156,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(superposition,[],[f128,f75])).

fof(f75,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f128,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f127])).

fof(f219,plain,
    ( spl2_27
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f168,f165,f64,f59,f216])).

fof(f165,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f168,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f61,f66,f166])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f165])).

fof(f192,plain,
    ( ~ spl2_23
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f158,f147,f69,f64,f59,f54,f189])).

fof(f54,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f147,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f158,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_19 ),
    inference(unit_resulting_resolution,[],[f61,f56,f70,f66,f148])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f70,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f56,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f175,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f138,f131,f64,f59,f172])).

fof(f131,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f138,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f61,f66,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f167,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f39,f165])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f155,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f38,f153])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f149,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f41,f147])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f142,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f52,f140])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f137,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f40,f135])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f133,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f50,f131])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f129,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f123,f120,f64,f127])).

fof(f120,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f123,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f66,f121])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f51,f120])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f110,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f49,f108])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f106,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f48,f104])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f102,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f47,f100])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f94,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f86,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f43,f84])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f82,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f42,f80])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f78,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f77,f73,f69])).

fof(f77,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f37,f75])).

fof(f37,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f76,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f36,f73,f69])).

fof(f36,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f34,f59])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f33,f54])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_vampire %s %d
% 0.16/0.35  % Computer   : n007.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % WCLimit    : 600
% 0.16/0.35  % DateTime   : Tue Dec  1 19:11:36 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.22/0.45  % (13421)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (13421)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f675,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f57,f62,f67,f76,f78,f82,f86,f94,f102,f106,f110,f122,f129,f133,f137,f142,f149,f155,f167,f175,f192,f219,f227,f240,f248,f254,f310,f312,f324,f344,f442,f509,f564,f635,f674])).
% 0.22/0.46  fof(f674,plain,(
% 0.22/0.46    spl2_23 | ~spl2_38 | ~spl2_72),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f673])).
% 0.22/0.46  fof(f673,plain,(
% 0.22/0.46    $false | (spl2_23 | ~spl2_38 | ~spl2_72)),
% 0.22/0.46    inference(subsumption_resolution,[],[f191,f668])).
% 0.22/0.46  fof(f668,plain,(
% 0.22/0.46    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_38 | ~spl2_72)),
% 0.22/0.46    inference(superposition,[],[f634,f343])).
% 0.22/0.46  fof(f343,plain,(
% 0.22/0.46    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_38),
% 0.22/0.46    inference(avatar_component_clause,[],[f341])).
% 0.22/0.46  fof(f341,plain,(
% 0.22/0.46    spl2_38 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.22/0.46  fof(f634,plain,(
% 0.22/0.46    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_72),
% 0.22/0.46    inference(avatar_component_clause,[],[f632])).
% 0.22/0.46  fof(f632,plain,(
% 0.22/0.46    spl2_72 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 0.22/0.46  fof(f191,plain,(
% 0.22/0.46    sK1 != k2_pre_topc(sK0,sK1) | spl2_23),
% 0.22/0.46    inference(avatar_component_clause,[],[f189])).
% 0.22/0.46  fof(f189,plain,(
% 0.22/0.46    spl2_23 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.46  fof(f635,plain,(
% 0.22/0.46    spl2_72 | ~spl2_52 | ~spl2_62),
% 0.22/0.46    inference(avatar_split_clause,[],[f599,f561,f440,f632])).
% 0.22/0.46  fof(f440,plain,(
% 0.22/0.46    spl2_52 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 0.22/0.46  fof(f561,plain,(
% 0.22/0.46    spl2_62 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).
% 0.22/0.46  fof(f599,plain,(
% 0.22/0.46    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_52 | ~spl2_62)),
% 0.22/0.46    inference(superposition,[],[f563,f441])).
% 0.22/0.46  fof(f441,plain,(
% 0.22/0.46    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | ~spl2_52),
% 0.22/0.46    inference(avatar_component_clause,[],[f440])).
% 0.22/0.46  fof(f563,plain,(
% 0.22/0.46    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_62),
% 0.22/0.46    inference(avatar_component_clause,[],[f561])).
% 0.22/0.46  fof(f564,plain,(
% 0.22/0.46    spl2_62 | ~spl2_12 | ~spl2_58),
% 0.22/0.46    inference(avatar_split_clause,[],[f532,f506,f104,f561])).
% 0.22/0.46  fof(f104,plain,(
% 0.22/0.46    spl2_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.46  fof(f506,plain,(
% 0.22/0.46    spl2_58 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 0.22/0.46  fof(f532,plain,(
% 0.22/0.46    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | (~spl2_12 | ~spl2_58)),
% 0.22/0.46    inference(superposition,[],[f105,f508])).
% 0.22/0.46  fof(f508,plain,(
% 0.22/0.46    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~spl2_58),
% 0.22/0.46    inference(avatar_component_clause,[],[f506])).
% 0.22/0.46  fof(f105,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl2_12),
% 0.22/0.46    inference(avatar_component_clause,[],[f104])).
% 0.22/0.46  fof(f509,plain,(
% 0.22/0.46    spl2_58 | ~spl2_37 | ~spl2_52),
% 0.22/0.46    inference(avatar_split_clause,[],[f444,f440,f307,f506])).
% 0.22/0.46  fof(f307,plain,(
% 0.22/0.46    spl2_37 <=> sK1 = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.22/0.46  fof(f444,plain,(
% 0.22/0.46    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | (~spl2_37 | ~spl2_52)),
% 0.22/0.46    inference(superposition,[],[f441,f309])).
% 0.22/0.46  fof(f309,plain,(
% 0.22/0.46    sK1 = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~spl2_37),
% 0.22/0.46    inference(avatar_component_clause,[],[f307])).
% 0.22/0.46  fof(f442,plain,(
% 0.22/0.46    spl2_52 | ~spl2_9 | ~spl2_30),
% 0.22/0.46    inference(avatar_split_clause,[],[f243,f238,f92,f440])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    spl2_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.46  fof(f238,plain,(
% 0.22/0.46    spl2_30 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.46  fof(f243,plain,(
% 0.22/0.46    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | (~spl2_9 | ~spl2_30)),
% 0.22/0.46    inference(superposition,[],[f239,f93])).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) ) | ~spl2_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f92])).
% 0.22/0.46  fof(f239,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) ) | ~spl2_30),
% 0.22/0.46    inference(avatar_component_clause,[],[f238])).
% 0.22/0.46  fof(f344,plain,(
% 0.22/0.46    spl2_38 | ~spl2_2 | ~spl2_3 | ~spl2_18 | ~spl2_20 | ~spl2_22),
% 0.22/0.46    inference(avatar_split_clause,[],[f186,f172,f153,f140,f64,f59,f341])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    spl2_2 <=> l1_pre_topc(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.46  fof(f140,plain,(
% 0.22/0.46    spl2_18 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.46  fof(f153,plain,(
% 0.22/0.46    spl2_20 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.46  fof(f172,plain,(
% 0.22/0.46    spl2_22 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.46  fof(f186,plain,(
% 0.22/0.46    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_18 | ~spl2_20 | ~spl2_22)),
% 0.22/0.46    inference(forward_demodulation,[],[f181,f159])).
% 0.22/0.46  fof(f159,plain,(
% 0.22/0.46    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_20)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f61,f66,f154])).
% 0.22/0.46  fof(f154,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_20),
% 0.22/0.46    inference(avatar_component_clause,[],[f153])).
% 0.22/0.46  fof(f66,plain,(
% 0.22/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f64])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    l1_pre_topc(sK0) | ~spl2_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f59])).
% 0.22/0.46  fof(f181,plain,(
% 0.22/0.46    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_18 | ~spl2_22)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f66,f174,f141])).
% 0.22/0.46  fof(f141,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f140])).
% 0.22/0.46  fof(f174,plain,(
% 0.22/0.46    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_22),
% 0.22/0.46    inference(avatar_component_clause,[],[f172])).
% 0.22/0.46  fof(f324,plain,(
% 0.22/0.46    spl2_5 | ~spl2_23 | ~spl2_27),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f323])).
% 0.22/0.46  fof(f323,plain,(
% 0.22/0.46    $false | (spl2_5 | ~spl2_23 | ~spl2_27)),
% 0.22/0.46    inference(subsumption_resolution,[],[f74,f317])).
% 0.22/0.46  fof(f317,plain,(
% 0.22/0.46    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_23 | ~spl2_27)),
% 0.22/0.46    inference(superposition,[],[f218,f190])).
% 0.22/0.46  fof(f190,plain,(
% 0.22/0.46    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_23),
% 0.22/0.46    inference(avatar_component_clause,[],[f189])).
% 0.22/0.46  fof(f218,plain,(
% 0.22/0.46    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_27),
% 0.22/0.46    inference(avatar_component_clause,[],[f216])).
% 0.22/0.46  fof(f216,plain,(
% 0.22/0.46    spl2_27 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.46  fof(f74,plain,(
% 0.22/0.46    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f73])).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.46  fof(f312,plain,(
% 0.22/0.46    ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_17 | spl2_23),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f311])).
% 0.22/0.46  fof(f311,plain,(
% 0.22/0.46    $false | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_17 | spl2_23)),
% 0.22/0.46    inference(subsumption_resolution,[],[f193,f71])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    v4_pre_topc(sK1,sK0) | ~spl2_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f69])).
% 0.22/0.46  fof(f69,plain,(
% 0.22/0.46    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.46  fof(f193,plain,(
% 0.22/0.46    ~v4_pre_topc(sK1,sK0) | (~spl2_2 | ~spl2_3 | ~spl2_17 | spl2_23)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f61,f66,f191,f136])).
% 0.22/0.46  fof(f136,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) ) | ~spl2_17),
% 0.22/0.46    inference(avatar_component_clause,[],[f135])).
% 0.22/0.46  fof(f135,plain,(
% 0.22/0.46    spl2_17 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.47  fof(f310,plain,(
% 0.22/0.47    spl2_37 | ~spl2_26 | ~spl2_32),
% 0.22/0.47    inference(avatar_split_clause,[],[f256,f252,f211,f307])).
% 0.22/0.47  fof(f211,plain,(
% 0.22/0.47    spl2_26 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.47  fof(f252,plain,(
% 0.22/0.47    spl2_32 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.47  fof(f256,plain,(
% 0.22/0.47    sK1 = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | (~spl2_26 | ~spl2_32)),
% 0.22/0.47    inference(superposition,[],[f253,f213])).
% 0.22/0.47  fof(f213,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_26),
% 0.22/0.47    inference(avatar_component_clause,[],[f211])).
% 0.22/0.47  fof(f253,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_32),
% 0.22/0.47    inference(avatar_component_clause,[],[f252])).
% 0.22/0.47  fof(f254,plain,(
% 0.22/0.47    spl2_32 | ~spl2_7 | ~spl2_9 | ~spl2_30 | ~spl2_31),
% 0.22/0.47    inference(avatar_split_clause,[],[f250,f246,f238,f92,f84,f252])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    spl2_7 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  fof(f246,plain,(
% 0.22/0.47    spl2_31 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.22/0.47  fof(f250,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | (~spl2_7 | ~spl2_9 | ~spl2_30 | ~spl2_31)),
% 0.22/0.47    inference(forward_demodulation,[],[f249,f85])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl2_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f84])).
% 0.22/0.47  fof(f249,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl2_9 | ~spl2_30 | ~spl2_31)),
% 0.22/0.47    inference(forward_demodulation,[],[f247,f243])).
% 0.22/0.47  fof(f247,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | ~spl2_31),
% 0.22/0.47    inference(avatar_component_clause,[],[f246])).
% 0.22/0.47  fof(f248,plain,(
% 0.22/0.47    spl2_31 | ~spl2_11 | ~spl2_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f117,f108,f100,f246])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    spl2_11 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    spl2_13 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl2_11 | ~spl2_13)),
% 0.22/0.47    inference(superposition,[],[f109,f101])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f100])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) ) | ~spl2_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f108])).
% 0.22/0.47  fof(f240,plain,(
% 0.22/0.47    spl2_30 | ~spl2_6 | ~spl2_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f113,f92,f80,f238])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl2_6 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) ) | (~spl2_6 | ~spl2_9)),
% 0.22/0.47    inference(superposition,[],[f93,f81])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f80])).
% 0.22/0.47  fof(f227,plain,(
% 0.22/0.47    spl2_26 | ~spl2_5 | ~spl2_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f156,f127,f73,f211])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    spl2_15 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_15)),
% 0.22/0.47    inference(superposition,[],[f128,f75])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f73])).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl2_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f127])).
% 0.22/0.47  fof(f219,plain,(
% 0.22/0.47    spl2_27 | ~spl2_2 | ~spl2_3 | ~spl2_21),
% 0.22/0.47    inference(avatar_split_clause,[],[f168,f165,f64,f59,f216])).
% 0.22/0.47  fof(f165,plain,(
% 0.22/0.47    spl2_21 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.47  fof(f168,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_21)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f61,f66,f166])).
% 0.22/0.47  fof(f166,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_21),
% 0.22/0.47    inference(avatar_component_clause,[],[f165])).
% 0.22/0.47  fof(f192,plain,(
% 0.22/0.47    ~spl2_23 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_19),
% 0.22/0.47    inference(avatar_split_clause,[],[f158,f147,f69,f64,f59,f54,f189])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    spl2_1 <=> v2_pre_topc(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f147,plain,(
% 0.22/0.47    spl2_19 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.47  fof(f158,plain,(
% 0.22/0.47    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_19)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f61,f56,f70,f66,f148])).
% 0.22/0.47  fof(f148,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_19),
% 0.22/0.47    inference(avatar_component_clause,[],[f147])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f69])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    v2_pre_topc(sK0) | ~spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f54])).
% 0.22/0.47  fof(f175,plain,(
% 0.22/0.47    spl2_22 | ~spl2_2 | ~spl2_3 | ~spl2_16),
% 0.22/0.47    inference(avatar_split_clause,[],[f138,f131,f64,f59,f172])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    spl2_16 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.47  fof(f138,plain,(
% 0.22/0.47    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3 | ~spl2_16)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f61,f66,f132])).
% 0.22/0.47  fof(f132,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f131])).
% 0.22/0.47  fof(f167,plain,(
% 0.22/0.47    spl2_21),
% 0.22/0.47    inference(avatar_split_clause,[],[f39,f165])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.22/0.47  fof(f155,plain,(
% 0.22/0.47    spl2_20),
% 0.22/0.47    inference(avatar_split_clause,[],[f38,f153])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.22/0.47  fof(f149,plain,(
% 0.22/0.47    spl2_19),
% 0.22/0.47    inference(avatar_split_clause,[],[f41,f147])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.47  fof(f142,plain,(
% 0.22/0.47    spl2_18),
% 0.22/0.47    inference(avatar_split_clause,[],[f52,f140])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(flattening,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    spl2_17),
% 0.22/0.47    inference(avatar_split_clause,[],[f40,f135])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    spl2_16),
% 0.22/0.47    inference(avatar_split_clause,[],[f50,f131])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    spl2_15 | ~spl2_3 | ~spl2_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f123,f120,f64,f127])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    spl2_14 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl2_3 | ~spl2_14)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f66,f121])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f120])).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    spl2_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f51,f120])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    spl2_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f49,f108])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    spl2_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f48,f104])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    spl2_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f47,f100])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    spl2_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f45,f92])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    spl2_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f43,f84])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    spl2_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f42,f80])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    ~spl2_4 | ~spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f77,f73,f69])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    ~v4_pre_topc(sK1,sK0) | ~spl2_5),
% 0.22/0.47    inference(subsumption_resolution,[],[f37,f75])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.47    inference(negated_conjecture,[],[f15])).
% 0.22/0.47  fof(f15,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    spl2_4 | spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f36,f73,f69])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f35,f64])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f34,f59])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    l1_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f33,f54])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    v2_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (13421)------------------------------
% 0.22/0.47  % (13421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (13421)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (13421)Memory used [KB]: 6524
% 0.22/0.47  % (13421)Time elapsed: 0.024 s
% 0.22/0.47  % (13421)------------------------------
% 0.22/0.47  % (13421)------------------------------
% 0.22/0.47  % (13410)Success in time 0.1 s
%------------------------------------------------------------------------------
