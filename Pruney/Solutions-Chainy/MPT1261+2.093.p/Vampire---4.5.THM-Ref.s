%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:02 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 485 expanded)
%              Number of leaves         :   61 ( 226 expanded)
%              Depth                    :   11
%              Number of atoms          :  767 (1518 expanded)
%              Number of equality atoms :  155 ( 360 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2683,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f97,f107,f111,f115,f123,f131,f139,f143,f172,f178,f184,f198,f206,f217,f231,f240,f244,f267,f291,f308,f331,f349,f363,f395,f453,f476,f494,f523,f678,f689,f731,f849,f855,f902,f907,f974,f988,f1075,f2574,f2627,f2672])).

fof(f2672,plain,
    ( ~ spl2_15
    | ~ spl2_26
    | spl2_32
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_67
    | ~ spl2_69
    | ~ spl2_75
    | ~ spl2_76
    | ~ spl2_77
    | ~ spl2_86
    | ~ spl2_136
    | ~ spl2_139 ),
    inference(avatar_contradiction_clause,[],[f2671])).

fof(f2671,plain,
    ( $false
    | ~ spl2_15
    | ~ spl2_26
    | spl2_32
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_67
    | ~ spl2_69
    | ~ spl2_75
    | ~ spl2_76
    | ~ spl2_77
    | ~ spl2_86
    | ~ spl2_136
    | ~ spl2_139 ),
    inference(subsumption_resolution,[],[f290,f2670])).

fof(f2670,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_15
    | ~ spl2_26
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_67
    | ~ spl2_69
    | ~ spl2_75
    | ~ spl2_76
    | ~ spl2_77
    | ~ spl2_86
    | ~ spl2_136
    | ~ spl2_139 ),
    inference(forward_demodulation,[],[f2669,f1148])).

fof(f1148,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_26
    | ~ spl2_67
    | ~ spl2_77
    | ~ spl2_86 ),
    inference(forward_demodulation,[],[f1135,f906])).

fof(f906,plain,
    ( sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f904])).

fof(f904,plain,
    ( spl2_77
  <=> sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f1135,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_26
    | ~ spl2_67
    | ~ spl2_86 ),
    inference(unit_resulting_resolution,[],[f686,f1074,f216])).

fof(f216,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl2_26
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f1074,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_86 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f1072,plain,
    ( spl2_86
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).

fof(f686,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f684])).

fof(f684,plain,
    ( spl2_67
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f2669,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_15
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_69
    | ~ spl2_75
    | ~ spl2_76
    | ~ spl2_136
    | ~ spl2_139 ),
    inference(forward_demodulation,[],[f2668,f680])).

fof(f680,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_44
    | ~ spl2_66 ),
    inference(unit_resulting_resolution,[],[f677,f394])).

fof(f394,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl2_44
  <=> ! [X3,X2] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f677,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f675])).

fof(f675,plain,
    ( spl2_66
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f2668,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_15
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_69
    | ~ spl2_75
    | ~ spl2_76
    | ~ spl2_136
    | ~ spl2_139 ),
    inference(forward_demodulation,[],[f2667,f735])).

fof(f735,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_15
    | ~ spl2_69 ),
    inference(superposition,[],[f142,f730])).

fof(f730,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f728])).

fof(f728,plain,
    ( spl2_69
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f142,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl2_15
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f2667,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_69
    | ~ spl2_75
    | ~ spl2_76
    | ~ spl2_136
    | ~ spl2_139 ),
    inference(forward_demodulation,[],[f2642,f2603])).

fof(f2603,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_69
    | ~ spl2_76
    | ~ spl2_136 ),
    inference(forward_demodulation,[],[f2602,f901])).

fof(f901,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f899])).

fof(f899,plain,
    ( spl2_76
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f2602,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_69
    | ~ spl2_136 ),
    inference(forward_demodulation,[],[f2589,f680])).

fof(f2589,plain,
    ( k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_69
    | ~ spl2_136 ),
    inference(superposition,[],[f2573,f730])).

fof(f2573,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ spl2_136 ),
    inference(avatar_component_clause,[],[f2572])).

fof(f2572,plain,
    ( spl2_136
  <=> ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).

fof(f2642,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_75
    | ~ spl2_139 ),
    inference(superposition,[],[f2626,f848])).

fof(f848,plain,
    ( k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f846])).

fof(f846,plain,
    ( spl2_75
  <=> k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f2626,plain,
    ( ! [X8,X9] : k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = k2_xboole_0(X8,k3_xboole_0(X8,X9))
    | ~ spl2_139 ),
    inference(avatar_component_clause,[],[f2625])).

fof(f2625,plain,
    ( spl2_139
  <=> ! [X9,X8] : k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = k2_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).

fof(f290,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_32 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl2_32
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f2627,plain,
    ( spl2_139
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f490,f474,f137,f109,f2625])).

fof(f109,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f137,plain,
    ( spl2_14
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f474,plain,
    ( spl2_50
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f490,plain,
    ( ! [X8,X9] : k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = k2_xboole_0(X8,k3_xboole_0(X8,X9))
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_50 ),
    inference(forward_demodulation,[],[f487,f110])).

fof(f110,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f487,plain,
    ( ! [X8,X9] : k2_xboole_0(k3_xboole_0(X8,X9),X8) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9))
    | ~ spl2_14
    | ~ spl2_50 ),
    inference(superposition,[],[f138,f475])).

fof(f475,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f474])).

fof(f138,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f2574,plain,
    ( spl2_136
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_50
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f541,f521,f474,f137,f109,f2572])).

fof(f521,plain,
    ( spl2_54
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f541,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_50
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f533,f490])).

fof(f533,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3))
    | ~ spl2_8
    | ~ spl2_54 ),
    inference(superposition,[],[f522,f110])).

fof(f522,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f521])).

fof(f1075,plain,
    ( spl2_86
    | ~ spl2_42
    | ~ spl2_69 ),
    inference(avatar_split_clause,[],[f736,f728,f361,f1072])).

fof(f361,plain,
    ( spl2_42
  <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f736,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_42
    | ~ spl2_69 ),
    inference(superposition,[],[f362,f730])).

fof(f362,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f361])).

fof(f988,plain,
    ( ~ spl2_2
    | spl2_66
    | ~ spl2_4
    | ~ spl2_3
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f226,f204,f85,f90,f675,f80])).

fof(f80,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f90,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f85,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f204,plain,
    ( spl2_24
  <=> ! [X1,X0] :
        ( r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f226,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_24 ),
    inference(resolution,[],[f205,f87])).

fof(f87,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f204])).

fof(f974,plain,
    ( ~ spl2_4
    | ~ spl2_15
    | ~ spl2_35
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_69 ),
    inference(avatar_split_clause,[],[f851,f728,f675,f393,f306,f141,f90])).

fof(f306,plain,
    ( spl2_35
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f851,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_15
    | ~ spl2_35
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f850,f743])).

fof(f743,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_15
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f735,f680])).

fof(f850,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f50,f307])).

fof(f307,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f306])).

fof(f50,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f907,plain,
    ( spl2_77
    | ~ spl2_40
    | ~ spl2_42
    | ~ spl2_51
    | ~ spl2_69 ),
    inference(avatar_split_clause,[],[f744,f728,f492,f361,f346,f904])).

fof(f346,plain,
    ( spl2_40
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f492,plain,
    ( spl2_51
  <=> ! [X1,X0] :
        ( k4_subset_1(X0,X1,k4_xboole_0(X0,X1)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f744,plain,
    ( sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_40
    | ~ spl2_42
    | ~ spl2_51
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f666,f736])).

fof(f666,plain,
    ( sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_40
    | ~ spl2_51 ),
    inference(superposition,[],[f493,f348])).

fof(f348,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f346])).

fof(f493,plain,
    ( ! [X0,X1] :
        ( k4_subset_1(X0,X1,k4_xboole_0(X0,X1)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f492])).

fof(f902,plain,
    ( spl2_76
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26
    | ~ spl2_29
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f283,f264,f242,f215,f85,f80,f899])).

fof(f242,plain,
    ( spl2_29
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f264,plain,
    ( spl2_31
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f283,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26
    | ~ spl2_29
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f278,f252])).

fof(f252,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_29 ),
    inference(unit_resulting_resolution,[],[f82,f87,f243])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f242])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f278,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_26
    | ~ spl2_31 ),
    inference(unit_resulting_resolution,[],[f87,f266,f216])).

fof(f266,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f264])).

fof(f855,plain,
    ( ~ spl2_15
    | spl2_40
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_69 ),
    inference(avatar_contradiction_clause,[],[f854])).

fof(f854,plain,
    ( $false
    | ~ spl2_15
    | spl2_40
    | ~ spl2_44
    | ~ spl2_66
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f743,f347])).

fof(f347,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | spl2_40 ),
    inference(avatar_component_clause,[],[f346])).

fof(f849,plain,
    ( spl2_75
    | ~ spl2_15
    | ~ spl2_35
    | ~ spl2_38
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f670,f346,f328,f306,f141,f846])).

fof(f328,plain,
    ( spl2_38
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f670,plain,
    ( k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_15
    | ~ spl2_35
    | ~ spl2_38
    | ~ spl2_40 ),
    inference(forward_demodulation,[],[f662,f334])).

fof(f334,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_35
    | ~ spl2_38 ),
    inference(superposition,[],[f330,f307])).

fof(f330,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f328])).

fof(f662,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_15
    | ~ spl2_40 ),
    inference(superposition,[],[f142,f348])).

fof(f731,plain,
    ( spl2_69
    | ~ spl2_35
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f334,f328,f306,f728])).

fof(f689,plain,
    ( ~ spl2_11
    | ~ spl2_66
    | spl2_67 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | ~ spl2_11
    | ~ spl2_66
    | spl2_67 ),
    inference(subsumption_resolution,[],[f682,f685])).

fof(f685,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_67 ),
    inference(avatar_component_clause,[],[f684])).

fof(f682,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_11
    | ~ spl2_66 ),
    inference(unit_resulting_resolution,[],[f677,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f678,plain,
    ( spl2_66
    | ~ spl2_7
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f660,f346,f105,f675])).

fof(f105,plain,
    ( spl2_7
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f660,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_7
    | ~ spl2_40 ),
    inference(superposition,[],[f106,f348])).

fof(f106,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f523,plain,
    ( spl2_54
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f165,f141,f137,f109,f521])).

fof(f165,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f163,f110])).

fof(f163,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(superposition,[],[f138,f142])).

fof(f494,plain,
    ( spl2_51
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f193,f182,f170,f492])).

fof(f170,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f182,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( k4_subset_1(X0,X1,k4_xboole_0(X0,X1)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( k4_subset_1(X0,X1,k4_xboole_0(X0,X1)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(superposition,[],[f183,f171])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f476,plain,
    ( spl2_50
    | ~ spl2_7
    | ~ spl2_44
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f454,f451,f393,f105,f474])).

fof(f451,plain,
    ( spl2_48
  <=> ! [X1,X0] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f454,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_7
    | ~ spl2_44
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f452,f397])).

fof(f397,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_7
    | ~ spl2_44 ),
    inference(unit_resulting_resolution,[],[f106,f394])).

fof(f452,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f451])).

fof(f453,plain,
    ( spl2_48
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f162,f141,f451])).

fof(f162,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_15 ),
    inference(superposition,[],[f142,f142])).

fof(f395,plain,
    ( spl2_44
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f154,f129,f113,f393])).

fof(f113,plain,
    ( spl2_9
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f129,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f154,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(superposition,[],[f130,f114])).

fof(f114,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f363,plain,
    ( spl2_42
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f134,f121,f105,f361])).

fof(f134,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f106,f122])).

fof(f349,plain,
    ( ~ spl2_3
    | spl2_40
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f189,f176,f94,f346,f85])).

fof(f94,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f176,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f189,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(superposition,[],[f177,f96])).

fof(f96,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f176])).

fof(f331,plain,
    ( spl2_38
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f247,f238,f85,f80,f328])).

fof(f238,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f247,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f82,f87,f239])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f238])).

fof(f308,plain,
    ( spl2_35
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f188,f176,f85,f306])).

fof(f188,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f87,f177])).

fof(f291,plain,
    ( ~ spl2_32
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f245,f229,f90,f85,f80,f75,f288])).

fof(f75,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f229,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f245,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_27 ),
    inference(unit_resulting_resolution,[],[f82,f77,f91,f87,f230])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f229])).

fof(f91,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f77,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f267,plain,
    ( spl2_31
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f207,f196,f85,f80,f264])).

fof(f196,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f207,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f82,f87,f197])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f196])).

fof(f244,plain,(
    spl2_29 ),
    inference(avatar_split_clause,[],[f53,f242])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f240,plain,(
    spl2_28 ),
    inference(avatar_split_clause,[],[f52,f238])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f231,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f55,f229])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f217,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f72,f215])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f206,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f56,f204])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f198,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f68,f196])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f184,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f73,f182])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f67,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f178,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f71,f176])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f172,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f66,f170])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f143,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f62,f141])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f139,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f61,f137])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f131,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f64,f129])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f123,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f70,f121])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f115,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f59,f113])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f111,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f58,f109])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f107,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f97,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f49,f94,f90])).

fof(f49,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f48,f85])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f47,f80])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f46,f75])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:26:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (32658)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (32662)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (32653)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (32663)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (32659)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (32654)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (32648)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (32650)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (32649)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (32661)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (32655)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (32652)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (32660)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (32656)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (32657)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (32664)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (32651)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (32665)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.49/0.55  % (32653)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.57  % SZS output start Proof for theBenchmark
% 1.49/0.57  fof(f2683,plain,(
% 1.49/0.57    $false),
% 1.49/0.57    inference(avatar_sat_refutation,[],[f78,f83,f88,f97,f107,f111,f115,f123,f131,f139,f143,f172,f178,f184,f198,f206,f217,f231,f240,f244,f267,f291,f308,f331,f349,f363,f395,f453,f476,f494,f523,f678,f689,f731,f849,f855,f902,f907,f974,f988,f1075,f2574,f2627,f2672])).
% 1.49/0.57  fof(f2672,plain,(
% 1.49/0.57    ~spl2_15 | ~spl2_26 | spl2_32 | ~spl2_44 | ~spl2_66 | ~spl2_67 | ~spl2_69 | ~spl2_75 | ~spl2_76 | ~spl2_77 | ~spl2_86 | ~spl2_136 | ~spl2_139),
% 1.49/0.57    inference(avatar_contradiction_clause,[],[f2671])).
% 1.49/0.57  fof(f2671,plain,(
% 1.49/0.57    $false | (~spl2_15 | ~spl2_26 | spl2_32 | ~spl2_44 | ~spl2_66 | ~spl2_67 | ~spl2_69 | ~spl2_75 | ~spl2_76 | ~spl2_77 | ~spl2_86 | ~spl2_136 | ~spl2_139)),
% 1.49/0.57    inference(subsumption_resolution,[],[f290,f2670])).
% 1.49/0.57  fof(f2670,plain,(
% 1.49/0.57    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_15 | ~spl2_26 | ~spl2_44 | ~spl2_66 | ~spl2_67 | ~spl2_69 | ~spl2_75 | ~spl2_76 | ~spl2_77 | ~spl2_86 | ~spl2_136 | ~spl2_139)),
% 1.49/0.57    inference(forward_demodulation,[],[f2669,f1148])).
% 1.49/0.57  fof(f1148,plain,(
% 1.49/0.57    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_26 | ~spl2_67 | ~spl2_77 | ~spl2_86)),
% 1.49/0.57    inference(forward_demodulation,[],[f1135,f906])).
% 1.49/0.57  fof(f906,plain,(
% 1.49/0.57    sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_77),
% 1.49/0.57    inference(avatar_component_clause,[],[f904])).
% 1.49/0.57  fof(f904,plain,(
% 1.49/0.57    spl2_77 <=> sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 1.49/0.57  fof(f1135,plain,(
% 1.49/0.57    k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_26 | ~spl2_67 | ~spl2_86)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f686,f1074,f216])).
% 1.49/0.57  fof(f216,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_26),
% 1.49/0.57    inference(avatar_component_clause,[],[f215])).
% 1.49/0.57  fof(f215,plain,(
% 1.49/0.57    spl2_26 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.49/0.57  fof(f1074,plain,(
% 1.49/0.57    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_86),
% 1.49/0.57    inference(avatar_component_clause,[],[f1072])).
% 1.49/0.57  fof(f1072,plain,(
% 1.49/0.57    spl2_86 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).
% 1.49/0.57  fof(f686,plain,(
% 1.49/0.57    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_67),
% 1.49/0.57    inference(avatar_component_clause,[],[f684])).
% 1.49/0.57  fof(f684,plain,(
% 1.49/0.57    spl2_67 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 1.49/0.57  fof(f2669,plain,(
% 1.49/0.57    k2_pre_topc(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_15 | ~spl2_44 | ~spl2_66 | ~spl2_69 | ~spl2_75 | ~spl2_76 | ~spl2_136 | ~spl2_139)),
% 1.49/0.57    inference(forward_demodulation,[],[f2668,f680])).
% 1.49/0.57  fof(f680,plain,(
% 1.49/0.57    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_44 | ~spl2_66)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f677,f394])).
% 1.49/0.57  fof(f394,plain,(
% 1.49/0.57    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | ~spl2_44),
% 1.49/0.57    inference(avatar_component_clause,[],[f393])).
% 1.49/0.57  fof(f393,plain,(
% 1.49/0.57    spl2_44 <=> ! [X3,X2] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 1.49/0.57  fof(f677,plain,(
% 1.49/0.57    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_66),
% 1.49/0.57    inference(avatar_component_clause,[],[f675])).
% 1.49/0.57  fof(f675,plain,(
% 1.49/0.57    spl2_66 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 1.49/0.57  fof(f2668,plain,(
% 1.49/0.57    k2_pre_topc(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_15 | ~spl2_44 | ~spl2_66 | ~spl2_69 | ~spl2_75 | ~spl2_76 | ~spl2_136 | ~spl2_139)),
% 1.49/0.57    inference(forward_demodulation,[],[f2667,f735])).
% 1.49/0.57  fof(f735,plain,(
% 1.49/0.57    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_15 | ~spl2_69)),
% 1.49/0.57    inference(superposition,[],[f142,f730])).
% 1.49/0.57  fof(f730,plain,(
% 1.49/0.57    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_69),
% 1.49/0.57    inference(avatar_component_clause,[],[f728])).
% 1.49/0.57  fof(f728,plain,(
% 1.49/0.57    spl2_69 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 1.49/0.57  fof(f142,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_15),
% 1.49/0.57    inference(avatar_component_clause,[],[f141])).
% 1.49/0.57  fof(f141,plain,(
% 1.49/0.57    spl2_15 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.49/0.57  fof(f2667,plain,(
% 1.49/0.57    k2_pre_topc(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) | (~spl2_44 | ~spl2_66 | ~spl2_69 | ~spl2_75 | ~spl2_76 | ~spl2_136 | ~spl2_139)),
% 1.49/0.57    inference(forward_demodulation,[],[f2642,f2603])).
% 1.49/0.57  fof(f2603,plain,(
% 1.49/0.57    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_44 | ~spl2_66 | ~spl2_69 | ~spl2_76 | ~spl2_136)),
% 1.49/0.57    inference(forward_demodulation,[],[f2602,f901])).
% 1.49/0.57  fof(f901,plain,(
% 1.49/0.57    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_76),
% 1.49/0.57    inference(avatar_component_clause,[],[f899])).
% 1.49/0.57  fof(f899,plain,(
% 1.49/0.57    spl2_76 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 1.49/0.57  fof(f2602,plain,(
% 1.49/0.57    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_44 | ~spl2_66 | ~spl2_69 | ~spl2_136)),
% 1.49/0.57    inference(forward_demodulation,[],[f2589,f680])).
% 1.49/0.57  fof(f2589,plain,(
% 1.49/0.57    k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_69 | ~spl2_136)),
% 1.49/0.57    inference(superposition,[],[f2573,f730])).
% 1.49/0.57  fof(f2573,plain,(
% 1.49/0.57    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X2,X3))) ) | ~spl2_136),
% 1.49/0.57    inference(avatar_component_clause,[],[f2572])).
% 1.49/0.57  fof(f2572,plain,(
% 1.49/0.57    spl2_136 <=> ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X2,X3))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).
% 1.49/0.57  fof(f2642,plain,(
% 1.49/0.57    k2_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_75 | ~spl2_139)),
% 1.49/0.57    inference(superposition,[],[f2626,f848])).
% 1.49/0.57  fof(f848,plain,(
% 1.49/0.57    k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_75),
% 1.49/0.57    inference(avatar_component_clause,[],[f846])).
% 1.49/0.57  fof(f846,plain,(
% 1.49/0.57    spl2_75 <=> k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 1.49/0.57  fof(f2626,plain,(
% 1.49/0.57    ( ! [X8,X9] : (k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = k2_xboole_0(X8,k3_xboole_0(X8,X9))) ) | ~spl2_139),
% 1.49/0.57    inference(avatar_component_clause,[],[f2625])).
% 1.49/0.57  fof(f2625,plain,(
% 1.49/0.57    spl2_139 <=> ! [X9,X8] : k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = k2_xboole_0(X8,k3_xboole_0(X8,X9))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).
% 1.49/0.57  fof(f290,plain,(
% 1.49/0.57    sK1 != k2_pre_topc(sK0,sK1) | spl2_32),
% 1.49/0.57    inference(avatar_component_clause,[],[f288])).
% 1.49/0.57  fof(f288,plain,(
% 1.49/0.57    spl2_32 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 1.49/0.57  fof(f2627,plain,(
% 1.49/0.57    spl2_139 | ~spl2_8 | ~spl2_14 | ~spl2_50),
% 1.49/0.57    inference(avatar_split_clause,[],[f490,f474,f137,f109,f2625])).
% 1.49/0.57  fof(f109,plain,(
% 1.49/0.57    spl2_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.49/0.57  fof(f137,plain,(
% 1.49/0.57    spl2_14 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.49/0.57  fof(f474,plain,(
% 1.49/0.57    spl2_50 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 1.49/0.57  fof(f490,plain,(
% 1.49/0.57    ( ! [X8,X9] : (k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = k2_xboole_0(X8,k3_xboole_0(X8,X9))) ) | (~spl2_8 | ~spl2_14 | ~spl2_50)),
% 1.49/0.57    inference(forward_demodulation,[],[f487,f110])).
% 1.49/0.57  fof(f110,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_8),
% 1.49/0.57    inference(avatar_component_clause,[],[f109])).
% 1.49/0.57  fof(f487,plain,(
% 1.49/0.57    ( ! [X8,X9] : (k2_xboole_0(k3_xboole_0(X8,X9),X8) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9))) ) | (~spl2_14 | ~spl2_50)),
% 1.49/0.57    inference(superposition,[],[f138,f475])).
% 1.49/0.57  fof(f475,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_50),
% 1.49/0.57    inference(avatar_component_clause,[],[f474])).
% 1.49/0.57  fof(f138,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_14),
% 1.49/0.57    inference(avatar_component_clause,[],[f137])).
% 1.49/0.57  fof(f2574,plain,(
% 1.49/0.57    spl2_136 | ~spl2_8 | ~spl2_14 | ~spl2_50 | ~spl2_54),
% 1.49/0.57    inference(avatar_split_clause,[],[f541,f521,f474,f137,f109,f2572])).
% 1.49/0.57  fof(f521,plain,(
% 1.49/0.57    spl2_54 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 1.49/0.57  fof(f541,plain,(
% 1.49/0.57    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X2,X3))) ) | (~spl2_8 | ~spl2_14 | ~spl2_50 | ~spl2_54)),
% 1.49/0.57    inference(forward_demodulation,[],[f533,f490])).
% 1.49/0.57  fof(f533,plain,(
% 1.49/0.57    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3))) ) | (~spl2_8 | ~spl2_54)),
% 1.49/0.57    inference(superposition,[],[f522,f110])).
% 1.49/0.57  fof(f522,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_54),
% 1.49/0.57    inference(avatar_component_clause,[],[f521])).
% 1.49/0.57  fof(f1075,plain,(
% 1.49/0.57    spl2_86 | ~spl2_42 | ~spl2_69),
% 1.49/0.57    inference(avatar_split_clause,[],[f736,f728,f361,f1072])).
% 1.49/0.57  fof(f361,plain,(
% 1.49/0.57    spl2_42 <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 1.49/0.57  fof(f736,plain,(
% 1.49/0.57    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_42 | ~spl2_69)),
% 1.49/0.57    inference(superposition,[],[f362,f730])).
% 1.49/0.57  fof(f362,plain,(
% 1.49/0.57    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_42),
% 1.49/0.57    inference(avatar_component_clause,[],[f361])).
% 1.49/0.57  fof(f988,plain,(
% 1.49/0.57    ~spl2_2 | spl2_66 | ~spl2_4 | ~spl2_3 | ~spl2_24),
% 1.49/0.57    inference(avatar_split_clause,[],[f226,f204,f85,f90,f675,f80])).
% 1.49/0.57  fof(f80,plain,(
% 1.49/0.57    spl2_2 <=> l1_pre_topc(sK0)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.49/0.57  fof(f90,plain,(
% 1.49/0.57    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.49/0.57  fof(f85,plain,(
% 1.49/0.57    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.49/0.57  fof(f204,plain,(
% 1.49/0.57    spl2_24 <=> ! [X1,X0] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.49/0.57  fof(f226,plain,(
% 1.49/0.57    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_24)),
% 1.49/0.57    inference(resolution,[],[f205,f87])).
% 1.49/0.57  fof(f87,plain,(
% 1.49/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.49/0.57    inference(avatar_component_clause,[],[f85])).
% 1.49/0.57  fof(f205,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl2_24),
% 1.49/0.57    inference(avatar_component_clause,[],[f204])).
% 1.49/0.57  fof(f974,plain,(
% 1.49/0.57    ~spl2_4 | ~spl2_15 | ~spl2_35 | ~spl2_44 | ~spl2_66 | ~spl2_69),
% 1.49/0.57    inference(avatar_split_clause,[],[f851,f728,f675,f393,f306,f141,f90])).
% 1.49/0.57  fof(f306,plain,(
% 1.49/0.57    spl2_35 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 1.49/0.57  fof(f851,plain,(
% 1.49/0.57    ~v4_pre_topc(sK1,sK0) | (~spl2_15 | ~spl2_35 | ~spl2_44 | ~spl2_66 | ~spl2_69)),
% 1.49/0.57    inference(subsumption_resolution,[],[f850,f743])).
% 1.49/0.57  fof(f743,plain,(
% 1.49/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_15 | ~spl2_44 | ~spl2_66 | ~spl2_69)),
% 1.49/0.57    inference(forward_demodulation,[],[f735,f680])).
% 1.49/0.57  fof(f850,plain,(
% 1.49/0.57    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_35),
% 1.49/0.57    inference(forward_demodulation,[],[f50,f307])).
% 1.49/0.57  fof(f307,plain,(
% 1.49/0.57    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl2_35),
% 1.49/0.57    inference(avatar_component_clause,[],[f306])).
% 1.49/0.57  fof(f50,plain,(
% 1.49/0.57    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.49/0.57    inference(cnf_transformation,[],[f44])).
% 1.49/0.57  fof(f44,plain,(
% 1.49/0.57    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 1.49/0.57  fof(f42,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f43,plain,(
% 1.49/0.57    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f41,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.49/0.57    inference(flattening,[],[f40])).
% 1.49/0.57  fof(f40,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.49/0.57    inference(nnf_transformation,[],[f24])).
% 1.49/0.57  fof(f24,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.49/0.57    inference(flattening,[],[f23])).
% 1.49/0.57  fof(f23,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f22])).
% 1.49/0.57  fof(f22,negated_conjecture,(
% 1.49/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.49/0.57    inference(negated_conjecture,[],[f21])).
% 1.49/0.57  fof(f21,conjecture,(
% 1.49/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 1.49/0.57  fof(f907,plain,(
% 1.49/0.57    spl2_77 | ~spl2_40 | ~spl2_42 | ~spl2_51 | ~spl2_69),
% 1.49/0.57    inference(avatar_split_clause,[],[f744,f728,f492,f361,f346,f904])).
% 1.49/0.57  fof(f346,plain,(
% 1.49/0.57    spl2_40 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 1.49/0.57  fof(f492,plain,(
% 1.49/0.57    spl2_51 <=> ! [X1,X0] : (k4_subset_1(X0,X1,k4_xboole_0(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 1.49/0.57  fof(f744,plain,(
% 1.49/0.57    sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_40 | ~spl2_42 | ~spl2_51 | ~spl2_69)),
% 1.49/0.57    inference(subsumption_resolution,[],[f666,f736])).
% 1.49/0.57  fof(f666,plain,(
% 1.49/0.57    sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_40 | ~spl2_51)),
% 1.49/0.57    inference(superposition,[],[f493,f348])).
% 1.49/0.57  fof(f348,plain,(
% 1.49/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_40),
% 1.49/0.57    inference(avatar_component_clause,[],[f346])).
% 1.49/0.57  fof(f493,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_subset_1(X0,X1,k4_xboole_0(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_51),
% 1.49/0.57    inference(avatar_component_clause,[],[f492])).
% 1.49/0.57  fof(f902,plain,(
% 1.49/0.57    spl2_76 | ~spl2_2 | ~spl2_3 | ~spl2_26 | ~spl2_29 | ~spl2_31),
% 1.49/0.57    inference(avatar_split_clause,[],[f283,f264,f242,f215,f85,f80,f899])).
% 1.49/0.57  fof(f242,plain,(
% 1.49/0.57    spl2_29 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 1.49/0.57  fof(f264,plain,(
% 1.49/0.57    spl2_31 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.49/0.57  fof(f283,plain,(
% 1.49/0.57    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_26 | ~spl2_29 | ~spl2_31)),
% 1.49/0.57    inference(forward_demodulation,[],[f278,f252])).
% 1.49/0.57  fof(f252,plain,(
% 1.49/0.57    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_29)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f82,f87,f243])).
% 1.49/0.57  fof(f243,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_29),
% 1.49/0.57    inference(avatar_component_clause,[],[f242])).
% 1.49/0.57  fof(f82,plain,(
% 1.49/0.57    l1_pre_topc(sK0) | ~spl2_2),
% 1.49/0.57    inference(avatar_component_clause,[],[f80])).
% 1.49/0.57  fof(f278,plain,(
% 1.49/0.57    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_26 | ~spl2_31)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f87,f266,f216])).
% 1.49/0.57  fof(f266,plain,(
% 1.49/0.57    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_31),
% 1.49/0.57    inference(avatar_component_clause,[],[f264])).
% 1.49/0.57  fof(f855,plain,(
% 1.49/0.57    ~spl2_15 | spl2_40 | ~spl2_44 | ~spl2_66 | ~spl2_69),
% 1.49/0.57    inference(avatar_contradiction_clause,[],[f854])).
% 1.49/0.57  fof(f854,plain,(
% 1.49/0.57    $false | (~spl2_15 | spl2_40 | ~spl2_44 | ~spl2_66 | ~spl2_69)),
% 1.49/0.57    inference(subsumption_resolution,[],[f743,f347])).
% 1.49/0.57  fof(f347,plain,(
% 1.49/0.57    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | spl2_40),
% 1.49/0.57    inference(avatar_component_clause,[],[f346])).
% 1.49/0.57  fof(f849,plain,(
% 1.49/0.57    spl2_75 | ~spl2_15 | ~spl2_35 | ~spl2_38 | ~spl2_40),
% 1.49/0.57    inference(avatar_split_clause,[],[f670,f346,f328,f306,f141,f846])).
% 1.49/0.57  fof(f328,plain,(
% 1.49/0.57    spl2_38 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 1.49/0.57  fof(f670,plain,(
% 1.49/0.57    k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_15 | ~spl2_35 | ~spl2_38 | ~spl2_40)),
% 1.49/0.57    inference(forward_demodulation,[],[f662,f334])).
% 1.49/0.57  fof(f334,plain,(
% 1.49/0.57    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_35 | ~spl2_38)),
% 1.49/0.57    inference(superposition,[],[f330,f307])).
% 1.49/0.57  fof(f330,plain,(
% 1.49/0.57    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_38),
% 1.49/0.57    inference(avatar_component_clause,[],[f328])).
% 1.49/0.57  fof(f662,plain,(
% 1.49/0.57    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_15 | ~spl2_40)),
% 1.49/0.57    inference(superposition,[],[f142,f348])).
% 1.49/0.57  fof(f731,plain,(
% 1.49/0.57    spl2_69 | ~spl2_35 | ~spl2_38),
% 1.49/0.57    inference(avatar_split_clause,[],[f334,f328,f306,f728])).
% 1.49/0.57  fof(f689,plain,(
% 1.49/0.57    ~spl2_11 | ~spl2_66 | spl2_67),
% 1.49/0.57    inference(avatar_contradiction_clause,[],[f688])).
% 1.49/0.57  fof(f688,plain,(
% 1.49/0.57    $false | (~spl2_11 | ~spl2_66 | spl2_67)),
% 1.49/0.57    inference(subsumption_resolution,[],[f682,f685])).
% 1.49/0.57  fof(f685,plain,(
% 1.49/0.57    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_67),
% 1.49/0.57    inference(avatar_component_clause,[],[f684])).
% 1.49/0.57  fof(f682,plain,(
% 1.49/0.57    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_11 | ~spl2_66)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f677,f122])).
% 1.49/0.57  fof(f122,plain,(
% 1.49/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_11),
% 1.49/0.57    inference(avatar_component_clause,[],[f121])).
% 1.49/0.57  fof(f121,plain,(
% 1.49/0.57    spl2_11 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.49/0.57  fof(f678,plain,(
% 1.49/0.57    spl2_66 | ~spl2_7 | ~spl2_40),
% 1.49/0.57    inference(avatar_split_clause,[],[f660,f346,f105,f675])).
% 1.49/0.57  fof(f105,plain,(
% 1.49/0.57    spl2_7 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.49/0.57  fof(f660,plain,(
% 1.49/0.57    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_7 | ~spl2_40)),
% 1.49/0.57    inference(superposition,[],[f106,f348])).
% 1.49/0.57  fof(f106,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_7),
% 1.49/0.57    inference(avatar_component_clause,[],[f105])).
% 1.49/0.57  fof(f523,plain,(
% 1.49/0.57    spl2_54 | ~spl2_8 | ~spl2_14 | ~spl2_15),
% 1.49/0.57    inference(avatar_split_clause,[],[f165,f141,f137,f109,f521])).
% 1.49/0.57  fof(f165,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) ) | (~spl2_8 | ~spl2_14 | ~spl2_15)),
% 1.49/0.57    inference(forward_demodulation,[],[f163,f110])).
% 1.49/0.57  fof(f163,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | (~spl2_14 | ~spl2_15)),
% 1.49/0.57    inference(superposition,[],[f138,f142])).
% 1.49/0.57  fof(f494,plain,(
% 1.49/0.57    spl2_51 | ~spl2_19 | ~spl2_21),
% 1.49/0.57    inference(avatar_split_clause,[],[f193,f182,f170,f492])).
% 1.49/0.57  fof(f170,plain,(
% 1.49/0.57    spl2_19 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.49/0.57  fof(f182,plain,(
% 1.49/0.57    spl2_21 <=> ! [X1,X0] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.49/0.57  fof(f193,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_subset_1(X0,X1,k4_xboole_0(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_19 | ~spl2_21)),
% 1.49/0.57    inference(duplicate_literal_removal,[],[f192])).
% 1.49/0.57  fof(f192,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_subset_1(X0,X1,k4_xboole_0(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_19 | ~spl2_21)),
% 1.49/0.57    inference(superposition,[],[f183,f171])).
% 1.49/0.57  fof(f171,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_19),
% 1.49/0.57    inference(avatar_component_clause,[],[f170])).
% 1.49/0.57  fof(f183,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_21),
% 1.49/0.57    inference(avatar_component_clause,[],[f182])).
% 1.49/0.57  fof(f476,plain,(
% 1.49/0.57    spl2_50 | ~spl2_7 | ~spl2_44 | ~spl2_48),
% 1.49/0.57    inference(avatar_split_clause,[],[f454,f451,f393,f105,f474])).
% 1.49/0.57  fof(f451,plain,(
% 1.49/0.57    spl2_48 <=> ! [X1,X0] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 1.49/0.57  fof(f454,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | (~spl2_7 | ~spl2_44 | ~spl2_48)),
% 1.49/0.57    inference(forward_demodulation,[],[f452,f397])).
% 1.49/0.57  fof(f397,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) ) | (~spl2_7 | ~spl2_44)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f106,f394])).
% 1.49/0.57  fof(f452,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_48),
% 1.49/0.57    inference(avatar_component_clause,[],[f451])).
% 1.49/0.57  fof(f453,plain,(
% 1.49/0.57    spl2_48 | ~spl2_15),
% 1.49/0.57    inference(avatar_split_clause,[],[f162,f141,f451])).
% 1.49/0.57  fof(f162,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_15),
% 1.49/0.57    inference(superposition,[],[f142,f142])).
% 1.49/0.57  fof(f395,plain,(
% 1.49/0.57    spl2_44 | ~spl2_9 | ~spl2_13),
% 1.49/0.57    inference(avatar_split_clause,[],[f154,f129,f113,f393])).
% 1.49/0.57  fof(f113,plain,(
% 1.49/0.57    spl2_9 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.49/0.57  fof(f129,plain,(
% 1.49/0.57    spl2_13 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.49/0.57  fof(f154,plain,(
% 1.49/0.57    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | (~spl2_9 | ~spl2_13)),
% 1.49/0.57    inference(superposition,[],[f130,f114])).
% 1.49/0.57  fof(f114,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_9),
% 1.49/0.57    inference(avatar_component_clause,[],[f113])).
% 1.49/0.57  fof(f130,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 1.49/0.57    inference(avatar_component_clause,[],[f129])).
% 1.49/0.57  fof(f363,plain,(
% 1.49/0.57    spl2_42 | ~spl2_7 | ~spl2_11),
% 1.49/0.57    inference(avatar_split_clause,[],[f134,f121,f105,f361])).
% 1.49/0.57  fof(f134,plain,(
% 1.49/0.57    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl2_7 | ~spl2_11)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f106,f122])).
% 1.49/0.57  fof(f349,plain,(
% 1.49/0.57    ~spl2_3 | spl2_40 | ~spl2_5 | ~spl2_20),
% 1.49/0.57    inference(avatar_split_clause,[],[f189,f176,f94,f346,f85])).
% 1.49/0.57  fof(f94,plain,(
% 1.49/0.57    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.49/0.57  fof(f176,plain,(
% 1.49/0.57    spl2_20 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.49/0.57  fof(f189,plain,(
% 1.49/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | ~spl2_20)),
% 1.49/0.57    inference(superposition,[],[f177,f96])).
% 1.49/0.57  fof(f96,plain,(
% 1.49/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 1.49/0.57    inference(avatar_component_clause,[],[f94])).
% 1.49/0.57  fof(f177,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_20),
% 1.49/0.57    inference(avatar_component_clause,[],[f176])).
% 1.49/0.57  fof(f331,plain,(
% 1.49/0.57    spl2_38 | ~spl2_2 | ~spl2_3 | ~spl2_28),
% 1.49/0.57    inference(avatar_split_clause,[],[f247,f238,f85,f80,f328])).
% 1.49/0.57  fof(f238,plain,(
% 1.49/0.57    spl2_28 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 1.49/0.57  fof(f247,plain,(
% 1.49/0.57    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_28)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f82,f87,f239])).
% 1.49/0.57  fof(f239,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_28),
% 1.49/0.57    inference(avatar_component_clause,[],[f238])).
% 1.49/0.57  fof(f308,plain,(
% 1.49/0.57    spl2_35 | ~spl2_3 | ~spl2_20),
% 1.49/0.57    inference(avatar_split_clause,[],[f188,f176,f85,f306])).
% 1.49/0.57  fof(f188,plain,(
% 1.49/0.57    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl2_3 | ~spl2_20)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f87,f177])).
% 1.49/0.57  fof(f291,plain,(
% 1.49/0.57    ~spl2_32 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_27),
% 1.49/0.57    inference(avatar_split_clause,[],[f245,f229,f90,f85,f80,f75,f288])).
% 1.49/0.57  fof(f75,plain,(
% 1.49/0.57    spl2_1 <=> v2_pre_topc(sK0)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.49/0.57  fof(f229,plain,(
% 1.49/0.57    spl2_27 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 1.49/0.57  fof(f245,plain,(
% 1.49/0.57    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_27)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f82,f77,f91,f87,f230])).
% 1.49/0.57  fof(f230,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_27),
% 1.49/0.57    inference(avatar_component_clause,[],[f229])).
% 1.49/0.57  fof(f91,plain,(
% 1.49/0.57    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 1.49/0.57    inference(avatar_component_clause,[],[f90])).
% 1.49/0.57  fof(f77,plain,(
% 1.49/0.57    v2_pre_topc(sK0) | ~spl2_1),
% 1.49/0.57    inference(avatar_component_clause,[],[f75])).
% 1.49/0.57  fof(f267,plain,(
% 1.49/0.57    spl2_31 | ~spl2_2 | ~spl2_3 | ~spl2_22),
% 1.49/0.57    inference(avatar_split_clause,[],[f207,f196,f85,f80,f264])).
% 1.49/0.57  fof(f196,plain,(
% 1.49/0.57    spl2_22 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.49/0.57  fof(f207,plain,(
% 1.49/0.57    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3 | ~spl2_22)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f82,f87,f197])).
% 1.49/0.57  fof(f197,plain,(
% 1.49/0.57    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_22),
% 1.49/0.57    inference(avatar_component_clause,[],[f196])).
% 1.49/0.57  fof(f244,plain,(
% 1.49/0.57    spl2_29),
% 1.49/0.57    inference(avatar_split_clause,[],[f53,f242])).
% 1.49/0.57  fof(f53,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f26])).
% 1.49/0.57  fof(f26,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f18])).
% 1.49/0.57  fof(f18,axiom,(
% 1.49/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 1.49/0.57  fof(f240,plain,(
% 1.49/0.57    spl2_28),
% 1.49/0.57    inference(avatar_split_clause,[],[f52,f238])).
% 1.49/0.57  fof(f52,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f25])).
% 1.49/0.57  fof(f25,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f20])).
% 1.49/0.57  fof(f20,axiom,(
% 1.49/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 1.49/0.57  fof(f231,plain,(
% 1.49/0.57    spl2_27),
% 1.49/0.57    inference(avatar_split_clause,[],[f55,f229])).
% 1.49/0.57  fof(f55,plain,(
% 1.49/0.57    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f28])).
% 1.49/0.57  fof(f28,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.57    inference(flattening,[],[f27])).
% 1.49/0.57  fof(f27,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f16])).
% 1.49/0.57  fof(f16,axiom,(
% 1.49/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.49/0.57  fof(f217,plain,(
% 1.49/0.57    spl2_26),
% 1.49/0.57    inference(avatar_split_clause,[],[f72,f215])).
% 1.49/0.57  fof(f72,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f39])).
% 1.49/0.57  fof(f39,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.57    inference(flattening,[],[f38])).
% 1.49/0.57  fof(f38,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.49/0.57    inference(ennf_transformation,[],[f11])).
% 1.49/0.57  fof(f11,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.49/0.57  fof(f206,plain,(
% 1.49/0.57    spl2_24),
% 1.49/0.57    inference(avatar_split_clause,[],[f56,f204])).
% 1.49/0.57  fof(f56,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f30])).
% 1.49/0.57  fof(f30,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.57    inference(flattening,[],[f29])).
% 1.49/0.57  fof(f29,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f19])).
% 1.49/0.57  fof(f19,axiom,(
% 1.49/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 1.49/0.57  fof(f198,plain,(
% 1.49/0.57    spl2_22),
% 1.49/0.57    inference(avatar_split_clause,[],[f68,f196])).
% 1.49/0.57  fof(f68,plain,(
% 1.49/0.57    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f36])).
% 1.49/0.57  fof(f36,plain,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.57    inference(flattening,[],[f35])).
% 1.49/0.57  fof(f35,plain,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f17])).
% 1.49/0.57  fof(f17,axiom,(
% 1.49/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.49/0.57  fof(f184,plain,(
% 1.49/0.57    spl2_21),
% 1.49/0.57    inference(avatar_split_clause,[],[f73,f182])).
% 1.49/0.57  fof(f73,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.57    inference(forward_demodulation,[],[f67,f51])).
% 1.49/0.57  fof(f51,plain,(
% 1.49/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.49/0.57    inference(cnf_transformation,[],[f8])).
% 1.49/0.57  fof(f8,axiom,(
% 1.49/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.49/0.57  fof(f67,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f34])).
% 1.49/0.57  fof(f34,plain,(
% 1.49/0.57    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f13])).
% 1.49/0.57  fof(f13,axiom,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 1.49/0.57  fof(f178,plain,(
% 1.49/0.57    spl2_20),
% 1.49/0.57    inference(avatar_split_clause,[],[f71,f176])).
% 1.49/0.57  fof(f71,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f37])).
% 1.49/0.57  fof(f37,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f12])).
% 1.49/0.57  fof(f12,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.49/0.57  fof(f172,plain,(
% 1.49/0.57    spl2_19),
% 1.49/0.57    inference(avatar_split_clause,[],[f66,f170])).
% 1.49/0.57  fof(f66,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f33])).
% 1.49/0.57  fof(f33,plain,(
% 1.49/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f9])).
% 1.49/0.57  fof(f9,axiom,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.49/0.57  fof(f143,plain,(
% 1.49/0.57    spl2_15),
% 1.49/0.57    inference(avatar_split_clause,[],[f62,f141])).
% 1.49/0.57  fof(f62,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f7])).
% 1.49/0.57  fof(f7,axiom,(
% 1.49/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.49/0.57  fof(f139,plain,(
% 1.49/0.57    spl2_14),
% 1.49/0.57    inference(avatar_split_clause,[],[f61,f137])).
% 1.49/0.57  fof(f61,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f6])).
% 1.49/0.57  fof(f6,axiom,(
% 1.49/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.49/0.57  fof(f131,plain,(
% 1.49/0.57    spl2_13),
% 1.49/0.57    inference(avatar_split_clause,[],[f64,f129])).
% 1.49/0.57  fof(f64,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f31])).
% 1.49/0.57  fof(f31,plain,(
% 1.49/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.49/0.57    inference(ennf_transformation,[],[f4])).
% 1.49/0.57  fof(f4,axiom,(
% 1.49/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.49/0.57  fof(f123,plain,(
% 1.49/0.57    spl2_11),
% 1.49/0.57    inference(avatar_split_clause,[],[f70,f121])).
% 1.49/0.57  fof(f70,plain,(
% 1.49/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f45])).
% 1.49/0.57  fof(f45,plain,(
% 1.49/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.49/0.57    inference(nnf_transformation,[],[f15])).
% 1.49/0.57  fof(f15,axiom,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.57  fof(f115,plain,(
% 1.49/0.57    spl2_9),
% 1.49/0.57    inference(avatar_split_clause,[],[f59,f113])).
% 1.49/0.57  fof(f59,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f2])).
% 1.49/0.57  fof(f2,axiom,(
% 1.49/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.49/0.57  fof(f111,plain,(
% 1.49/0.57    spl2_8),
% 1.49/0.57    inference(avatar_split_clause,[],[f58,f109])).
% 1.49/0.57  fof(f58,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f1])).
% 1.49/0.57  fof(f1,axiom,(
% 1.49/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.49/0.57  fof(f107,plain,(
% 1.49/0.57    spl2_7),
% 1.49/0.57    inference(avatar_split_clause,[],[f57,f105])).
% 1.49/0.57  fof(f57,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f5])).
% 1.49/0.57  fof(f5,axiom,(
% 1.49/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.49/0.57  fof(f97,plain,(
% 1.49/0.57    spl2_4 | spl2_5),
% 1.49/0.57    inference(avatar_split_clause,[],[f49,f94,f90])).
% 1.49/0.57  fof(f49,plain,(
% 1.49/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.49/0.57    inference(cnf_transformation,[],[f44])).
% 1.49/0.57  fof(f88,plain,(
% 1.49/0.57    spl2_3),
% 1.49/0.57    inference(avatar_split_clause,[],[f48,f85])).
% 1.49/0.57  fof(f48,plain,(
% 1.49/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.57    inference(cnf_transformation,[],[f44])).
% 1.49/0.57  fof(f83,plain,(
% 1.49/0.57    spl2_2),
% 1.49/0.57    inference(avatar_split_clause,[],[f47,f80])).
% 1.49/0.57  fof(f47,plain,(
% 1.49/0.57    l1_pre_topc(sK0)),
% 1.49/0.57    inference(cnf_transformation,[],[f44])).
% 1.49/0.57  fof(f78,plain,(
% 1.49/0.57    spl2_1),
% 1.49/0.57    inference(avatar_split_clause,[],[f46,f75])).
% 1.49/0.57  fof(f46,plain,(
% 1.49/0.57    v2_pre_topc(sK0)),
% 1.49/0.57    inference(cnf_transformation,[],[f44])).
% 1.49/0.57  % SZS output end Proof for theBenchmark
% 1.49/0.57  % (32653)------------------------------
% 1.49/0.57  % (32653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (32653)Termination reason: Refutation
% 1.49/0.57  
% 1.49/0.57  % (32653)Memory used [KB]: 8059
% 1.49/0.57  % (32653)Time elapsed: 0.142 s
% 1.49/0.57  % (32653)------------------------------
% 1.49/0.57  % (32653)------------------------------
% 1.49/0.58  % (32646)Success in time 0.215 s
%------------------------------------------------------------------------------
