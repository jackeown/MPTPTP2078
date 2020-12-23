%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  359 (1643 expanded)
%              Number of leaves         :   80 ( 612 expanded)
%              Depth                    :   12
%              Number of atoms          :  847 (2858 expanded)
%              Number of equality atoms :  235 (1332 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1489,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f84,f420,f421,f457,f463,f473,f478,f586,f599,f606,f617,f630,f684,f694,f713,f719,f743,f771,f777,f799,f818,f830,f835,f853,f875,f901,f923,f933,f940,f958,f964,f987,f989,f1004,f1027,f1028,f1042,f1064,f1068,f1075,f1083,f1107,f1113,f1118,f1143,f1171,f1176,f1205,f1223,f1228,f1233,f1272,f1294,f1321,f1326,f1331,f1343,f1366,f1375,f1380,f1404,f1421,f1437,f1439,f1441,f1443,f1444,f1446,f1462,f1483,f1488])).

fof(f1488,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f1487])).

fof(f1487,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f1486,f73])).

fof(f73,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1486,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f1485,f78])).

fof(f78,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1485,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3
    | spl2_4
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f1484,f83])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1484,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl2_4
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f1478,f414])).

fof(f414,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1478,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_12 ),
    inference(superposition,[],[f64,f605])).

fof(f605,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f603])).

fof(f603,plain,
    ( spl2_12
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f1483,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f1482])).

fof(f1482,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f1481,f83])).

fof(f1481,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_4
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f1479,f414])).

fof(f1479,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(trivial_inequality_removal,[],[f1477])).

fof(f1477,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(superposition,[],[f632,f605])).

fof(f632,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f631,f78])).

fof(f631,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f52,f73])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f1462,plain,
    ( spl2_12
    | ~ spl2_31
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1447,f1080,f937,f603])).

fof(f937,plain,
    ( spl2_31
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f1080,plain,
    ( spl2_37
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f1447,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_31
    | ~ spl2_37 ),
    inference(superposition,[],[f939,f1082])).

fof(f1082,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f1080])).

fof(f939,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f937])).

fof(f1446,plain,
    ( spl2_31
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f1424,f1418,f937])).

fof(f1418,plain,
    ( spl2_58
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f1424,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_58 ),
    inference(superposition,[],[f104,f1420])).

fof(f1420,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f104,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f101,f90])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(resolution,[],[f61,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f57,f99])).

fof(f99,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f86,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f58,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1444,plain,
    ( spl2_32
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f1422,f1418,f955])).

fof(f955,plain,
    ( spl2_32
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f1422,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_58 ),
    inference(superposition,[],[f53,f1420])).

fof(f1443,plain,
    ( spl2_35
    | ~ spl2_58 ),
    inference(avatar_contradiction_clause,[],[f1442])).

fof(f1442,plain,
    ( $false
    | spl2_35
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f1434,f1062])).

fof(f1062,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_35 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f1061,plain,
    ( spl2_35
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f1434,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_58 ),
    inference(superposition,[],[f333,f1420])).

fof(f333,plain,(
    ! [X10,X9] : k3_xboole_0(k2_xboole_0(X9,X10),X9) = X9 ),
    inference(superposition,[],[f218,f90])).

fof(f218,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f133,f99])).

fof(f133,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f119,f61])).

fof(f119,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f114,f101])).

fof(f114,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f53,f111])).

fof(f111,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f88,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f59,f56])).

fof(f1441,plain,
    ( spl2_31
    | ~ spl2_58 ),
    inference(avatar_contradiction_clause,[],[f1440])).

fof(f1440,plain,
    ( $false
    | spl2_31
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f1424,f938])).

fof(f938,plain,
    ( sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_31 ),
    inference(avatar_component_clause,[],[f937])).

fof(f1439,plain,
    ( spl2_34
    | ~ spl2_58 ),
    inference(avatar_contradiction_clause,[],[f1438])).

fof(f1438,plain,
    ( $false
    | spl2_34
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f1423,f985])).

fof(f985,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | spl2_34 ),
    inference(avatar_component_clause,[],[f984])).

fof(f984,plain,
    ( spl2_34
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f1423,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_58 ),
    inference(superposition,[],[f90,f1420])).

fof(f1437,plain,
    ( spl2_32
    | ~ spl2_58 ),
    inference(avatar_contradiction_clause,[],[f1436])).

fof(f1436,plain,
    ( $false
    | spl2_32
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f1422,f956])).

fof(f956,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_32 ),
    inference(avatar_component_clause,[],[f955])).

fof(f1421,plain,
    ( spl2_58
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f1416,f475,f460,f1418])).

fof(f460,plain,
    ( spl2_7
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f475,plain,
    ( spl2_9
  <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f1416,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f1415,f477])).

fof(f477,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f475])).

fof(f1415,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_7 ),
    inference(resolution,[],[f1368,f462])).

fof(f462,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f460])).

fof(f1368,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,X1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,X1)) )
    | ~ spl2_7 ),
    inference(resolution,[],[f993,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f993,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | k4_subset_1(sK1,k2_tops_1(sK0,sK1),X2) = k2_xboole_0(k2_tops_1(sK0,sK1),X2) )
    | ~ spl2_7 ),
    inference(resolution,[],[f462,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1404,plain,
    ( spl2_57
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f1399,f691,f81,f1401])).

fof(f1401,plain,
    ( spl2_57
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f691,plain,
    ( spl2_16
  <=> u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f1399,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f1398,f693])).

fof(f693,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f691])).

fof(f1398,plain,
    ( k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f1397,f111])).

fof(f1397,plain,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f1299,f83])).

fof(f1299,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X9) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X9) )
    | ~ spl2_3 ),
    inference(resolution,[],[f573,f83])).

fof(f573,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | k4_subset_1(X4,k3_subset_1(X4,X5),X3) = k2_xboole_0(k3_subset_1(X4,X5),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f67,f62])).

fof(f1380,plain,
    ( spl2_56
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f879,f872,f1377])).

fof(f1377,plain,
    ( spl2_56
  <=> k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k5_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f872,plain,
    ( spl2_27
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f879,plain,
    ( k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k5_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_27 ),
    inference(superposition,[],[f60,f874])).

fof(f874,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f872])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1375,plain,
    ( spl2_55
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f702,f691,f1372])).

fof(f1372,plain,
    ( spl2_55
  <=> k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f702,plain,
    ( k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f148,f693])).

fof(f148,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k4_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f144,f128])).

fof(f128,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f60,f91])).

fof(f91,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f61,f85])).

fof(f85,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f53,f57])).

fof(f144,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k5_xboole_0(X3,X3) ),
    inference(superposition,[],[f60,f113])).

fof(f113,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f90,f111])).

fof(f1366,plain,
    ( spl2_54
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f991,f460,f1363])).

fof(f1363,plain,
    ( spl2_54
  <=> sK1 = k4_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f991,plain,
    ( sK1 = k4_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))))
    | ~ spl2_7 ),
    inference(resolution,[],[f462,f466])).

fof(f466,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k4_subset_1(X2,k3_subset_1(X2,X3),k3_subset_1(X2,k3_subset_1(X2,X3))) = X2 ) ),
    inference(resolution,[],[f69,f62])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f63,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f1343,plain,
    ( spl2_53
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f1237,f1220,f1340])).

fof(f1340,plain,
    ( spl2_53
  <=> k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f1220,plain,
    ( spl2_45
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f1237,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_45 ),
    inference(superposition,[],[f60,f1222])).

fof(f1222,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f1331,plain,
    ( spl2_52
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1098,f1080,f1328])).

fof(f1328,plain,
    ( spl2_52
  <=> k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f1098,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f154,f1082])).

fof(f154,plain,(
    ! [X4,X3] : k4_xboole_0(k2_xboole_0(X4,X3),X3) = k5_xboole_0(k2_xboole_0(X4,X3),X3) ),
    inference(superposition,[],[f130,f113])).

fof(f130,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f60,f99])).

fof(f1326,plain,
    ( spl2_51
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1096,f1080,f1323])).

fof(f1323,plain,
    ( spl2_51
  <=> k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f1096,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f148,f1082])).

fof(f1321,plain,
    ( spl2_50
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f1087,f81,f76,f1318])).

fof(f1318,plain,
    ( spl2_50
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f1087,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f982,f83])).

fof(f982,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f50,f78])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1294,plain,
    ( spl2_49
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1102,f1080,f1291])).

fof(f1291,plain,
    ( spl2_49
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f1102,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f334,f1082])).

fof(f334,plain,(
    ! [X12,X11] : k3_xboole_0(k2_xboole_0(X12,X11),X11) = X11 ),
    inference(superposition,[],[f218,f113])).

fof(f1272,plain,
    ( spl2_48
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1100,f1080,f1269])).

fof(f1269,plain,
    ( spl2_48
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f1100,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f178,f1082])).

fof(f178,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f145,f111])).

fof(f145,plain,(
    ! [X10,X9] : k2_xboole_0(X10,X9) = k2_xboole_0(k2_xboole_0(X10,X9),X9) ),
    inference(superposition,[],[f101,f113])).

fof(f1233,plain,
    ( spl2_47
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1097,f1080,f1230])).

fof(f1230,plain,
    ( spl2_47
  <=> k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k5_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f1097,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_37 ),
    inference(superposition,[],[f153,f1082])).

fof(f153,plain,(
    ! [X2,X1] : k4_xboole_0(k2_xboole_0(X1,X2),X1) = k5_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f130,f90])).

fof(f1228,plain,
    ( spl2_46
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1095,f1080,f1225])).

fof(f1225,plain,
    ( spl2_46
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f1095,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f145,f1082])).

fof(f1223,plain,
    ( spl2_45
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1092,f1080,f1220])).

fof(f1092,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f113,f1082])).

fof(f1205,plain,
    ( spl2_44
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1099,f1080,f1202])).

fof(f1202,plain,
    ( spl2_44
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1099,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f163,f1082])).

fof(f163,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f104,f111])).

fof(f1176,plain,
    ( spl2_43
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1094,f1080,f1173])).

fof(f1173,plain,
    ( spl2_43
  <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f1094,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f132,f1082])).

fof(f132,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f129,f128])).

fof(f129,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f60,f90])).

fof(f1171,plain,
    ( spl2_42
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1091,f1080,f1168])).

fof(f1168,plain,
    ( spl2_42
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f1091,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_37 ),
    inference(superposition,[],[f104,f1082])).

fof(f1143,plain,
    ( spl2_41
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1101,f1080,f1140])).

fof(f1140,plain,
    ( spl2_41
  <=> sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f1101,plain,
    ( sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_37 ),
    inference(superposition,[],[f333,f1082])).

fof(f1118,plain,
    ( spl2_40
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1093,f1080,f1115])).

fof(f1115,plain,
    ( spl2_40
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f1093,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f114,f1082])).

fof(f1113,plain,
    ( spl2_39
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1090,f1080,f1110])).

fof(f1110,plain,
    ( spl2_39
  <=> sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f1090,plain,
    ( sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f90,f1082])).

fof(f1107,plain,
    ( spl2_38
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1089,f1080,f1104])).

fof(f1104,plain,
    ( spl2_38
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f1089,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f53,f1082])).

fof(f1083,plain,
    ( spl2_37
    | ~ spl2_13
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f1076,f1072,f614,f1080])).

fof(f614,plain,
    ( spl2_13
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f1072,plain,
    ( spl2_36
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f1076,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_13
    | ~ spl2_36 ),
    inference(superposition,[],[f1074,f616])).

fof(f616,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f614])).

fof(f1074,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f1075,plain,
    ( spl2_36
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f927,f81,f76,f1072])).

fof(f927,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f800,f83])).

fof(f800,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f49,f78])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f1068,plain,
    ( ~ spl2_35
    | spl2_34 ),
    inference(avatar_split_clause,[],[f1066,f984,f1061])).

fof(f1066,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_34 ),
    inference(superposition,[],[f985,f99])).

fof(f1064,plain,
    ( spl2_35
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f1005,f984,f1061])).

fof(f1005,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_34 ),
    inference(superposition,[],[f986,f99])).

fof(f986,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f984])).

fof(f1042,plain,
    ( spl2_33
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f1024,f984,f961])).

fof(f961,plain,
    ( spl2_33
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f1024,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_34 ),
    inference(superposition,[],[f249,f986])).

fof(f249,plain,(
    ! [X8,X7] : k2_xboole_0(k3_xboole_0(X8,X7),X7) = X7 ),
    inference(superposition,[],[f178,f101])).

fof(f1028,plain,
    ( spl2_31
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f1011,f984,f937])).

fof(f1011,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_34 ),
    inference(superposition,[],[f101,f986])).

fof(f1027,plain,
    ( spl2_31
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f1026])).

fof(f1026,plain,
    ( $false
    | spl2_31
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f1011,f938])).

fof(f1004,plain,
    ( spl2_34
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f959,f955,f984])).

fof(f959,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_32 ),
    inference(resolution,[],[f957,f61])).

fof(f957,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f955])).

fof(f989,plain,
    ( spl2_31
    | ~ spl2_33 ),
    inference(avatar_contradiction_clause,[],[f988])).

fof(f988,plain,
    ( $false
    | spl2_31
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f938,f971])).

fof(f971,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_33 ),
    inference(superposition,[],[f111,f963])).

fof(f963,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f961])).

fof(f987,plain,
    ( spl2_34
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f944,f937,f984])).

fof(f944,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_31 ),
    inference(superposition,[],[f113,f939])).

fof(f964,plain,
    ( spl2_33
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f951,f937,f961])).

fof(f951,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_31 ),
    inference(superposition,[],[f178,f939])).

fof(f958,plain,
    ( spl2_32
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f945,f937,f955])).

fof(f945,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_31 ),
    inference(superposition,[],[f114,f939])).

fof(f940,plain,
    ( spl2_31
    | ~ spl2_13
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f934,f930,f614,f937])).

fof(f930,plain,
    ( spl2_30
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f934,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_13
    | ~ spl2_30 ),
    inference(superposition,[],[f932,f616])).

fof(f932,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f930])).

fof(f933,plain,
    ( spl2_30
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f928,f603,f81,f76,f930])).

fof(f928,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f927,f605])).

fof(f923,plain,
    ( spl2_29
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f704,f691,f920])).

fof(f920,plain,
    ( spl2_29
  <=> k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f704,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_16 ),
    inference(superposition,[],[f154,f693])).

fof(f901,plain,
    ( spl2_28
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f708,f691,f898])).

fof(f898,plain,
    ( spl2_28
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f708,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_16 ),
    inference(superposition,[],[f334,f693])).

fof(f875,plain,
    ( spl2_27
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f698,f691,f872])).

fof(f698,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f113,f693])).

fof(f853,plain,
    ( spl2_26
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f706,f691,f850])).

fof(f850,plain,
    ( spl2_26
  <=> u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f706,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f178,f693])).

fof(f835,plain,
    ( spl2_25
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f701,f691,f832])).

fof(f832,plain,
    ( spl2_25
  <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f701,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_16 ),
    inference(superposition,[],[f145,f693])).

fof(f830,plain,
    ( spl2_24
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f703,f691,f827])).

fof(f827,plain,
    ( spl2_24
  <=> k4_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f703,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_16 ),
    inference(superposition,[],[f153,f693])).

fof(f818,plain,
    ( spl2_23
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f700,f691,f815])).

fof(f815,plain,
    ( spl2_23
  <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f700,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f132,f693])).

fof(f799,plain,
    ( spl2_22
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f705,f691,f796])).

fof(f796,plain,
    ( spl2_22
  <=> u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f705,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f163,f693])).

fof(f777,plain,
    ( spl2_21
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f697,f691,f774])).

fof(f774,plain,
    ( spl2_21
  <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f697,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_16 ),
    inference(superposition,[],[f104,f693])).

fof(f771,plain,
    ( spl2_20
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f699,f691,f768])).

fof(f768,plain,
    ( spl2_20
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f699,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f114,f693])).

fof(f743,plain,
    ( spl2_19
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f707,f691,f740])).

fof(f740,plain,
    ( spl2_19
  <=> sK1 = k3_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f707,plain,
    ( sK1 = k3_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_16 ),
    inference(superposition,[],[f333,f693])).

fof(f719,plain,
    ( spl2_18
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f696,f691,f716])).

fof(f716,plain,
    ( spl2_18
  <=> sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f696,plain,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f90,f693])).

fof(f713,plain,
    ( spl2_17
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f695,f691,f710])).

fof(f710,plain,
    ( spl2_17
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f695,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f53,f693])).

fof(f694,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f689,f470,f81,f691])).

fof(f470,plain,
    ( spl2_8
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f689,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f688,f472])).

fof(f472,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f470])).

fof(f688,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f578,f83])).

fof(f578,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X1)) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X1)) )
    | ~ spl2_3 ),
    inference(resolution,[],[f576,f62])).

fof(f576,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X9) = k2_xboole_0(sK1,X9) )
    | ~ spl2_3 ),
    inference(resolution,[],[f67,f83])).

fof(f684,plain,
    ( spl2_15
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f679,f81,f76,f681])).

fof(f681,plain,
    ( spl2_15
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f679,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f558,f83])).

fof(f558,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0))) )
    | ~ spl2_2 ),
    inference(resolution,[],[f557,f69])).

fof(f557,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2 ),
    inference(resolution,[],[f65,f78])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f630,plain,
    ( spl2_14
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f625,f81,f627])).

fof(f627,plain,
    ( spl2_14
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f625,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_3 ),
    inference(resolution,[],[f466,f83])).

fof(f617,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f612,f81,f76,f614])).

fof(f612,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f579,f83])).

fof(f579,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2)) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f576,f557])).

fof(f606,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f601,f413,f81,f76,f603])).

fof(f601,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f600,f83])).

fof(f600,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f415,f560])).

fof(f560,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_2 ),
    inference(resolution,[],[f51,f78])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f415,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f413])).

fof(f599,plain,
    ( spl2_11
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f594,f460,f596])).

fof(f596,plain,
    ( spl2_11
  <=> k2_tops_1(sK0,sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f594,plain,
    ( k2_tops_1(sK0,sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f593,f92])).

fof(f92,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f57,f91])).

fof(f593,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_7 ),
    inference(resolution,[],[f574,f462])).

fof(f574,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
        | k4_subset_1(sK1,k2_tops_1(sK0,sK1),X6) = k2_xboole_0(k2_tops_1(sK0,sK1),X6) )
    | ~ spl2_7 ),
    inference(resolution,[],[f67,f462])).

fof(f586,plain,
    ( spl2_10
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f581,f81,f583])).

fof(f583,plain,
    ( spl2_10
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f581,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f580,f92])).

fof(f580,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f576,f83])).

fof(f478,plain,
    ( spl2_9
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f467,f460,f475])).

fof(f467,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_7 ),
    inference(resolution,[],[f69,f462])).

fof(f473,plain,
    ( spl2_8
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f468,f81,f470])).

fof(f468,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f69,f83])).

fof(f463,plain,
    ( spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f458,f454,f460])).

fof(f454,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f458,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_6 ),
    inference(superposition,[],[f68,f456])).

fof(f456,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f454])).

fof(f68,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f54,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f457,plain,
    ( spl2_6
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f451,f417,f81,f454])).

fof(f417,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f451,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f448,f419])).

fof(f419,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f417])).

fof(f448,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_3 ),
    inference(resolution,[],[f66,f83])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f421,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f47,f417,f413])).

fof(f47,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f420,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f46,f417,f413])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f45,f81])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f44,f76])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f43,f71])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (30248)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (30252)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (30256)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (30251)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (30263)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (30249)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (30257)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (30262)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (30253)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (30265)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (30260)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (30255)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (30254)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (30259)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (30250)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (30261)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (30258)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (30264)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.53  % (30248)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1489,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f74,f79,f84,f420,f421,f457,f463,f473,f478,f586,f599,f606,f617,f630,f684,f694,f713,f719,f743,f771,f777,f799,f818,f830,f835,f853,f875,f901,f923,f933,f940,f958,f964,f987,f989,f1004,f1027,f1028,f1042,f1064,f1068,f1075,f1083,f1107,f1113,f1118,f1143,f1171,f1176,f1205,f1223,f1228,f1233,f1272,f1294,f1321,f1326,f1331,f1343,f1366,f1375,f1380,f1404,f1421,f1437,f1439,f1441,f1443,f1444,f1446,f1462,f1483,f1488])).
% 0.21/0.53  fof(f1488,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1487])).
% 0.21/0.53  fof(f1487,plain,(
% 0.21/0.53    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1486,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f1486,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | (~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1485,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f1485,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_3 | spl2_4 | ~spl2_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1484,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f1484,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl2_4 | ~spl2_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1478,f414])).
% 0.21/0.53  fof(f414,plain,(
% 0.21/0.53    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f413])).
% 0.21/0.53  fof(f413,plain,(
% 0.21/0.53    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f1478,plain,(
% 0.21/0.53    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_12),
% 0.21/0.53    inference(superposition,[],[f64,f605])).
% 0.21/0.53  fof(f605,plain,(
% 0.21/0.53    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f603])).
% 0.21/0.53  fof(f603,plain,(
% 0.21/0.53    spl2_12 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.21/0.53  fof(f1483,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1482])).
% 0.21/0.53  fof(f1482,plain,(
% 0.21/0.53    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1481,f83])).
% 0.21/0.53  fof(f1481,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_2 | spl2_4 | ~spl2_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1479,f414])).
% 0.21/0.53  fof(f1479,plain,(
% 0.21/0.53    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_12)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f1477])).
% 0.21/0.53  fof(f1477,plain,(
% 0.21/0.53    sK1 != sK1 | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_12)),
% 0.21/0.53    inference(superposition,[],[f632,f605])).
% 0.21/0.53  fof(f632,plain,(
% 0.21/0.53    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f631,f78])).
% 0.21/0.53  fof(f631,plain,(
% 0.21/0.53    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_1),
% 0.21/0.53    inference(resolution,[],[f52,f73])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.53  fof(f1462,plain,(
% 0.21/0.53    spl2_12 | ~spl2_31 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1447,f1080,f937,f603])).
% 0.21/0.53  fof(f937,plain,(
% 0.21/0.53    spl2_31 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.53  fof(f1080,plain,(
% 0.21/0.53    spl2_37 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.53  fof(f1447,plain,(
% 0.21/0.53    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_31 | ~spl2_37)),
% 0.21/0.53    inference(superposition,[],[f939,f1082])).
% 0.21/0.53  fof(f1082,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(avatar_component_clause,[],[f1080])).
% 0.21/0.53  fof(f939,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_31),
% 0.21/0.53    inference(avatar_component_clause,[],[f937])).
% 0.21/0.53  fof(f1446,plain,(
% 0.21/0.53    spl2_31 | ~spl2_58),
% 0.21/0.53    inference(avatar_split_clause,[],[f1424,f1418,f937])).
% 0.21/0.53  fof(f1418,plain,(
% 0.21/0.53    spl2_58 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 0.21/0.53  fof(f1424,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_58),
% 0.21/0.53    inference(superposition,[],[f104,f1420])).
% 0.21/0.53  fof(f1420,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_58),
% 0.21/0.53    inference(avatar_component_clause,[],[f1418])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 0.21/0.53    inference(superposition,[],[f101,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.53    inference(resolution,[],[f61,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 0.21/0.53    inference(superposition,[],[f57,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.21/0.53    inference(superposition,[],[f86,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.21/0.53    inference(superposition,[],[f58,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.53  fof(f1444,plain,(
% 0.21/0.53    spl2_32 | ~spl2_58),
% 0.21/0.53    inference(avatar_split_clause,[],[f1422,f1418,f955])).
% 0.21/0.53  fof(f955,plain,(
% 0.21/0.53    spl2_32 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.53  fof(f1422,plain,(
% 0.21/0.53    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_58),
% 0.21/0.53    inference(superposition,[],[f53,f1420])).
% 0.21/0.53  fof(f1443,plain,(
% 0.21/0.53    spl2_35 | ~spl2_58),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1442])).
% 0.21/0.53  fof(f1442,plain,(
% 0.21/0.53    $false | (spl2_35 | ~spl2_58)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1434,f1062])).
% 0.21/0.53  fof(f1062,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_35),
% 0.21/0.53    inference(avatar_component_clause,[],[f1061])).
% 0.21/0.53  fof(f1061,plain,(
% 0.21/0.53    spl2_35 <=> k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.53  fof(f1434,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_58),
% 0.21/0.53    inference(superposition,[],[f333,f1420])).
% 0.21/0.53  fof(f333,plain,(
% 0.21/0.53    ( ! [X10,X9] : (k3_xboole_0(k2_xboole_0(X9,X10),X9) = X9) )),
% 0.21/0.53    inference(superposition,[],[f218,f90])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 0.21/0.53    inference(superposition,[],[f133,f99])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 0.21/0.53    inference(resolution,[],[f119,f61])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) )),
% 0.21/0.53    inference(superposition,[],[f114,f101])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) )),
% 0.21/0.53    inference(superposition,[],[f53,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 0.21/0.53    inference(superposition,[],[f88,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 0.21/0.53    inference(superposition,[],[f59,f56])).
% 0.21/0.53  fof(f1441,plain,(
% 0.21/0.53    spl2_31 | ~spl2_58),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1440])).
% 0.21/0.53  fof(f1440,plain,(
% 0.21/0.53    $false | (spl2_31 | ~spl2_58)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1424,f938])).
% 0.21/0.53  fof(f938,plain,(
% 0.21/0.53    sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_31),
% 0.21/0.53    inference(avatar_component_clause,[],[f937])).
% 0.21/0.53  fof(f1439,plain,(
% 0.21/0.53    spl2_34 | ~spl2_58),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1438])).
% 0.21/0.53  fof(f1438,plain,(
% 0.21/0.53    $false | (spl2_34 | ~spl2_58)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1423,f985])).
% 0.21/0.53  fof(f985,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) != k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | spl2_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f984])).
% 0.21/0.53  fof(f984,plain,(
% 0.21/0.53    spl2_34 <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.53  fof(f1423,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_58),
% 0.21/0.53    inference(superposition,[],[f90,f1420])).
% 0.21/0.53  fof(f1437,plain,(
% 0.21/0.53    spl2_32 | ~spl2_58),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1436])).
% 0.21/0.53  fof(f1436,plain,(
% 0.21/0.53    $false | (spl2_32 | ~spl2_58)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1422,f956])).
% 0.21/0.53  fof(f956,plain,(
% 0.21/0.53    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_32),
% 0.21/0.53    inference(avatar_component_clause,[],[f955])).
% 0.21/0.53  fof(f1421,plain,(
% 0.21/0.53    spl2_58 | ~spl2_7 | ~spl2_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f1416,f475,f460,f1418])).
% 0.21/0.53  fof(f460,plain,(
% 0.21/0.53    spl2_7 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.53  fof(f475,plain,(
% 0.21/0.53    spl2_9 <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.53  fof(f1416,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | (~spl2_7 | ~spl2_9)),
% 0.21/0.53    inference(forward_demodulation,[],[f1415,f477])).
% 0.21/0.53  fof(f477,plain,(
% 0.21/0.53    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f475])).
% 0.21/0.53  fof(f1415,plain,(
% 0.21/0.53    k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_7),
% 0.21/0.53    inference(resolution,[],[f1368,f462])).
% 0.21/0.53  fof(f462,plain,(
% 0.21/0.53    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f460])).
% 0.21/0.53  fof(f1368,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK1)) | k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,X1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,X1))) ) | ~spl2_7),
% 0.21/0.53    inference(resolution,[],[f993,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.53  fof(f993,plain,(
% 0.21/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | k4_subset_1(sK1,k2_tops_1(sK0,sK1),X2) = k2_xboole_0(k2_tops_1(sK0,sK1),X2)) ) | ~spl2_7),
% 0.21/0.53    inference(resolution,[],[f462,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(flattening,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.53  fof(f1404,plain,(
% 0.21/0.53    spl2_57 | ~spl2_3 | ~spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f1399,f691,f81,f1401])).
% 0.21/0.53  fof(f1401,plain,(
% 0.21/0.53    spl2_57 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 0.21/0.53  fof(f691,plain,(
% 0.21/0.53    spl2_16 <=> u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.53  fof(f1399,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) | (~spl2_3 | ~spl2_16)),
% 0.21/0.53    inference(forward_demodulation,[],[f1398,f693])).
% 0.21/0.53  fof(f693,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f691])).
% 0.21/0.53  fof(f1398,plain,(
% 0.21/0.53    k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) | ~spl2_3),
% 0.21/0.53    inference(forward_demodulation,[],[f1397,f111])).
% 0.21/0.53  fof(f1397,plain,(
% 0.21/0.53    k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) | ~spl2_3),
% 0.21/0.53    inference(resolution,[],[f1299,f83])).
% 0.21/0.53  fof(f1299,plain,(
% 0.21/0.53    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X9) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X9)) ) | ~spl2_3),
% 0.21/0.53    inference(resolution,[],[f573,f83])).
% 0.21/0.53  fof(f573,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(X4)) | k4_subset_1(X4,k3_subset_1(X4,X5),X3) = k2_xboole_0(k3_subset_1(X4,X5),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X4))) )),
% 0.21/0.53    inference(resolution,[],[f67,f62])).
% 0.21/0.53  fof(f1380,plain,(
% 0.21/0.53    spl2_56 | ~spl2_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f879,f872,f1377])).
% 0.21/0.53  fof(f1377,plain,(
% 0.21/0.53    spl2_56 <=> k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k5_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 0.21/0.53  fof(f872,plain,(
% 0.21/0.53    spl2_27 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.53  fof(f879,plain,(
% 0.21/0.53    k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k5_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_27),
% 0.21/0.53    inference(superposition,[],[f60,f874])).
% 0.21/0.53  fof(f874,plain,(
% 0.21/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f872])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f1375,plain,(
% 0.21/0.53    spl2_55 | ~spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f702,f691,f1372])).
% 0.21/0.53  fof(f1372,plain,(
% 0.21/0.53    spl2_55 <=> k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 0.21/0.53  fof(f702,plain,(
% 0.21/0.53    k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_16),
% 0.21/0.53    inference(superposition,[],[f148,f693])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k4_xboole_0(X3,X3)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f144,f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f60,f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 0.21/0.53    inference(resolution,[],[f61,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f53,f57])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k5_xboole_0(X3,X3)) )),
% 0.21/0.53    inference(superposition,[],[f60,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) )),
% 0.21/0.53    inference(superposition,[],[f90,f111])).
% 0.21/0.53  fof(f1366,plain,(
% 0.21/0.53    spl2_54 | ~spl2_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f991,f460,f1363])).
% 0.21/0.53  fof(f1363,plain,(
% 0.21/0.53    spl2_54 <=> sK1 = k4_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.21/0.53  fof(f991,plain,(
% 0.21/0.53    sK1 = k4_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))) | ~spl2_7),
% 0.21/0.53    inference(resolution,[],[f462,f466])).
% 0.21/0.53  fof(f466,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k4_subset_1(X2,k3_subset_1(X2,X3),k3_subset_1(X2,k3_subset_1(X2,X3))) = X2) )),
% 0.21/0.53    inference(resolution,[],[f69,f62])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f63,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 0.21/0.53  fof(f1343,plain,(
% 0.21/0.53    spl2_53 | ~spl2_45),
% 0.21/0.53    inference(avatar_split_clause,[],[f1237,f1220,f1340])).
% 0.21/0.53  fof(f1340,plain,(
% 0.21/0.53    spl2_53 <=> k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.21/0.53  fof(f1220,plain,(
% 0.21/0.53    spl2_45 <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.21/0.53  fof(f1237,plain,(
% 0.21/0.53    k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_45),
% 0.21/0.53    inference(superposition,[],[f60,f1222])).
% 0.21/0.53  fof(f1222,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_45),
% 0.21/0.53    inference(avatar_component_clause,[],[f1220])).
% 0.21/0.53  fof(f1331,plain,(
% 0.21/0.53    spl2_52 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1098,f1080,f1328])).
% 0.21/0.53  fof(f1328,plain,(
% 0.21/0.53    spl2_52 <=> k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 0.21/0.53  fof(f1098,plain,(
% 0.21/0.53    k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f154,f1082])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k4_xboole_0(k2_xboole_0(X4,X3),X3) = k5_xboole_0(k2_xboole_0(X4,X3),X3)) )),
% 0.21/0.53    inference(superposition,[],[f130,f113])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))) )),
% 0.21/0.53    inference(superposition,[],[f60,f99])).
% 0.21/0.53  fof(f1326,plain,(
% 0.21/0.53    spl2_51 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1096,f1080,f1323])).
% 0.21/0.53  fof(f1323,plain,(
% 0.21/0.53    spl2_51 <=> k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.21/0.53  fof(f1096,plain,(
% 0.21/0.53    k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f148,f1082])).
% 0.21/0.53  fof(f1321,plain,(
% 0.21/0.53    spl2_50 | ~spl2_2 | ~spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f1087,f81,f76,f1318])).
% 0.21/0.53  fof(f1318,plain,(
% 0.21/0.53    spl2_50 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.21/0.53  fof(f1087,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 0.21/0.53    inference(resolution,[],[f982,f83])).
% 0.21/0.53  fof(f982,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_2),
% 0.21/0.53    inference(resolution,[],[f50,f78])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.53  fof(f1294,plain,(
% 0.21/0.53    spl2_49 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1102,f1080,f1291])).
% 0.21/0.53  fof(f1291,plain,(
% 0.21/0.53    spl2_49 <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 0.21/0.53  fof(f1102,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f334,f1082])).
% 0.21/0.53  fof(f334,plain,(
% 0.21/0.53    ( ! [X12,X11] : (k3_xboole_0(k2_xboole_0(X12,X11),X11) = X11) )),
% 0.21/0.53    inference(superposition,[],[f218,f113])).
% 0.21/0.53  fof(f1272,plain,(
% 0.21/0.53    spl2_48 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1100,f1080,f1269])).
% 0.21/0.53  fof(f1269,plain,(
% 0.21/0.53    spl2_48 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.21/0.53  fof(f1100,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f178,f1082])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X4,k2_xboole_0(X3,X4))) )),
% 0.21/0.53    inference(superposition,[],[f145,f111])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X10,X9] : (k2_xboole_0(X10,X9) = k2_xboole_0(k2_xboole_0(X10,X9),X9)) )),
% 0.21/0.53    inference(superposition,[],[f101,f113])).
% 0.21/0.53  fof(f1233,plain,(
% 0.21/0.53    spl2_47 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1097,f1080,f1230])).
% 0.21/0.53  fof(f1230,plain,(
% 0.21/0.53    spl2_47 <=> k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k5_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.21/0.53  fof(f1097,plain,(
% 0.21/0.53    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k5_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f153,f1082])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(X1,X2),X1) = k5_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 0.21/0.53    inference(superposition,[],[f130,f90])).
% 0.21/0.53  fof(f1228,plain,(
% 0.21/0.53    spl2_46 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1095,f1080,f1225])).
% 0.21/0.53  fof(f1225,plain,(
% 0.21/0.53    spl2_46 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.21/0.53  fof(f1095,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f145,f1082])).
% 0.21/0.53  fof(f1223,plain,(
% 0.21/0.53    spl2_45 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1092,f1080,f1220])).
% 0.21/0.53  fof(f1092,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f113,f1082])).
% 0.21/0.53  fof(f1205,plain,(
% 0.21/0.53    spl2_44 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1099,f1080,f1202])).
% 0.21/0.53  fof(f1202,plain,(
% 0.21/0.53    spl2_44 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.21/0.53  fof(f1099,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f163,f1082])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.21/0.53    inference(superposition,[],[f104,f111])).
% 0.21/0.53  fof(f1176,plain,(
% 0.21/0.53    spl2_43 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1094,f1080,f1173])).
% 0.21/0.53  fof(f1173,plain,(
% 0.21/0.53    spl2_43 <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.21/0.53  fof(f1094,plain,(
% 0.21/0.53    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f132,f1082])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f129,f128])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X1)) )),
% 0.21/0.53    inference(superposition,[],[f60,f90])).
% 0.21/0.53  fof(f1171,plain,(
% 0.21/0.53    spl2_42 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1091,f1080,f1168])).
% 0.21/0.53  fof(f1168,plain,(
% 0.21/0.53    spl2_42 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.21/0.53  fof(f1091,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f104,f1082])).
% 0.21/0.53  fof(f1143,plain,(
% 0.21/0.53    spl2_41 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1101,f1080,f1140])).
% 0.21/0.53  fof(f1140,plain,(
% 0.21/0.53    spl2_41 <=> sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.21/0.53  fof(f1101,plain,(
% 0.21/0.53    sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f333,f1082])).
% 0.21/0.53  fof(f1118,plain,(
% 0.21/0.53    spl2_40 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1093,f1080,f1115])).
% 0.21/0.53  fof(f1115,plain,(
% 0.21/0.53    spl2_40 <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.21/0.53  fof(f1093,plain,(
% 0.21/0.53    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f114,f1082])).
% 0.21/0.53  fof(f1113,plain,(
% 0.21/0.53    spl2_39 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1090,f1080,f1110])).
% 0.21/0.53  fof(f1110,plain,(
% 0.21/0.53    spl2_39 <=> sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.53  fof(f1090,plain,(
% 0.21/0.53    sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f90,f1082])).
% 0.21/0.53  fof(f1107,plain,(
% 0.21/0.53    spl2_38 | ~spl2_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f1089,f1080,f1104])).
% 0.21/0.53  fof(f1104,plain,(
% 0.21/0.53    spl2_38 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.21/0.53  fof(f1089,plain,(
% 0.21/0.53    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_37),
% 0.21/0.53    inference(superposition,[],[f53,f1082])).
% 0.21/0.53  fof(f1083,plain,(
% 0.21/0.53    spl2_37 | ~spl2_13 | ~spl2_36),
% 0.21/0.53    inference(avatar_split_clause,[],[f1076,f1072,f614,f1080])).
% 0.21/0.53  fof(f614,plain,(
% 0.21/0.53    spl2_13 <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.53  fof(f1072,plain,(
% 0.21/0.53    spl2_36 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.53  fof(f1076,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_13 | ~spl2_36)),
% 0.21/0.53    inference(superposition,[],[f1074,f616])).
% 0.21/0.53  fof(f616,plain,(
% 0.21/0.53    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f614])).
% 0.21/0.53  fof(f1074,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_36),
% 0.21/0.53    inference(avatar_component_clause,[],[f1072])).
% 0.21/0.53  fof(f1075,plain,(
% 0.21/0.53    spl2_36 | ~spl2_2 | ~spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f927,f81,f76,f1072])).
% 0.21/0.53  fof(f927,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 0.21/0.53    inference(resolution,[],[f800,f83])).
% 0.21/0.53  fof(f800,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_2),
% 0.21/0.53    inference(resolution,[],[f49,f78])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.53  fof(f1068,plain,(
% 0.21/0.53    ~spl2_35 | spl2_34),
% 0.21/0.53    inference(avatar_split_clause,[],[f1066,f984,f1061])).
% 0.21/0.53  fof(f1066,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_34),
% 0.21/0.53    inference(superposition,[],[f985,f99])).
% 0.21/0.53  fof(f1064,plain,(
% 0.21/0.53    spl2_35 | ~spl2_34),
% 0.21/0.53    inference(avatar_split_clause,[],[f1005,f984,f1061])).
% 0.21/0.53  fof(f1005,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_34),
% 0.21/0.53    inference(superposition,[],[f986,f99])).
% 0.21/0.53  fof(f986,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f984])).
% 0.21/0.53  fof(f1042,plain,(
% 0.21/0.53    spl2_33 | ~spl2_34),
% 0.21/0.53    inference(avatar_split_clause,[],[f1024,f984,f961])).
% 0.21/0.53  fof(f961,plain,(
% 0.21/0.53    spl2_33 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.53  fof(f1024,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_34),
% 0.21/0.53    inference(superposition,[],[f249,f986])).
% 0.21/0.53  fof(f249,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k2_xboole_0(k3_xboole_0(X8,X7),X7) = X7) )),
% 0.21/0.53    inference(superposition,[],[f178,f101])).
% 0.21/0.53  fof(f1028,plain,(
% 0.21/0.53    spl2_31 | ~spl2_34),
% 0.21/0.53    inference(avatar_split_clause,[],[f1011,f984,f937])).
% 0.21/0.53  fof(f1011,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_34),
% 0.21/0.53    inference(superposition,[],[f101,f986])).
% 0.21/0.53  fof(f1027,plain,(
% 0.21/0.53    spl2_31 | ~spl2_34),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1026])).
% 0.21/0.53  fof(f1026,plain,(
% 0.21/0.53    $false | (spl2_31 | ~spl2_34)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1011,f938])).
% 0.21/0.53  fof(f1004,plain,(
% 0.21/0.53    spl2_34 | ~spl2_32),
% 0.21/0.53    inference(avatar_split_clause,[],[f959,f955,f984])).
% 0.21/0.53  fof(f959,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_32),
% 0.21/0.53    inference(resolution,[],[f957,f61])).
% 0.21/0.53  fof(f957,plain,(
% 0.21/0.53    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_32),
% 0.21/0.53    inference(avatar_component_clause,[],[f955])).
% 0.21/0.53  fof(f989,plain,(
% 0.21/0.53    spl2_31 | ~spl2_33),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f988])).
% 0.21/0.53  fof(f988,plain,(
% 0.21/0.53    $false | (spl2_31 | ~spl2_33)),
% 0.21/0.53    inference(subsumption_resolution,[],[f938,f971])).
% 0.21/0.53  fof(f971,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_33),
% 0.21/0.53    inference(superposition,[],[f111,f963])).
% 0.21/0.53  fof(f963,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f961])).
% 0.21/0.53  fof(f987,plain,(
% 0.21/0.53    spl2_34 | ~spl2_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f944,f937,f984])).
% 0.21/0.53  fof(f944,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_31),
% 0.21/0.53    inference(superposition,[],[f113,f939])).
% 0.21/0.53  fof(f964,plain,(
% 0.21/0.53    spl2_33 | ~spl2_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f951,f937,f961])).
% 0.21/0.53  fof(f951,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_31),
% 0.21/0.53    inference(superposition,[],[f178,f939])).
% 0.21/0.53  fof(f958,plain,(
% 0.21/0.53    spl2_32 | ~spl2_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f945,f937,f955])).
% 0.21/0.53  fof(f945,plain,(
% 0.21/0.53    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_31),
% 0.21/0.53    inference(superposition,[],[f114,f939])).
% 0.21/0.53  fof(f940,plain,(
% 0.21/0.53    spl2_31 | ~spl2_13 | ~spl2_30),
% 0.21/0.53    inference(avatar_split_clause,[],[f934,f930,f614,f937])).
% 0.21/0.53  fof(f930,plain,(
% 0.21/0.53    spl2_30 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.53  fof(f934,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_13 | ~spl2_30)),
% 0.21/0.53    inference(superposition,[],[f932,f616])).
% 0.21/0.53  fof(f932,plain,(
% 0.21/0.53    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f930])).
% 0.21/0.53  fof(f933,plain,(
% 0.21/0.53    spl2_30 | ~spl2_2 | ~spl2_3 | ~spl2_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f928,f603,f81,f76,f930])).
% 0.21/0.53  fof(f928,plain,(
% 0.21/0.53    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_12)),
% 0.21/0.53    inference(forward_demodulation,[],[f927,f605])).
% 0.21/0.53  fof(f923,plain,(
% 0.21/0.53    spl2_29 | ~spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f704,f691,f920])).
% 0.21/0.53  fof(f920,plain,(
% 0.21/0.53    spl2_29 <=> k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.53  fof(f704,plain,(
% 0.21/0.53    k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_16),
% 0.21/0.53    inference(superposition,[],[f154,f693])).
% 0.21/0.53  fof(f901,plain,(
% 0.21/0.53    spl2_28 | ~spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f708,f691,f898])).
% 0.21/0.53  fof(f898,plain,(
% 0.21/0.53    spl2_28 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.53  fof(f708,plain,(
% 0.21/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_16),
% 0.21/0.53    inference(superposition,[],[f334,f693])).
% 0.21/0.53  fof(f875,plain,(
% 0.21/0.53    spl2_27 | ~spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f698,f691,f872])).
% 0.21/0.53  fof(f698,plain,(
% 0.21/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_16),
% 0.21/0.53    inference(superposition,[],[f113,f693])).
% 0.21/0.53  fof(f853,plain,(
% 0.21/0.53    spl2_26 | ~spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f706,f691,f850])).
% 0.21/0.53  fof(f850,plain,(
% 0.21/0.53    spl2_26 <=> u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.53  fof(f706,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_16),
% 0.21/0.53    inference(superposition,[],[f178,f693])).
% 0.21/0.53  fof(f835,plain,(
% 0.21/0.53    spl2_25 | ~spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f701,f691,f832])).
% 0.21/0.53  fof(f832,plain,(
% 0.21/0.53    spl2_25 <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.53  fof(f701,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_16),
% 0.21/0.53    inference(superposition,[],[f145,f693])).
% 0.21/0.53  fof(f830,plain,(
% 0.21/0.53    spl2_24 | ~spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f703,f691,f827])).
% 0.21/0.53  fof(f827,plain,(
% 0.21/0.53    spl2_24 <=> k4_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.53  fof(f703,plain,(
% 0.21/0.53    k4_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_16),
% 0.21/0.53    inference(superposition,[],[f153,f693])).
% 0.21/0.53  fof(f818,plain,(
% 0.21/0.53    spl2_23 | ~spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f700,f691,f815])).
% 0.21/0.53  fof(f815,plain,(
% 0.21/0.53    spl2_23 <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.53  fof(f700,plain,(
% 0.21/0.53    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,u1_struct_0(sK0)) | ~spl2_16),
% 0.21/0.53    inference(superposition,[],[f132,f693])).
% 0.21/0.53  fof(f799,plain,(
% 0.21/0.53    spl2_22 | ~spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f705,f691,f796])).
% 0.21/0.53  fof(f796,plain,(
% 0.21/0.53    spl2_22 <=> u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.53  fof(f705,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) | ~spl2_16),
% 0.21/0.53    inference(superposition,[],[f163,f693])).
% 1.47/0.53  fof(f777,plain,(
% 1.47/0.53    spl2_21 | ~spl2_16),
% 1.47/0.53    inference(avatar_split_clause,[],[f697,f691,f774])).
% 1.47/0.53  fof(f774,plain,(
% 1.47/0.53    spl2_21 <=> u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK1)),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.47/0.53  fof(f697,plain,(
% 1.47/0.53    u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_16),
% 1.47/0.53    inference(superposition,[],[f104,f693])).
% 1.47/0.53  fof(f771,plain,(
% 1.47/0.53    spl2_20 | ~spl2_16),
% 1.47/0.53    inference(avatar_split_clause,[],[f699,f691,f768])).
% 1.47/0.53  fof(f768,plain,(
% 1.47/0.53    spl2_20 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.47/0.53  fof(f699,plain,(
% 1.47/0.53    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_16),
% 1.47/0.53    inference(superposition,[],[f114,f693])).
% 1.47/0.53  fof(f743,plain,(
% 1.47/0.53    spl2_19 | ~spl2_16),
% 1.47/0.53    inference(avatar_split_clause,[],[f707,f691,f740])).
% 1.47/0.53  fof(f740,plain,(
% 1.47/0.53    spl2_19 <=> sK1 = k3_xboole_0(u1_struct_0(sK0),sK1)),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.47/0.53  fof(f707,plain,(
% 1.47/0.53    sK1 = k3_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_16),
% 1.47/0.53    inference(superposition,[],[f333,f693])).
% 1.47/0.53  fof(f719,plain,(
% 1.47/0.53    spl2_18 | ~spl2_16),
% 1.47/0.53    inference(avatar_split_clause,[],[f696,f691,f716])).
% 1.47/0.53  fof(f716,plain,(
% 1.47/0.53    spl2_18 <=> sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.47/0.53  fof(f696,plain,(
% 1.47/0.53    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) | ~spl2_16),
% 1.47/0.53    inference(superposition,[],[f90,f693])).
% 1.47/0.53  fof(f713,plain,(
% 1.47/0.53    spl2_17 | ~spl2_16),
% 1.47/0.53    inference(avatar_split_clause,[],[f695,f691,f710])).
% 1.47/0.53  fof(f710,plain,(
% 1.47/0.53    spl2_17 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.47/0.53  fof(f695,plain,(
% 1.47/0.53    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_16),
% 1.47/0.53    inference(superposition,[],[f53,f693])).
% 1.47/0.53  fof(f694,plain,(
% 1.47/0.53    spl2_16 | ~spl2_3 | ~spl2_8),
% 1.47/0.53    inference(avatar_split_clause,[],[f689,f470,f81,f691])).
% 1.47/0.53  fof(f470,plain,(
% 1.47/0.53    spl2_8 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.47/0.53  fof(f689,plain,(
% 1.47/0.53    u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_3 | ~spl2_8)),
% 1.47/0.53    inference(forward_demodulation,[],[f688,f472])).
% 1.47/0.53  fof(f472,plain,(
% 1.47/0.53    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_8),
% 1.47/0.53    inference(avatar_component_clause,[],[f470])).
% 1.47/0.53  fof(f688,plain,(
% 1.47/0.53    k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_3),
% 1.47/0.53    inference(resolution,[],[f578,f83])).
% 1.47/0.53  fof(f578,plain,(
% 1.47/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X1)) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X1))) ) | ~spl2_3),
% 1.47/0.53    inference(resolution,[],[f576,f62])).
% 1.47/0.53  fof(f576,plain,(
% 1.47/0.53    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X9) = k2_xboole_0(sK1,X9)) ) | ~spl2_3),
% 1.47/0.53    inference(resolution,[],[f67,f83])).
% 1.47/0.53  fof(f684,plain,(
% 1.47/0.53    spl2_15 | ~spl2_2 | ~spl2_3),
% 1.47/0.53    inference(avatar_split_clause,[],[f679,f81,f76,f681])).
% 1.47/0.53  fof(f681,plain,(
% 1.47/0.53    spl2_15 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.47/0.53  fof(f679,plain,(
% 1.47/0.53    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3)),
% 1.47/0.53    inference(resolution,[],[f558,f83])).
% 1.47/0.53  fof(f558,plain,(
% 1.47/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0)))) ) | ~spl2_2),
% 1.47/0.53    inference(resolution,[],[f557,f69])).
% 1.47/0.53  fof(f557,plain,(
% 1.47/0.53    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_2),
% 1.47/0.53    inference(resolution,[],[f65,f78])).
% 1.47/0.53  fof(f65,plain,(
% 1.47/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.47/0.53    inference(cnf_transformation,[],[f34])).
% 1.47/0.53  fof(f34,plain,(
% 1.47/0.53    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.47/0.53    inference(flattening,[],[f33])).
% 1.47/0.53  fof(f33,plain,(
% 1.47/0.53    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.47/0.53    inference(ennf_transformation,[],[f16])).
% 1.47/0.53  fof(f16,axiom,(
% 1.47/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.47/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.47/0.53  fof(f630,plain,(
% 1.47/0.53    spl2_14 | ~spl2_3),
% 1.47/0.53    inference(avatar_split_clause,[],[f625,f81,f627])).
% 1.47/0.53  fof(f627,plain,(
% 1.47/0.53    spl2_14 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.47/0.53  fof(f625,plain,(
% 1.47/0.53    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_3),
% 1.47/0.53    inference(resolution,[],[f466,f83])).
% 1.47/0.53  fof(f617,plain,(
% 1.47/0.53    spl2_13 | ~spl2_2 | ~spl2_3),
% 1.47/0.53    inference(avatar_split_clause,[],[f612,f81,f76,f614])).
% 1.47/0.53  fof(f612,plain,(
% 1.47/0.53    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 1.47/0.53    inference(resolution,[],[f579,f83])).
% 1.47/0.53  fof(f579,plain,(
% 1.47/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2))) ) | (~spl2_2 | ~spl2_3)),
% 1.47/0.53    inference(resolution,[],[f576,f557])).
% 1.47/0.53  fof(f606,plain,(
% 1.47/0.53    spl2_12 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 1.47/0.53    inference(avatar_split_clause,[],[f601,f413,f81,f76,f603])).
% 1.47/0.53  fof(f601,plain,(
% 1.47/0.53    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 1.47/0.53    inference(subsumption_resolution,[],[f600,f83])).
% 1.47/0.53  fof(f600,plain,(
% 1.47/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_4)),
% 1.47/0.53    inference(resolution,[],[f415,f560])).
% 1.47/0.53  fof(f560,plain,(
% 1.47/0.53    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_2),
% 1.47/0.53    inference(resolution,[],[f51,f78])).
% 1.47/0.53  fof(f51,plain,(
% 1.47/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 1.47/0.53    inference(cnf_transformation,[],[f27])).
% 1.47/0.53  fof(f415,plain,(
% 1.47/0.53    v4_pre_topc(sK1,sK0) | ~spl2_4),
% 1.47/0.53    inference(avatar_component_clause,[],[f413])).
% 1.47/0.53  fof(f599,plain,(
% 1.47/0.53    spl2_11 | ~spl2_7),
% 1.47/0.53    inference(avatar_split_clause,[],[f594,f460,f596])).
% 1.47/0.53  fof(f596,plain,(
% 1.47/0.53    spl2_11 <=> k2_tops_1(sK0,sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.47/0.53  fof(f594,plain,(
% 1.47/0.53    k2_tops_1(sK0,sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_7),
% 1.47/0.53    inference(forward_demodulation,[],[f593,f92])).
% 1.47/0.53  fof(f92,plain,(
% 1.47/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.47/0.53    inference(superposition,[],[f57,f91])).
% 1.47/0.53  fof(f593,plain,(
% 1.47/0.53    k4_subset_1(sK1,k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_7),
% 1.47/0.53    inference(resolution,[],[f574,f462])).
% 1.47/0.53  fof(f574,plain,(
% 1.47/0.53    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(sK1)) | k4_subset_1(sK1,k2_tops_1(sK0,sK1),X6) = k2_xboole_0(k2_tops_1(sK0,sK1),X6)) ) | ~spl2_7),
% 1.47/0.53    inference(resolution,[],[f67,f462])).
% 1.47/0.53  fof(f586,plain,(
% 1.47/0.53    spl2_10 | ~spl2_3),
% 1.47/0.53    inference(avatar_split_clause,[],[f581,f81,f583])).
% 1.47/0.53  fof(f583,plain,(
% 1.47/0.53    spl2_10 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.47/0.53  fof(f581,plain,(
% 1.47/0.53    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) | ~spl2_3),
% 1.47/0.53    inference(forward_demodulation,[],[f580,f92])).
% 1.47/0.53  fof(f580,plain,(
% 1.47/0.53    k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) | ~spl2_3),
% 1.47/0.53    inference(resolution,[],[f576,f83])).
% 1.47/0.53  fof(f478,plain,(
% 1.47/0.53    spl2_9 | ~spl2_7),
% 1.47/0.53    inference(avatar_split_clause,[],[f467,f460,f475])).
% 1.47/0.53  fof(f467,plain,(
% 1.47/0.53    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_7),
% 1.47/0.53    inference(resolution,[],[f69,f462])).
% 1.47/0.53  fof(f473,plain,(
% 1.47/0.53    spl2_8 | ~spl2_3),
% 1.47/0.53    inference(avatar_split_clause,[],[f468,f81,f470])).
% 1.47/0.53  fof(f468,plain,(
% 1.47/0.53    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_3),
% 1.47/0.53    inference(resolution,[],[f69,f83])).
% 1.47/0.53  fof(f463,plain,(
% 1.47/0.53    spl2_7 | ~spl2_6),
% 1.47/0.53    inference(avatar_split_clause,[],[f458,f454,f460])).
% 1.47/0.53  fof(f454,plain,(
% 1.47/0.53    spl2_6 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.47/0.53  fof(f458,plain,(
% 1.47/0.53    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_6),
% 1.47/0.53    inference(superposition,[],[f68,f456])).
% 1.47/0.53  fof(f456,plain,(
% 1.47/0.53    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 1.47/0.53    inference(avatar_component_clause,[],[f454])).
% 1.47/0.53  fof(f68,plain,(
% 1.47/0.53    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.47/0.53    inference(forward_demodulation,[],[f54,f55])).
% 1.47/0.53  fof(f55,plain,(
% 1.47/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.47/0.53    inference(cnf_transformation,[],[f11])).
% 1.47/0.53  fof(f11,axiom,(
% 1.47/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.47/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.47/0.53  fof(f54,plain,(
% 1.47/0.53    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.47/0.53    inference(cnf_transformation,[],[f9])).
% 1.47/0.53  fof(f9,axiom,(
% 1.47/0.53    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.47/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.47/0.53  fof(f457,plain,(
% 1.47/0.53    spl2_6 | ~spl2_3 | ~spl2_5),
% 1.47/0.53    inference(avatar_split_clause,[],[f451,f417,f81,f454])).
% 1.47/0.53  fof(f417,plain,(
% 1.47/0.53    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.47/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.47/0.53  fof(f451,plain,(
% 1.47/0.53    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_5)),
% 1.47/0.53    inference(superposition,[],[f448,f419])).
% 1.47/0.53  fof(f419,plain,(
% 1.47/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 1.47/0.53    inference(avatar_component_clause,[],[f417])).
% 1.47/0.53  fof(f448,plain,(
% 1.47/0.53    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl2_3),
% 1.47/0.53    inference(resolution,[],[f66,f83])).
% 1.47/0.53  fof(f66,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.47/0.53    inference(cnf_transformation,[],[f35])).
% 1.47/0.53  fof(f35,plain,(
% 1.47/0.53    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.53    inference(ennf_transformation,[],[f12])).
% 1.47/0.53  fof(f12,axiom,(
% 1.47/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.47/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.47/0.53  fof(f421,plain,(
% 1.47/0.53    ~spl2_4 | ~spl2_5),
% 1.47/0.53    inference(avatar_split_clause,[],[f47,f417,f413])).
% 1.47/0.53  fof(f47,plain,(
% 1.47/0.53    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.47/0.53    inference(cnf_transformation,[],[f42])).
% 1.47/0.53  fof(f42,plain,(
% 1.47/0.53    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.47/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 1.47/0.53  fof(f40,plain,(
% 1.47/0.53    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.47/0.53    introduced(choice_axiom,[])).
% 1.47/0.53  fof(f41,plain,(
% 1.47/0.53    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.47/0.53    introduced(choice_axiom,[])).
% 1.47/0.53  fof(f39,plain,(
% 1.47/0.53    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.47/0.53    inference(flattening,[],[f38])).
% 1.47/0.53  fof(f38,plain,(
% 1.47/0.53    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.47/0.53    inference(nnf_transformation,[],[f23])).
% 1.47/0.53  fof(f23,plain,(
% 1.47/0.53    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.47/0.53    inference(flattening,[],[f22])).
% 1.47/0.53  fof(f22,plain,(
% 1.47/0.53    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.47/0.53    inference(ennf_transformation,[],[f21])).
% 1.47/0.53  fof(f21,negated_conjecture,(
% 1.47/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.47/0.53    inference(negated_conjecture,[],[f20])).
% 1.47/0.53  fof(f20,conjecture,(
% 1.47/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.47/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 1.47/0.53  fof(f420,plain,(
% 1.47/0.53    spl2_4 | spl2_5),
% 1.47/0.53    inference(avatar_split_clause,[],[f46,f417,f413])).
% 1.47/0.53  fof(f46,plain,(
% 1.47/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.47/0.53    inference(cnf_transformation,[],[f42])).
% 1.47/0.53  fof(f84,plain,(
% 1.47/0.53    spl2_3),
% 1.47/0.53    inference(avatar_split_clause,[],[f45,f81])).
% 1.47/0.53  fof(f45,plain,(
% 1.47/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.53    inference(cnf_transformation,[],[f42])).
% 1.47/0.53  fof(f79,plain,(
% 1.47/0.53    spl2_2),
% 1.47/0.53    inference(avatar_split_clause,[],[f44,f76])).
% 1.47/0.53  fof(f44,plain,(
% 1.47/0.53    l1_pre_topc(sK0)),
% 1.47/0.53    inference(cnf_transformation,[],[f42])).
% 1.47/0.53  fof(f74,plain,(
% 1.47/0.53    spl2_1),
% 1.47/0.53    inference(avatar_split_clause,[],[f43,f71])).
% 1.47/0.53  fof(f43,plain,(
% 1.47/0.53    v2_pre_topc(sK0)),
% 1.47/0.53    inference(cnf_transformation,[],[f42])).
% 1.47/0.53  % SZS output end Proof for theBenchmark
% 1.47/0.53  % (30248)------------------------------
% 1.47/0.53  % (30248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.53  % (30248)Termination reason: Refutation
% 1.47/0.53  
% 1.47/0.53  % (30248)Memory used [KB]: 7036
% 1.47/0.53  % (30248)Time elapsed: 0.123 s
% 1.47/0.53  % (30248)------------------------------
% 1.47/0.53  % (30248)------------------------------
% 1.47/0.54  % (30247)Success in time 0.184 s
%------------------------------------------------------------------------------
