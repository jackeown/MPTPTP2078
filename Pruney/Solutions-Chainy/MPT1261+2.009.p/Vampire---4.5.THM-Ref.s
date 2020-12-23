%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:48 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 300 expanded)
%              Number of leaves         :   33 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  472 ( 945 expanded)
%              Number of equality atoms :  104 ( 231 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1598,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f95,f100,f105,f110,f1194,f1203,f1250,f1304,f1316,f1331,f1372,f1487,f1488,f1507,f1516,f1521,f1597])).

fof(f1597,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_40 ),
    inference(avatar_contradiction_clause,[],[f1596])).

fof(f1596,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_40 ),
    inference(subsumption_resolution,[],[f1595,f104])).

fof(f104,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1595,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_40 ),
    inference(subsumption_resolution,[],[f1593,f99])).

fof(f99,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1593,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_40 ),
    inference(trivial_inequality_removal,[],[f1591])).

fof(f1591,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_40 ),
    inference(superposition,[],[f1347,f272])).

fof(f272,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f59,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1347,plain,
    ( k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_40 ),
    inference(avatar_component_clause,[],[f1346])).

fof(f1346,plain,
    ( spl2_40
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f1521,plain,
    ( ~ spl2_40
    | ~ spl2_20
    | spl2_37 ),
    inference(avatar_split_clause,[],[f1520,f1301,f261,f1346])).

fof(f261,plain,
    ( spl2_20
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f1301,plain,
    ( spl2_37
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f1520,plain,
    ( k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_20
    | spl2_37 ),
    inference(subsumption_resolution,[],[f1519,f263])).

fof(f263,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f261])).

fof(f1519,plain,
    ( k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_37 ),
    inference(superposition,[],[f1302,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1302,plain,
    ( k1_tops_1(sK0,sK1) != k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | spl2_37 ),
    inference(avatar_component_clause,[],[f1301])).

fof(f1516,plain,
    ( ~ spl2_15
    | spl2_20 ),
    inference(avatar_contradiction_clause,[],[f1515])).

fof(f1515,plain,
    ( $false
    | ~ spl2_15
    | spl2_20 ),
    inference(subsumption_resolution,[],[f1513,f211])).

fof(f211,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl2_15
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f1513,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_20 ),
    inference(resolution,[],[f262,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f262,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_20 ),
    inference(avatar_component_clause,[],[f261])).

fof(f1507,plain,
    ( ~ spl2_12
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f1506,f97,f91,f177])).

fof(f177,plain,
    ( spl2_12
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f91,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1506,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1505,f99])).

fof(f1505,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(superposition,[],[f93,f59])).

fof(f93,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f1488,plain,
    ( ~ spl2_20
    | spl2_12
    | ~ spl2_32
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1479,f1301,f1277,f177,f261])).

fof(f1277,plain,
    ( spl2_32
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f1479,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_32
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f1337,f1278])).

fof(f1278,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f1337,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f168,f1303])).

fof(f1303,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f1301])).

fof(f168,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f70,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1487,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1486,f1369,f102,f97,f231])).

fof(f231,plain,
    ( spl2_18
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f1369,plain,
    ( spl2_42
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f1486,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_42 ),
    inference(subsumption_resolution,[],[f1485,f104])).

fof(f1485,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_42 ),
    inference(subsumption_resolution,[],[f1437,f99])).

fof(f1437,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_42 ),
    inference(superposition,[],[f1371,f279])).

fof(f279,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f278,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f278,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f63,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f1371,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f1369])).

fof(f1372,plain,
    ( ~ spl2_32
    | spl2_42
    | ~ spl2_20
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1367,f1301,f261,f1369,f1277])).

fof(f1367,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_20
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f1366,f294])).

fof(f294,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f125,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f125,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f78,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1366,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_20
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f1343,f263])).

fof(f1343,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_37 ),
    inference(superposition,[],[f459,f1303])).

fof(f459,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(k3_subset_1(X5,X4),k1_zfmisc_1(X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | k2_xboole_0(X4,X5) = X5 ) ),
    inference(superposition,[],[f77,f245])).

fof(f245,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f186,f66])).

fof(f186,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f76,f82])).

fof(f82,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f1331,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_32 ),
    inference(avatar_contradiction_clause,[],[f1330])).

fof(f1330,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_32 ),
    inference(subsumption_resolution,[],[f1329,f104])).

fof(f1329,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_32 ),
    inference(subsumption_resolution,[],[f1325,f99])).

fof(f1325,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_32 ),
    inference(resolution,[],[f1279,f407])).

fof(f407,plain,(
    ! [X8,X9] :
      ( m1_subset_1(k1_tops_1(X9,X8),k1_zfmisc_1(X8))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ l1_pre_topc(X9) ) ),
    inference(superposition,[],[f120,f272])).

fof(f120,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f81,f75])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f81,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f1279,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_32 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f1316,plain,
    ( spl2_20
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f1261,f177,f261])).

fof(f1261,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_12 ),
    inference(superposition,[],[f120,f179])).

fof(f179,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1304,plain,
    ( ~ spl2_32
    | spl2_37
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f1265,f177,f1301,f1277])).

fof(f1265,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_12 ),
    inference(superposition,[],[f171,f179])).

fof(f171,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f69,f70])).

fof(f1250,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f1249,f97,f91,f177])).

fof(f1249,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1246,f99])).

fof(f1246,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f59,f92])).

fof(f92,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f1203,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f1202,f102,f97,f87,f209])).

fof(f87,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1202,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f204,f104])).

fof(f204,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f62,f99])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f1194,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f1193,f231,f107,f102,f97,f87])).

fof(f107,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1193,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f1192,f104])).

fof(f1192,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f1191,f99])).

fof(f1191,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f269,f109])).

fof(f109,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f269,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_18 ),
    inference(trivial_inequality_removal,[],[f268])).

fof(f268,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_18 ),
    inference(superposition,[],[f65,f233])).

fof(f233,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f231])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f110,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f51,f107])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f105,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f52,f102])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f53,f97])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f54,f91,f87])).

fof(f54,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f55,f91,f87])).

fof(f55,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:36:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (25575)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (25592)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (25582)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (25592)Refutation not found, incomplete strategy% (25592)------------------------------
% 0.21/0.54  % (25592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25580)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (25592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25592)Memory used [KB]: 10618
% 0.21/0.54  % (25592)Time elapsed: 0.112 s
% 0.21/0.54  % (25592)------------------------------
% 0.21/0.54  % (25592)------------------------------
% 0.21/0.54  % (25579)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (25576)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (25587)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (25604)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (25585)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (25585)Refutation not found, incomplete strategy% (25585)------------------------------
% 0.21/0.55  % (25585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25585)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25585)Memory used [KB]: 10746
% 0.21/0.55  % (25585)Time elapsed: 0.126 s
% 0.21/0.55  % (25585)------------------------------
% 0.21/0.55  % (25585)------------------------------
% 0.21/0.55  % (25596)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (25603)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (25602)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (25601)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (25578)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (25577)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.56  % (25595)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (25584)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (25588)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (25600)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (25586)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.55/0.57  % (25605)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.55/0.57  % (25604)Refutation not found, incomplete strategy% (25604)------------------------------
% 1.55/0.57  % (25604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (25604)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (25604)Memory used [KB]: 10874
% 1.55/0.57  % (25604)Time elapsed: 0.149 s
% 1.55/0.57  % (25604)------------------------------
% 1.55/0.57  % (25604)------------------------------
% 1.55/0.57  % (25598)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.55/0.57  % (25594)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.57  % (25591)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.57  % (25599)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.55/0.57  % (25593)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.55/0.58  % (25597)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.55/0.58  % (25581)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.58  % (25589)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.58  % (25583)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.10/0.68  % (25626)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.10/0.68  % (25597)Refutation found. Thanks to Tanya!
% 2.10/0.68  % SZS status Theorem for theBenchmark
% 2.10/0.68  % SZS output start Proof for theBenchmark
% 2.10/0.68  fof(f1598,plain,(
% 2.10/0.68    $false),
% 2.10/0.68    inference(avatar_sat_refutation,[],[f94,f95,f100,f105,f110,f1194,f1203,f1250,f1304,f1316,f1331,f1372,f1487,f1488,f1507,f1516,f1521,f1597])).
% 2.10/0.68  fof(f1597,plain,(
% 2.10/0.68    ~spl2_3 | ~spl2_4 | spl2_40),
% 2.10/0.68    inference(avatar_contradiction_clause,[],[f1596])).
% 2.10/0.68  fof(f1596,plain,(
% 2.10/0.68    $false | (~spl2_3 | ~spl2_4 | spl2_40)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1595,f104])).
% 2.10/0.68  fof(f104,plain,(
% 2.10/0.68    l1_pre_topc(sK0) | ~spl2_4),
% 2.10/0.68    inference(avatar_component_clause,[],[f102])).
% 2.10/0.68  fof(f102,plain,(
% 2.10/0.68    spl2_4 <=> l1_pre_topc(sK0)),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.10/0.68  fof(f1595,plain,(
% 2.10/0.68    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_40)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1593,f99])).
% 2.10/0.68  fof(f99,plain,(
% 2.10/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.10/0.68    inference(avatar_component_clause,[],[f97])).
% 2.10/0.68  fof(f97,plain,(
% 2.10/0.68    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.10/0.68  fof(f1593,plain,(
% 2.10/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_40),
% 2.10/0.68    inference(trivial_inequality_removal,[],[f1591])).
% 2.10/0.68  fof(f1591,plain,(
% 2.10/0.68    k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_40),
% 2.10/0.68    inference(superposition,[],[f1347,f272])).
% 2.10/0.68  fof(f272,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.10/0.68    inference(duplicate_literal_removal,[],[f271])).
% 2.10/0.68  fof(f271,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.10/0.68    inference(superposition,[],[f59,f60])).
% 2.10/0.68  fof(f60,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f29])).
% 2.10/0.68  fof(f29,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.68    inference(ennf_transformation,[],[f23])).
% 2.10/0.68  fof(f23,axiom,(
% 2.10/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.10/0.68  fof(f59,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(cnf_transformation,[],[f28])).
% 2.10/0.68  fof(f28,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f15])).
% 2.10/0.68  fof(f15,axiom,(
% 2.10/0.68    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.10/0.68  fof(f1347,plain,(
% 2.10/0.68    k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_40),
% 2.10/0.68    inference(avatar_component_clause,[],[f1346])).
% 2.10/0.68  fof(f1346,plain,(
% 2.10/0.68    spl2_40 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 2.10/0.68  fof(f1521,plain,(
% 2.10/0.68    ~spl2_40 | ~spl2_20 | spl2_37),
% 2.10/0.68    inference(avatar_split_clause,[],[f1520,f1301,f261,f1346])).
% 2.10/0.68  fof(f261,plain,(
% 2.10/0.68    spl2_20 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 2.10/0.68  fof(f1301,plain,(
% 2.10/0.68    spl2_37 <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 2.10/0.68  fof(f1520,plain,(
% 2.10/0.68    k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_20 | spl2_37)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1519,f263])).
% 2.10/0.68  fof(f263,plain,(
% 2.10/0.68    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_20),
% 2.10/0.68    inference(avatar_component_clause,[],[f261])).
% 2.10/0.68  fof(f1519,plain,(
% 2.10/0.68    k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_37),
% 2.10/0.68    inference(superposition,[],[f1302,f70])).
% 2.10/0.68  fof(f70,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(cnf_transformation,[],[f40])).
% 2.10/0.68  fof(f40,plain,(
% 2.10/0.68    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f10])).
% 2.10/0.68  fof(f10,axiom,(
% 2.10/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.10/0.68  fof(f1302,plain,(
% 2.10/0.68    k1_tops_1(sK0,sK1) != k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | spl2_37),
% 2.10/0.68    inference(avatar_component_clause,[],[f1301])).
% 2.10/0.68  fof(f1516,plain,(
% 2.10/0.68    ~spl2_15 | spl2_20),
% 2.10/0.68    inference(avatar_contradiction_clause,[],[f1515])).
% 2.10/0.68  fof(f1515,plain,(
% 2.10/0.68    $false | (~spl2_15 | spl2_20)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1513,f211])).
% 2.10/0.68  fof(f211,plain,(
% 2.10/0.68    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_15),
% 2.10/0.68    inference(avatar_component_clause,[],[f209])).
% 2.10/0.68  fof(f209,plain,(
% 2.10/0.68    spl2_15 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 2.10/0.68  fof(f1513,plain,(
% 2.10/0.68    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_20),
% 2.10/0.68    inference(resolution,[],[f262,f68])).
% 2.10/0.68  fof(f68,plain,(
% 2.10/0.68    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f49])).
% 2.10/0.68  fof(f49,plain,(
% 2.10/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.10/0.68    inference(nnf_transformation,[],[f18])).
% 2.10/0.68  fof(f18,axiom,(
% 2.10/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.10/0.68  fof(f262,plain,(
% 2.10/0.68    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_20),
% 2.10/0.68    inference(avatar_component_clause,[],[f261])).
% 2.10/0.68  fof(f1507,plain,(
% 2.10/0.68    ~spl2_12 | spl2_2 | ~spl2_3),
% 2.10/0.68    inference(avatar_split_clause,[],[f1506,f97,f91,f177])).
% 2.10/0.68  fof(f177,plain,(
% 2.10/0.68    spl2_12 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 2.10/0.68  fof(f91,plain,(
% 2.10/0.68    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.10/0.68  fof(f1506,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (spl2_2 | ~spl2_3)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1505,f99])).
% 2.10/0.68  fof(f1505,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 2.10/0.68    inference(superposition,[],[f93,f59])).
% 2.10/0.68  fof(f93,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 2.10/0.68    inference(avatar_component_clause,[],[f91])).
% 2.10/0.68  fof(f1488,plain,(
% 2.10/0.68    ~spl2_20 | spl2_12 | ~spl2_32 | ~spl2_37),
% 2.10/0.68    inference(avatar_split_clause,[],[f1479,f1301,f1277,f177,f261])).
% 2.10/0.68  fof(f1277,plain,(
% 2.10/0.68    spl2_32 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 2.10/0.68  fof(f1479,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_32 | ~spl2_37)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1337,f1278])).
% 2.10/0.68  fof(f1278,plain,(
% 2.10/0.68    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_32),
% 2.10/0.68    inference(avatar_component_clause,[],[f1277])).
% 2.10/0.68  fof(f1337,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_37),
% 2.10/0.68    inference(superposition,[],[f168,f1303])).
% 2.10/0.68  fof(f1303,plain,(
% 2.10/0.68    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_37),
% 2.10/0.68    inference(avatar_component_clause,[],[f1301])).
% 2.10/0.68  fof(f168,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(superposition,[],[f70,f69])).
% 2.10/0.68  fof(f69,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(cnf_transformation,[],[f39])).
% 2.10/0.68  fof(f39,plain,(
% 2.10/0.68    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f12])).
% 2.10/0.68  fof(f12,axiom,(
% 2.10/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.10/0.68  fof(f1487,plain,(
% 2.10/0.68    spl2_18 | ~spl2_3 | ~spl2_4 | ~spl2_42),
% 2.10/0.68    inference(avatar_split_clause,[],[f1486,f1369,f102,f97,f231])).
% 2.10/0.68  fof(f231,plain,(
% 2.10/0.68    spl2_18 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.10/0.68  fof(f1369,plain,(
% 2.10/0.68    spl2_42 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 2.10/0.68  fof(f1486,plain,(
% 2.10/0.68    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_42)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1485,f104])).
% 2.10/0.68  fof(f1485,plain,(
% 2.10/0.68    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_42)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1437,f99])).
% 2.10/0.68  fof(f1437,plain,(
% 2.10/0.68    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_42),
% 2.10/0.68    inference(superposition,[],[f1371,f279])).
% 2.10/0.68  fof(f279,plain,(
% 2.10/0.68    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.10/0.68    inference(subsumption_resolution,[],[f278,f61])).
% 2.10/0.68  fof(f61,plain,(
% 2.10/0.68    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f31])).
% 2.10/0.68  fof(f31,plain,(
% 2.10/0.68    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.10/0.68    inference(flattening,[],[f30])).
% 2.10/0.68  fof(f30,plain,(
% 2.10/0.68    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f20])).
% 2.10/0.68  fof(f20,axiom,(
% 2.10/0.68    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.10/0.68  fof(f278,plain,(
% 2.10/0.68    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.10/0.68    inference(duplicate_literal_removal,[],[f275])).
% 2.10/0.68  fof(f275,plain,(
% 2.10/0.68    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.10/0.68    inference(superposition,[],[f63,f66])).
% 2.10/0.68  fof(f66,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(cnf_transformation,[],[f38])).
% 2.10/0.68  fof(f38,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.68    inference(flattening,[],[f37])).
% 2.10/0.68  fof(f37,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.10/0.68    inference(ennf_transformation,[],[f13])).
% 2.10/0.68  fof(f13,axiom,(
% 2.10/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.10/0.68  fof(f63,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f34])).
% 2.10/0.68  fof(f34,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.68    inference(ennf_transformation,[],[f21])).
% 2.10/0.68  fof(f21,axiom,(
% 2.10/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.10/0.68  fof(f1371,plain,(
% 2.10/0.68    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_42),
% 2.10/0.68    inference(avatar_component_clause,[],[f1369])).
% 2.10/0.68  fof(f1372,plain,(
% 2.10/0.68    ~spl2_32 | spl2_42 | ~spl2_20 | ~spl2_37),
% 2.10/0.68    inference(avatar_split_clause,[],[f1367,f1301,f261,f1369,f1277])).
% 2.10/0.68  fof(f1367,plain,(
% 2.10/0.68    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_20 | ~spl2_37)),
% 2.10/0.68    inference(forward_demodulation,[],[f1366,f294])).
% 2.10/0.68  fof(f294,plain,(
% 2.10/0.68    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 2.10/0.68    inference(superposition,[],[f125,f78])).
% 2.10/0.68  fof(f78,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.10/0.68    inference(cnf_transformation,[],[f8])).
% 2.10/0.68  fof(f8,axiom,(
% 2.10/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.10/0.68  fof(f125,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 2.10/0.68    inference(superposition,[],[f78,f83])).
% 2.10/0.68  fof(f83,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f7])).
% 2.10/0.68  fof(f7,axiom,(
% 2.10/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.10/0.68  fof(f1366,plain,(
% 2.10/0.68    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | (~spl2_20 | ~spl2_37)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1343,f263])).
% 2.10/0.68  fof(f1343,plain,(
% 2.10/0.68    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_37),
% 2.10/0.68    inference(superposition,[],[f459,f1303])).
% 2.10/0.68  fof(f459,plain,(
% 2.10/0.68    ( ! [X4,X5] : (~m1_subset_1(k3_subset_1(X5,X4),k1_zfmisc_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(X5)) | k2_xboole_0(X4,X5) = X5) )),
% 2.10/0.68    inference(superposition,[],[f77,f245])).
% 2.10/0.68  fof(f245,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(duplicate_literal_removal,[],[f244])).
% 2.10/0.68  fof(f244,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(superposition,[],[f186,f66])).
% 2.10/0.68  fof(f186,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(forward_demodulation,[],[f76,f82])).
% 2.10/0.68  fof(f82,plain,(
% 2.10/0.68    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.10/0.68    inference(cnf_transformation,[],[f9])).
% 2.10/0.68  fof(f9,axiom,(
% 2.10/0.68    ! [X0] : k2_subset_1(X0) = X0),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.10/0.68  fof(f76,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(cnf_transformation,[],[f41])).
% 2.10/0.68  fof(f41,plain,(
% 2.10/0.68    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f16])).
% 2.10/0.68  fof(f16,axiom,(
% 2.10/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 2.10/0.68  fof(f77,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.10/0.68    inference(cnf_transformation,[],[f6])).
% 2.10/0.68  fof(f6,axiom,(
% 2.10/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 2.10/0.68  fof(f1331,plain,(
% 2.10/0.68    ~spl2_3 | ~spl2_4 | spl2_32),
% 2.10/0.68    inference(avatar_contradiction_clause,[],[f1330])).
% 2.10/0.68  fof(f1330,plain,(
% 2.10/0.68    $false | (~spl2_3 | ~spl2_4 | spl2_32)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1329,f104])).
% 2.10/0.68  fof(f1329,plain,(
% 2.10/0.68    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_32)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1325,f99])).
% 2.10/0.68  fof(f1325,plain,(
% 2.10/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_32),
% 2.10/0.68    inference(resolution,[],[f1279,f407])).
% 2.10/0.68  fof(f407,plain,(
% 2.10/0.68    ( ! [X8,X9] : (m1_subset_1(k1_tops_1(X9,X8),k1_zfmisc_1(X8)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) | ~l1_pre_topc(X9)) )),
% 2.10/0.68    inference(superposition,[],[f120,f272])).
% 2.10/0.68  fof(f120,plain,(
% 2.10/0.68    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(backward_demodulation,[],[f81,f75])).
% 2.10/0.68  fof(f75,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f14])).
% 2.10/0.68  fof(f14,axiom,(
% 2.10/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.10/0.68  fof(f81,plain,(
% 2.10/0.68    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(cnf_transformation,[],[f11])).
% 2.10/0.68  fof(f11,axiom,(
% 2.10/0.68    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.10/0.68  fof(f1279,plain,(
% 2.10/0.68    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_32),
% 2.10/0.68    inference(avatar_component_clause,[],[f1277])).
% 2.10/0.68  fof(f1316,plain,(
% 2.10/0.68    spl2_20 | ~spl2_12),
% 2.10/0.68    inference(avatar_split_clause,[],[f1261,f177,f261])).
% 2.10/0.68  fof(f1261,plain,(
% 2.10/0.68    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_12),
% 2.10/0.68    inference(superposition,[],[f120,f179])).
% 2.10/0.68  fof(f179,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_12),
% 2.10/0.68    inference(avatar_component_clause,[],[f177])).
% 2.10/0.68  fof(f1304,plain,(
% 2.10/0.68    ~spl2_32 | spl2_37 | ~spl2_12),
% 2.10/0.68    inference(avatar_split_clause,[],[f1265,f177,f1301,f1277])).
% 2.10/0.68  fof(f1265,plain,(
% 2.10/0.68    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_12),
% 2.10/0.68    inference(superposition,[],[f171,f179])).
% 2.10/0.68  fof(f171,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(duplicate_literal_removal,[],[f169])).
% 2.10/0.68  fof(f169,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.68    inference(superposition,[],[f69,f70])).
% 2.10/0.68  fof(f1250,plain,(
% 2.10/0.68    spl2_12 | ~spl2_2 | ~spl2_3),
% 2.10/0.68    inference(avatar_split_clause,[],[f1249,f97,f91,f177])).
% 2.10/0.68  fof(f1249,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1246,f99])).
% 2.10/0.68  fof(f1246,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 2.10/0.68    inference(superposition,[],[f59,f92])).
% 2.10/0.68  fof(f92,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 2.10/0.68    inference(avatar_component_clause,[],[f91])).
% 2.10/0.68  fof(f1203,plain,(
% 2.10/0.68    spl2_15 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 2.10/0.68    inference(avatar_split_clause,[],[f1202,f102,f97,f87,f209])).
% 2.10/0.68  fof(f87,plain,(
% 2.10/0.68    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.10/0.68  fof(f1202,plain,(
% 2.10/0.68    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 2.10/0.68    inference(subsumption_resolution,[],[f204,f104])).
% 2.10/0.68  fof(f204,plain,(
% 2.10/0.68    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 2.10/0.68    inference(resolution,[],[f62,f99])).
% 2.10/0.68  fof(f62,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f33])).
% 2.10/0.68  fof(f33,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.68    inference(flattening,[],[f32])).
% 2.10/0.68  fof(f32,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.68    inference(ennf_transformation,[],[f22])).
% 2.10/0.68  fof(f22,axiom,(
% 2.10/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 2.10/0.68  fof(f1194,plain,(
% 2.10/0.68    spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_18),
% 2.10/0.68    inference(avatar_split_clause,[],[f1193,f231,f107,f102,f97,f87])).
% 2.10/0.68  fof(f107,plain,(
% 2.10/0.68    spl2_5 <=> v2_pre_topc(sK0)),
% 2.10/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.10/0.68  fof(f1193,plain,(
% 2.10/0.68    v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_18)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1192,f104])).
% 2.10/0.68  fof(f1192,plain,(
% 2.10/0.68    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_5 | ~spl2_18)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1191,f99])).
% 2.10/0.68  fof(f1191,plain,(
% 2.10/0.68    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_5 | ~spl2_18)),
% 2.10/0.68    inference(subsumption_resolution,[],[f269,f109])).
% 2.10/0.68  fof(f109,plain,(
% 2.10/0.68    v2_pre_topc(sK0) | ~spl2_5),
% 2.10/0.68    inference(avatar_component_clause,[],[f107])).
% 2.10/0.68  fof(f269,plain,(
% 2.10/0.68    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_18),
% 2.10/0.68    inference(trivial_inequality_removal,[],[f268])).
% 2.10/0.68  fof(f268,plain,(
% 2.10/0.68    sK1 != sK1 | v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_18),
% 2.10/0.68    inference(superposition,[],[f65,f233])).
% 2.10/0.68  fof(f233,plain,(
% 2.10/0.68    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_18),
% 2.10/0.68    inference(avatar_component_clause,[],[f231])).
% 2.10/0.68  fof(f65,plain,(
% 2.10/0.68    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f36])).
% 2.10/0.68  fof(f36,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.68    inference(flattening,[],[f35])).
% 2.10/0.68  fof(f35,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.68    inference(ennf_transformation,[],[f19])).
% 2.10/0.68  fof(f19,axiom,(
% 2.10/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.10/0.68  fof(f110,plain,(
% 2.10/0.68    spl2_5),
% 2.10/0.68    inference(avatar_split_clause,[],[f51,f107])).
% 2.10/0.68  fof(f51,plain,(
% 2.10/0.68    v2_pre_topc(sK0)),
% 2.10/0.68    inference(cnf_transformation,[],[f46])).
% 2.10/0.68  fof(f46,plain,(
% 2.10/0.68    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.10/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 2.10/0.68  fof(f44,plain,(
% 2.10/0.68    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.10/0.68    introduced(choice_axiom,[])).
% 2.10/0.68  fof(f45,plain,(
% 2.10/0.68    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.10/0.68    introduced(choice_axiom,[])).
% 2.10/0.68  fof(f43,plain,(
% 2.10/0.68    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.10/0.68    inference(flattening,[],[f42])).
% 2.10/0.68  fof(f42,plain,(
% 2.10/0.68    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.10/0.68    inference(nnf_transformation,[],[f27])).
% 2.10/0.68  fof(f27,plain,(
% 2.10/0.68    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.10/0.68    inference(flattening,[],[f26])).
% 2.10/0.68  fof(f26,plain,(
% 2.10/0.68    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f25])).
% 2.10/0.68  fof(f25,negated_conjecture,(
% 2.10/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.10/0.68    inference(negated_conjecture,[],[f24])).
% 2.10/0.68  fof(f24,conjecture,(
% 2.10/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 2.10/0.68  fof(f105,plain,(
% 2.10/0.68    spl2_4),
% 2.10/0.68    inference(avatar_split_clause,[],[f52,f102])).
% 2.10/0.68  fof(f52,plain,(
% 2.10/0.68    l1_pre_topc(sK0)),
% 2.10/0.68    inference(cnf_transformation,[],[f46])).
% 2.10/0.68  fof(f100,plain,(
% 2.10/0.68    spl2_3),
% 2.10/0.68    inference(avatar_split_clause,[],[f53,f97])).
% 2.10/0.68  fof(f53,plain,(
% 2.10/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.10/0.68    inference(cnf_transformation,[],[f46])).
% 2.10/0.68  fof(f95,plain,(
% 2.10/0.68    spl2_1 | spl2_2),
% 2.10/0.68    inference(avatar_split_clause,[],[f54,f91,f87])).
% 2.10/0.68  fof(f54,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.10/0.68    inference(cnf_transformation,[],[f46])).
% 2.10/0.68  fof(f94,plain,(
% 2.10/0.68    ~spl2_1 | ~spl2_2),
% 2.10/0.68    inference(avatar_split_clause,[],[f55,f91,f87])).
% 2.10/0.68  fof(f55,plain,(
% 2.10/0.68    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.10/0.68    inference(cnf_transformation,[],[f46])).
% 2.10/0.68  % SZS output end Proof for theBenchmark
% 2.10/0.68  % (25597)------------------------------
% 2.10/0.68  % (25597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.68  % (25597)Termination reason: Refutation
% 2.10/0.68  
% 2.10/0.68  % (25597)Memory used [KB]: 7291
% 2.10/0.68  % (25597)Time elapsed: 0.269 s
% 2.10/0.68  % (25597)------------------------------
% 2.10/0.68  % (25597)------------------------------
% 2.10/0.71  % (25573)Success in time 0.336 s
%------------------------------------------------------------------------------
