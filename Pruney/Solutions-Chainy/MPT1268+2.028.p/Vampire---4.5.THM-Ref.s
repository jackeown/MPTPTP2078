%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:30 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 281 expanded)
%              Number of leaves         :   30 ( 107 expanded)
%              Depth                    :   10
%              Number of atoms          :  540 (1685 expanded)
%              Number of equality atoms :   64 ( 236 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f485,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f91,f115,f128,f133,f138,f143,f171,f181,f275,f280,f285,f432,f434,f484])).

fof(f484,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | spl3_9
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f483])).

fof(f483,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | spl3_9
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f482,f347])).

fof(f347,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f132,f335,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f335,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f103,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(unit_resulting_resolution,[],[f64,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f53])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f132,plain,
    ( k1_xboole_0 != sK2
    | spl3_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f482,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f481,f458])).

fof(f458,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f76,f127,f137,f170])).

fof(f170,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl3_13
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f137,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f127,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_8
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f76,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f481,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f471,f283])).

fof(f283,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl3_22
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f471,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f76,f137,f81,f90,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f90,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_5
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f81,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f434,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_22 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_22 ),
    inference(subsumption_resolution,[],[f85,f295])).

fof(f295,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_22 ),
    inference(unit_resulting_resolution,[],[f76,f81,f284,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f284,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f282])).

fof(f85,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f432,plain,
    ( ~ spl3_7
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_21
    | spl3_22 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_21
    | spl3_22 ),
    inference(subsumption_resolution,[],[f430,f284])).

fof(f430,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f421,f274])).

fof(f274,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl3_20
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f421,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(resolution,[],[f398,f279])).

fof(f279,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl3_21
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0 )
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f148,f192])).

fof(f192,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_11 ),
    inference(resolution,[],[f142,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f142,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_11
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f148,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_7 ),
    inference(resolution,[],[f114,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f114,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_7
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f285,plain,
    ( ~ spl3_22
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f157,f84,f79,f74,f282])).

fof(f157,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f76,f86,f81,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f280,plain,
    ( spl3_21
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f152,f79,f74,f69,f277])).

fof(f69,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f152,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f71,f76,f81,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f71,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f275,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f150,f79,f74,f272])).

fof(f150,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f76,f81,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f181,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f173,f71])).

fof(f173,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f76,f81,f167])).

fof(f167,plain,
    ( ! [X2,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_12
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f171,plain,
    ( spl3_12
    | spl3_13 ),
    inference(avatar_split_clause,[],[f51,f169,f166])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f143,plain,
    ( spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f93,f79,f140])).

fof(f93,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f81,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f138,plain,
    ( ~ spl3_4
    | spl3_10 ),
    inference(avatar_split_clause,[],[f42,f135,f84])).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_tops_1(X1,sK0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK0)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK0)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_tops_1(sK1,sK0) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK0)
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK2
      & v3_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f133,plain,
    ( ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f45,f130,f84])).

fof(f45,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f128,plain,
    ( ~ spl3_4
    | spl3_8 ),
    inference(avatar_split_clause,[],[f44,f125,f84])).

fof(f44,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f115,plain,
    ( spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f41,f113,f84])).

fof(f41,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f43,f88,f84])).

fof(f43,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:31:40 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.51  % (8829)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.51  % (8820)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.52  % (8845)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.52  % (8824)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.53  % (8842)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.53  % (8837)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.53  % (8830)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.54  % (8821)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.54  % (8832)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.54  % (8822)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.54  % (8839)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.54  % (8823)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.54  % (8838)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.54  % (8835)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.55  % (8828)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.55  % (8834)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.55  % (8843)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.55  % (8825)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.55  % (8831)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.55  % (8840)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.55  % (8833)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.55  % (8836)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.55  % (8826)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.56  % (8844)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.56  % (8849)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.56  % (8846)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.56  % (8827)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.56  % (8841)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.57  % (8847)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.58  % (8848)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.58  % (8840)Refutation found. Thanks to Tanya!
% 0.23/0.58  % SZS status Theorem for theBenchmark
% 0.23/0.58  % SZS output start Proof for theBenchmark
% 0.23/0.58  fof(f485,plain,(
% 0.23/0.58    $false),
% 0.23/0.58    inference(avatar_sat_refutation,[],[f72,f77,f82,f91,f115,f128,f133,f138,f143,f171,f181,f275,f280,f285,f432,f434,f484])).
% 0.23/0.58  fof(f484,plain,(
% 0.23/0.58    ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_8 | spl3_9 | ~spl3_10 | ~spl3_13 | ~spl3_22),
% 0.23/0.58    inference(avatar_contradiction_clause,[],[f483])).
% 0.23/0.58  fof(f483,plain,(
% 0.23/0.58    $false | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_8 | spl3_9 | ~spl3_10 | ~spl3_13 | ~spl3_22)),
% 0.23/0.58    inference(subsumption_resolution,[],[f482,f347])).
% 0.23/0.58  fof(f347,plain,(
% 0.23/0.58    ~r1_tarski(sK2,k1_xboole_0) | spl3_9),
% 0.23/0.58    inference(unit_resulting_resolution,[],[f132,f335,f57])).
% 0.23/0.58  fof(f57,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f36])).
% 0.23/0.58  fof(f36,plain,(
% 0.23/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.58    inference(flattening,[],[f35])).
% 0.23/0.58  fof(f35,plain,(
% 0.23/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.58    inference(nnf_transformation,[],[f1])).
% 0.23/0.58  fof(f1,axiom,(
% 0.23/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.58  fof(f335,plain,(
% 0.23/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.58    inference(superposition,[],[f103,f62])).
% 0.23/0.58  fof(f62,plain,(
% 0.23/0.58    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.23/0.58    inference(definition_unfolding,[],[f46,f53])).
% 0.23/0.58  fof(f53,plain,(
% 0.23/0.58    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f5])).
% 0.23/0.58  fof(f5,axiom,(
% 0.23/0.58    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.58  fof(f46,plain,(
% 0.23/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f4])).
% 0.23/0.58  fof(f4,axiom,(
% 0.23/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.23/0.58  fof(f103,plain,(
% 0.23/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.23/0.58    inference(unit_resulting_resolution,[],[f64,f63])).
% 0.23/0.58  fof(f63,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 0.23/0.58    inference(definition_unfolding,[],[f60,f53])).
% 0.23/0.58  fof(f60,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f24])).
% 0.23/0.58  fof(f24,plain,(
% 0.23/0.58    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.23/0.58    inference(ennf_transformation,[],[f2])).
% 0.23/0.58  fof(f2,axiom,(
% 0.23/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.23/0.58  fof(f64,plain,(
% 0.23/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.58    inference(equality_resolution,[],[f56])).
% 0.23/0.58  fof(f56,plain,(
% 0.23/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.58    inference(cnf_transformation,[],[f36])).
% 0.23/0.58  fof(f132,plain,(
% 0.23/0.58    k1_xboole_0 != sK2 | spl3_9),
% 0.23/0.58    inference(avatar_component_clause,[],[f130])).
% 0.23/0.58  fof(f130,plain,(
% 0.23/0.58    spl3_9 <=> k1_xboole_0 = sK2),
% 0.23/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.23/0.58  fof(f482,plain,(
% 0.23/0.58    r1_tarski(sK2,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_13 | ~spl3_22)),
% 0.23/0.58    inference(forward_demodulation,[],[f481,f458])).
% 0.23/0.58  fof(f458,plain,(
% 0.23/0.58    sK2 = k1_tops_1(sK0,sK2) | (~spl3_2 | ~spl3_8 | ~spl3_10 | ~spl3_13)),
% 0.23/0.58    inference(unit_resulting_resolution,[],[f76,f127,f137,f170])).
% 0.23/0.58  fof(f170,plain,(
% 0.23/0.58    ( ! [X3,X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1)) ) | ~spl3_13),
% 0.23/0.58    inference(avatar_component_clause,[],[f169])).
% 0.23/0.58  fof(f169,plain,(
% 0.23/0.58    spl3_13 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 0.23/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.23/0.58  fof(f137,plain,(
% 0.23/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_10),
% 0.23/0.58    inference(avatar_component_clause,[],[f135])).
% 0.23/0.58  fof(f135,plain,(
% 0.23/0.58    spl3_10 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.23/0.58  fof(f127,plain,(
% 0.23/0.58    v3_pre_topc(sK2,sK0) | ~spl3_8),
% 0.23/0.58    inference(avatar_component_clause,[],[f125])).
% 0.23/0.58  fof(f125,plain,(
% 0.23/0.58    spl3_8 <=> v3_pre_topc(sK2,sK0)),
% 0.23/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.58  fof(f76,plain,(
% 0.23/0.58    l1_pre_topc(sK0) | ~spl3_2),
% 0.23/0.58    inference(avatar_component_clause,[],[f74])).
% 0.23/0.58  fof(f74,plain,(
% 0.23/0.58    spl3_2 <=> l1_pre_topc(sK0)),
% 0.23/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.58  fof(f481,plain,(
% 0.23/0.58    r1_tarski(k1_tops_1(sK0,sK2),k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_22)),
% 0.23/0.58    inference(forward_demodulation,[],[f471,f283])).
% 0.23/0.58  fof(f283,plain,(
% 0.23/0.58    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl3_22),
% 0.23/0.58    inference(avatar_component_clause,[],[f282])).
% 0.23/0.58  fof(f282,plain,(
% 0.23/0.58    spl3_22 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.23/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.23/0.58  fof(f471,plain,(
% 0.23/0.58    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_10)),
% 0.23/0.58    inference(unit_resulting_resolution,[],[f76,f137,f81,f90,f50])).
% 0.23/0.58  fof(f50,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f19])).
% 0.23/0.58  fof(f19,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.58    inference(flattening,[],[f18])).
% 0.23/0.58  fof(f18,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.58    inference(ennf_transformation,[],[f9])).
% 0.23/0.58  fof(f9,axiom,(
% 0.23/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.23/0.58  fof(f90,plain,(
% 0.23/0.58    r1_tarski(sK2,sK1) | ~spl3_5),
% 0.23/0.58    inference(avatar_component_clause,[],[f88])).
% 0.23/0.58  fof(f88,plain,(
% 0.23/0.58    spl3_5 <=> r1_tarski(sK2,sK1)),
% 0.23/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.58  fof(f81,plain,(
% 0.23/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.23/0.58    inference(avatar_component_clause,[],[f79])).
% 0.23/0.58  fof(f79,plain,(
% 0.23/0.58    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.58  fof(f434,plain,(
% 0.23/0.58    ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_22),
% 0.23/0.58    inference(avatar_contradiction_clause,[],[f433])).
% 0.23/0.58  fof(f433,plain,(
% 0.23/0.58    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_22)),
% 0.23/0.58    inference(subsumption_resolution,[],[f85,f295])).
% 0.23/0.58  fof(f295,plain,(
% 0.23/0.58    ~v2_tops_1(sK1,sK0) | (~spl3_2 | ~spl3_3 | spl3_22)),
% 0.23/0.58    inference(unit_resulting_resolution,[],[f76,f81,f284,f48])).
% 0.23/0.58  fof(f48,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f34])).
% 0.23/0.58  fof(f34,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.58    inference(nnf_transformation,[],[f17])).
% 0.23/0.58  fof(f17,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.58    inference(ennf_transformation,[],[f11])).
% 0.23/0.58  fof(f11,axiom,(
% 0.23/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.23/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.23/0.58  fof(f284,plain,(
% 0.23/0.58    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl3_22),
% 0.23/0.58    inference(avatar_component_clause,[],[f282])).
% 0.23/0.58  fof(f85,plain,(
% 0.23/0.58    v2_tops_1(sK1,sK0) | ~spl3_4),
% 0.23/0.58    inference(avatar_component_clause,[],[f84])).
% 0.23/0.58  fof(f84,plain,(
% 0.23/0.58    spl3_4 <=> v2_tops_1(sK1,sK0)),
% 0.23/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.58  fof(f432,plain,(
% 0.23/0.58    ~spl3_7 | ~spl3_11 | ~spl3_20 | ~spl3_21 | spl3_22),
% 0.23/0.58    inference(avatar_contradiction_clause,[],[f431])).
% 0.23/0.58  fof(f431,plain,(
% 0.23/0.58    $false | (~spl3_7 | ~spl3_11 | ~spl3_20 | ~spl3_21 | spl3_22)),
% 0.23/0.58    inference(subsumption_resolution,[],[f430,f284])).
% 0.23/0.58  fof(f430,plain,(
% 0.23/0.58    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl3_7 | ~spl3_11 | ~spl3_20 | ~spl3_21)),
% 0.23/0.58    inference(subsumption_resolution,[],[f421,f274])).
% 0.23/0.58  fof(f274,plain,(
% 0.23/0.58    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_20),
% 0.23/0.58    inference(avatar_component_clause,[],[f272])).
% 0.23/0.58  fof(f272,plain,(
% 0.23/0.58    spl3_20 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.23/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.23/0.58  fof(f421,plain,(
% 0.23/0.58    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl3_7 | ~spl3_11 | ~spl3_21)),
% 0.23/0.58    inference(resolution,[],[f398,f279])).
% 0.23/0.58  fof(f279,plain,(
% 0.23/0.58    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl3_21),
% 0.23/0.58    inference(avatar_component_clause,[],[f277])).
% 1.65/0.59  fof(f277,plain,(
% 1.65/0.59    spl3_21 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.65/0.59  fof(f398,plain,(
% 1.65/0.59    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1) | k1_xboole_0 = X0) ) | (~spl3_7 | ~spl3_11)),
% 1.65/0.59    inference(subsumption_resolution,[],[f148,f192])).
% 1.65/0.59  fof(f192,plain,(
% 1.65/0.59    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1)) ) | ~spl3_11),
% 1.65/0.59    inference(resolution,[],[f142,f61])).
% 1.65/0.59  fof(f61,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f26])).
% 1.65/0.59  fof(f26,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.65/0.59    inference(flattening,[],[f25])).
% 1.65/0.59  fof(f25,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.65/0.59    inference(ennf_transformation,[],[f3])).
% 1.65/0.59  fof(f3,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.65/0.59  fof(f142,plain,(
% 1.65/0.59    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_11),
% 1.65/0.59    inference(avatar_component_clause,[],[f140])).
% 1.65/0.59  fof(f140,plain,(
% 1.65/0.59    spl3_11 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.65/0.59  fof(f148,plain,(
% 1.65/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl3_7),
% 1.65/0.59    inference(resolution,[],[f114,f59])).
% 1.65/0.59  fof(f59,plain,(
% 1.65/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f37])).
% 1.65/0.59  fof(f37,plain,(
% 1.65/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.65/0.59    inference(nnf_transformation,[],[f6])).
% 1.65/0.59  fof(f6,axiom,(
% 1.65/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.65/0.59  fof(f114,plain,(
% 1.65/0.59    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0)) ) | ~spl3_7),
% 1.65/0.59    inference(avatar_component_clause,[],[f113])).
% 1.65/0.59  fof(f113,plain,(
% 1.65/0.59    spl3_7 <=> ! [X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.65/0.59  fof(f285,plain,(
% 1.65/0.59    ~spl3_22 | ~spl3_2 | ~spl3_3 | spl3_4),
% 1.65/0.59    inference(avatar_split_clause,[],[f157,f84,f79,f74,f282])).
% 1.65/0.59  fof(f157,plain,(
% 1.65/0.59    k1_xboole_0 != k1_tops_1(sK0,sK1) | (~spl3_2 | ~spl3_3 | spl3_4)),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f76,f86,f81,f49])).
% 1.65/0.59  fof(f49,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f34])).
% 1.65/0.59  fof(f86,plain,(
% 1.65/0.59    ~v2_tops_1(sK1,sK0) | spl3_4),
% 1.65/0.59    inference(avatar_component_clause,[],[f84])).
% 1.65/0.59  fof(f280,plain,(
% 1.65/0.59    spl3_21 | ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.65/0.59    inference(avatar_split_clause,[],[f152,f79,f74,f69,f277])).
% 1.65/0.59  fof(f69,plain,(
% 1.65/0.59    spl3_1 <=> v2_pre_topc(sK0)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.65/0.59  fof(f152,plain,(
% 1.65/0.59    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f71,f76,f81,f54])).
% 1.65/0.59  fof(f54,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~v2_pre_topc(X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f23])).
% 1.65/0.59  fof(f23,plain,(
% 1.65/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.59    inference(flattening,[],[f22])).
% 1.65/0.59  fof(f22,plain,(
% 1.65/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.65/0.59    inference(ennf_transformation,[],[f7])).
% 1.65/0.59  fof(f7,axiom,(
% 1.65/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.65/0.59  fof(f71,plain,(
% 1.65/0.59    v2_pre_topc(sK0) | ~spl3_1),
% 1.65/0.59    inference(avatar_component_clause,[],[f69])).
% 1.65/0.59  fof(f275,plain,(
% 1.65/0.59    spl3_20 | ~spl3_2 | ~spl3_3),
% 1.65/0.59    inference(avatar_split_clause,[],[f150,f79,f74,f272])).
% 1.65/0.59  fof(f150,plain,(
% 1.65/0.59    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_2 | ~spl3_3)),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f76,f81,f47])).
% 1.65/0.59  fof(f47,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f16])).
% 1.65/0.59  fof(f16,plain,(
% 1.65/0.59    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f8])).
% 1.65/0.59  fof(f8,axiom,(
% 1.65/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.65/0.59  fof(f181,plain,(
% 1.65/0.59    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_12),
% 1.65/0.59    inference(avatar_contradiction_clause,[],[f180])).
% 1.65/0.59  fof(f180,plain,(
% 1.65/0.59    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_12)),
% 1.65/0.59    inference(subsumption_resolution,[],[f173,f71])).
% 1.65/0.59  fof(f173,plain,(
% 1.65/0.59    ~v2_pre_topc(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_12)),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f76,f81,f167])).
% 1.65/0.59  fof(f167,plain,(
% 1.65/0.59    ( ! [X2,X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_12),
% 1.65/0.59    inference(avatar_component_clause,[],[f166])).
% 1.65/0.59  fof(f166,plain,(
% 1.65/0.59    spl3_12 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.65/0.59  fof(f171,plain,(
% 1.65/0.59    spl3_12 | spl3_13),
% 1.65/0.59    inference(avatar_split_clause,[],[f51,f169,f166])).
% 1.65/0.59  fof(f51,plain,(
% 1.65/0.59    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f21])).
% 1.65/0.59  fof(f21,plain,(
% 1.65/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.59    inference(flattening,[],[f20])).
% 1.65/0.59  fof(f20,plain,(
% 1.65/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.65/0.59    inference(ennf_transformation,[],[f10])).
% 1.65/0.59  fof(f10,axiom,(
% 1.65/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 1.65/0.59  fof(f143,plain,(
% 1.65/0.59    spl3_11 | ~spl3_3),
% 1.65/0.59    inference(avatar_split_clause,[],[f93,f79,f140])).
% 1.65/0.59  fof(f93,plain,(
% 1.65/0.59    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f81,f58])).
% 1.65/0.59  fof(f58,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f37])).
% 1.65/0.59  fof(f138,plain,(
% 1.65/0.59    ~spl3_4 | spl3_10),
% 1.65/0.59    inference(avatar_split_clause,[],[f42,f135,f84])).
% 1.65/0.59  fof(f42,plain,(
% 1.65/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 1.65/0.59    inference(cnf_transformation,[],[f33])).
% 1.65/0.59  fof(f33,plain,(
% 1.65/0.59    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.65/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).
% 1.65/0.59  fof(f30,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f31,plain,(
% 1.65/0.59    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f32,plain,(
% 1.65/0.59    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f29,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.65/0.59    inference(rectify,[],[f28])).
% 1.65/0.59  fof(f28,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.65/0.59    inference(flattening,[],[f27])).
% 1.65/0.59  fof(f27,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.65/0.59    inference(nnf_transformation,[],[f15])).
% 1.65/0.59  fof(f15,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.65/0.59    inference(flattening,[],[f14])).
% 1.65/0.59  fof(f14,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.65/0.59    inference(ennf_transformation,[],[f13])).
% 1.65/0.59  fof(f13,negated_conjecture,(
% 1.65/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.65/0.59    inference(negated_conjecture,[],[f12])).
% 1.65/0.59  fof(f12,conjecture,(
% 1.65/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.65/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 1.65/0.59  fof(f133,plain,(
% 1.65/0.59    ~spl3_4 | ~spl3_9),
% 1.65/0.59    inference(avatar_split_clause,[],[f45,f130,f84])).
% 1.65/0.59  fof(f45,plain,(
% 1.65/0.59    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 1.65/0.59    inference(cnf_transformation,[],[f33])).
% 1.65/0.59  fof(f128,plain,(
% 1.65/0.59    ~spl3_4 | spl3_8),
% 1.65/0.59    inference(avatar_split_clause,[],[f44,f125,f84])).
% 1.65/0.59  fof(f44,plain,(
% 1.65/0.59    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 1.65/0.59    inference(cnf_transformation,[],[f33])).
% 1.65/0.59  fof(f115,plain,(
% 1.65/0.59    spl3_4 | spl3_7),
% 1.65/0.59    inference(avatar_split_clause,[],[f41,f113,f84])).
% 1.65/0.59  fof(f41,plain,(
% 1.65/0.59    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f33])).
% 1.65/0.59  fof(f91,plain,(
% 1.65/0.59    ~spl3_4 | spl3_5),
% 1.65/0.59    inference(avatar_split_clause,[],[f43,f88,f84])).
% 1.65/0.59  fof(f43,plain,(
% 1.65/0.59    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 1.65/0.59    inference(cnf_transformation,[],[f33])).
% 1.65/0.59  fof(f82,plain,(
% 1.65/0.59    spl3_3),
% 1.65/0.59    inference(avatar_split_clause,[],[f40,f79])).
% 1.65/0.59  fof(f40,plain,(
% 1.65/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.59    inference(cnf_transformation,[],[f33])).
% 1.65/0.59  fof(f77,plain,(
% 1.65/0.59    spl3_2),
% 1.65/0.59    inference(avatar_split_clause,[],[f39,f74])).
% 1.65/0.59  fof(f39,plain,(
% 1.65/0.59    l1_pre_topc(sK0)),
% 1.65/0.59    inference(cnf_transformation,[],[f33])).
% 1.65/0.59  fof(f72,plain,(
% 1.65/0.59    spl3_1),
% 1.65/0.59    inference(avatar_split_clause,[],[f38,f69])).
% 1.65/0.59  fof(f38,plain,(
% 1.65/0.59    v2_pre_topc(sK0)),
% 1.65/0.59    inference(cnf_transformation,[],[f33])).
% 1.65/0.59  % SZS output end Proof for theBenchmark
% 1.65/0.59  % (8840)------------------------------
% 1.65/0.59  % (8840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (8840)Termination reason: Refutation
% 1.65/0.59  
% 1.65/0.59  % (8840)Memory used [KB]: 11001
% 1.65/0.59  % (8840)Time elapsed: 0.146 s
% 1.65/0.59  % (8840)------------------------------
% 1.65/0.59  % (8840)------------------------------
% 1.65/0.59  % (8819)Success in time 0.22 s
%------------------------------------------------------------------------------
