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
% DateTime   : Thu Dec  3 13:11:34 EST 2020

% Result     : Theorem 4.53s
% Output     : Refutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 396 expanded)
%              Number of leaves         :   44 ( 139 expanded)
%              Depth                    :   13
%              Number of atoms          :  633 (1239 expanded)
%              Number of equality atoms :  103 ( 230 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (16788)Time limit reached!
% (16788)------------------------------
% (16788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16788)Termination reason: Time limit

% (16788)Memory used [KB]: 15095
% (16788)Time elapsed: 0.518 s
% (16788)------------------------------
% (16788)------------------------------
fof(f6151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f119,f124,f129,f134,f255,f733,f2667,f2729,f2747,f3541,f3573,f3797,f3811,f3821,f3855,f3857,f3867,f6017,f6061,f6147,f6150])).

fof(f6150,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | v3_pre_topc(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6147,plain,(
    ~ spl2_143 ),
    inference(avatar_contradiction_clause,[],[f6122])).

fof(f6122,plain,
    ( $false
    | ~ spl2_143 ),
    inference(unit_resulting_resolution,[],[f557,f98,f3912,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f3912,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_143 ),
    inference(avatar_component_clause,[],[f3911])).

fof(f3911,plain,
    ( spl2_143
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_143])])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f557,plain,(
    ! [X11] : m1_subset_1(X11,k1_zfmisc_1(X11)) ),
    inference(subsumption_resolution,[],[f556,f98])).

fof(f556,plain,(
    ! [X11] :
      ( m1_subset_1(X11,k1_zfmisc_1(X11))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ) ),
    inference(superposition,[],[f217,f86])).

fof(f86,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f217,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f97,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f6061,plain,
    ( spl2_138
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_215 ),
    inference(avatar_split_clause,[],[f6060,f6014,f126,f121,f3597])).

fof(f3597,plain,
    ( spl2_138
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).

fof(f121,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f126,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f6014,plain,
    ( spl2_215
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_215])])).

fof(f6060,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_215 ),
    inference(subsumption_resolution,[],[f6059,f128])).

fof(f128,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f6059,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_215 ),
    inference(subsumption_resolution,[],[f6031,f123])).

fof(f123,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f6031,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_215 ),
    inference(superposition,[],[f276,f6016])).

fof(f6016,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_215 ),
    inference(avatar_component_clause,[],[f6014])).

fof(f276,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f74,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f6017,plain,
    ( spl2_143
    | spl2_215
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f6012,f835,f830,f6014,f3911])).

fof(f830,plain,
    ( spl2_30
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f835,plain,
    ( spl2_31
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f6012,plain,
    ( ! [X18] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f5979,f832])).

fof(f832,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f830])).

fof(f5979,plain,
    ( ! [X18] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl2_31 ),
    inference(superposition,[],[f981,f837])).

fof(f837,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f835])).

fof(f981,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f976,f97])).

fof(f976,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f302,f74])).

fof(f302,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f298,f97])).

fof(f298,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f88,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f3867,plain,
    ( ~ spl2_137
    | spl2_138
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f3866,f2521,f3597,f3593])).

fof(f3593,plain,
    ( spl2_137
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).

fof(f2521,plain,
    ( spl2_78
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f3866,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_78 ),
    inference(resolution,[],[f2522,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2522,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f2521])).

fof(f3857,plain,
    ( spl2_31
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f3856,f826,f231,f835])).

fof(f231,plain,
    ( spl2_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f826,plain,
    ( spl2_29
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f3856,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f3838,f827])).

fof(f827,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f826])).

fof(f3838,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f218,f233])).

fof(f233,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f231])).

fof(f218,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f80,f81])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f3855,plain,
    ( spl2_30
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f3854,f826,f231,f830])).

fof(f3854,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f3837,f827])).

fof(f3837,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f217,f233])).

fof(f3821,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f3820,f227,f115,f231])).

fof(f115,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f227,plain,
    ( spl2_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f3820,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f3817,f228])).

fof(f228,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f227])).

fof(f3817,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f74,f116])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f3811,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_10
    | ~ spl2_138 ),
    inference(avatar_contradiction_clause,[],[f3810])).

fof(f3810,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10
    | ~ spl2_138 ),
    inference(subsumption_resolution,[],[f3809,f128])).

fof(f3809,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_10
    | ~ spl2_138 ),
    inference(subsumption_resolution,[],[f3808,f123])).

fof(f3808,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_10
    | ~ spl2_138 ),
    inference(subsumption_resolution,[],[f3805,f232])).

fof(f232,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f231])).

fof(f3805,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_138 ),
    inference(superposition,[],[f1123,f3599])).

fof(f3599,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_138 ),
    inference(avatar_component_clause,[],[f3597])).

fof(f1123,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f308,f291])).

fof(f291,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f284,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f284,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f105,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f308,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f89,f74])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f3797,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | spl2_137 ),
    inference(avatar_contradiction_clause,[],[f3796])).

fof(f3796,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | spl2_137 ),
    inference(subsumption_resolution,[],[f3795,f108])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f3795,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | spl2_137 ),
    inference(subsumption_resolution,[],[f3787,f112])).

fof(f112,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f3787,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | spl2_137 ),
    inference(resolution,[],[f3595,f328])).

fof(f328,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f322,f201])).

fof(f201,plain,
    ( ! [X7] :
        ( r1_tarski(X7,u1_struct_0(sK0))
        | ~ r1_tarski(X7,sK1) )
    | ~ spl2_6 ),
    inference(resolution,[],[f101,f149])).

fof(f149,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl2_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f322,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f317,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f317,plain,
    ( ! [X15] :
        ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X15,sK0)
        | r1_tarski(X15,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X15,sK1) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f315,f128])).

fof(f315,plain,
    ( ! [X15] :
        ( ~ r1_tarski(X15,sK1)
        | ~ v3_pre_topc(X15,sK0)
        | r1_tarski(X15,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f94,f123])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f3595,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl2_137 ),
    inference(avatar_component_clause,[],[f3593])).

fof(f3573,plain,
    ( spl2_82
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f3572,f126,f121,f2603])).

fof(f2603,plain,
    ( spl2_82
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).

fof(f3572,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f3553,f128])).

fof(f3553,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f876,f123])).

fof(f876,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | r1_tarski(X8,k2_pre_topc(X9,X8))
      | ~ l1_pre_topc(X9) ) ),
    inference(superposition,[],[f154,f289])).

fof(f289,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f286,f92])).

fof(f286,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f91,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f154,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X1,k2_xboole_0(X1,X2)) ) ),
    inference(superposition,[],[f75,f84])).

fof(f84,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f3541,plain,
    ( spl2_78
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f3540,f126,f121,f2521])).

fof(f3540,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f3531,f128])).

fof(f3531,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f852,f123])).

fof(f852,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | r1_tarski(k1_tops_1(X9,X8),X8)
      | ~ l1_pre_topc(X9) ) ),
    inference(superposition,[],[f100,f276])).

fof(f100,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2747,plain,
    ( ~ spl2_82
    | spl2_29 ),
    inference(avatar_split_clause,[],[f2746,f826,f2603])).

fof(f2746,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_29 ),
    inference(resolution,[],[f828,f96])).

fof(f828,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f826])).

fof(f2729,plain,
    ( ~ spl2_10
    | spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f2728,f227,f115,f231])).

fof(f2728,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f2727,f228])).

fof(f2727,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(superposition,[],[f117,f74])).

fof(f117,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f2667,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f2665,f121,f147])).

fof(f2665,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f123,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f733,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f732])).

fof(f732,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(subsumption_resolution,[],[f731,f128])).

fof(f731,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_9 ),
    inference(subsumption_resolution,[],[f724,f123])).

fof(f724,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_9 ),
    inference(resolution,[],[f291,f229])).

fof(f229,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f227])).

fof(f255,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f250,f131,f126,f121,f252])).

fof(f252,plain,
    ( spl2_12
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f131,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f250,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f249,f133])).

fof(f133,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f249,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f247,f128])).

fof(f247,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f93,f123])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f134,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f69,f131])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f61,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f129,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f70,f126])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f124,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f71,f121])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f119,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f72,f115,f111])).

fof(f72,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f118,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f73,f115,f111])).

fof(f73,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (16807)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.48  % (16799)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.50  % (16790)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (16810)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (16791)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (16792)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (16793)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (16794)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (16806)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (16804)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (16787)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (16802)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (16796)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (16808)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (16786)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (16783)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (16798)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (16800)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (16788)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (16795)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (16782)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (16784)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (16785)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (16811)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (16797)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (16803)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (16789)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (16809)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (16805)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (16801)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 3.19/0.82  % (16806)Time limit reached!
% 3.19/0.82  % (16806)------------------------------
% 3.19/0.82  % (16806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.82  % (16806)Termination reason: Time limit
% 3.19/0.82  
% 3.19/0.82  % (16806)Memory used [KB]: 13432
% 3.19/0.82  % (16806)Time elapsed: 0.422 s
% 3.19/0.82  % (16806)------------------------------
% 3.19/0.82  % (16806)------------------------------
% 3.82/0.86  % (16784)Time limit reached!
% 3.82/0.86  % (16784)------------------------------
% 3.82/0.86  % (16784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.86  % (16784)Termination reason: Time limit
% 3.82/0.86  % (16784)Termination phase: Saturation
% 3.82/0.86  
% 3.82/0.86  % (16784)Memory used [KB]: 6780
% 3.82/0.86  % (16784)Time elapsed: 0.400 s
% 3.82/0.86  % (16784)------------------------------
% 3.82/0.86  % (16784)------------------------------
% 4.42/0.93  % (16811)Time limit reached!
% 4.42/0.93  % (16811)------------------------------
% 4.42/0.93  % (16811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.93  % (16811)Termination reason: Time limit
% 4.42/0.93  
% 4.42/0.93  % (16811)Memory used [KB]: 3837
% 4.42/0.93  % (16811)Time elapsed: 0.520 s
% 4.42/0.93  % (16811)------------------------------
% 4.42/0.93  % (16811)------------------------------
% 4.53/0.95  % (16796)Time limit reached!
% 4.53/0.95  % (16796)------------------------------
% 4.53/0.95  % (16796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/0.95  % (16796)Termination reason: Time limit
% 4.53/0.95  
% 4.53/0.95  % (16796)Memory used [KB]: 5884
% 4.53/0.95  % (16796)Time elapsed: 0.516 s
% 4.53/0.95  % (16796)------------------------------
% 4.53/0.95  % (16796)------------------------------
% 4.53/0.96  % (16803)Refutation found. Thanks to Tanya!
% 4.53/0.96  % SZS status Theorem for theBenchmark
% 4.53/0.96  % SZS output start Proof for theBenchmark
% 4.53/0.96  % (16788)Time limit reached!
% 4.53/0.96  % (16788)------------------------------
% 4.53/0.96  % (16788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/0.96  % (16788)Termination reason: Time limit
% 4.53/0.96  
% 4.53/0.96  % (16788)Memory used [KB]: 15095
% 4.53/0.96  % (16788)Time elapsed: 0.518 s
% 4.53/0.96  % (16788)------------------------------
% 4.53/0.96  % (16788)------------------------------
% 4.53/0.96  fof(f6151,plain,(
% 4.53/0.96    $false),
% 4.53/0.96    inference(avatar_sat_refutation,[],[f118,f119,f124,f129,f134,f255,f733,f2667,f2729,f2747,f3541,f3573,f3797,f3811,f3821,f3855,f3857,f3867,f6017,f6061,f6147,f6150])).
% 4.53/0.96  fof(f6150,plain,(
% 4.53/0.96    sK1 != k1_tops_1(sK0,sK1) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | v3_pre_topc(sK1,sK0)),
% 4.53/0.96    introduced(theory_tautology_sat_conflict,[])).
% 4.53/0.96  fof(f6147,plain,(
% 4.53/0.96    ~spl2_143),
% 4.53/0.96    inference(avatar_contradiction_clause,[],[f6122])).
% 4.53/0.96  fof(f6122,plain,(
% 4.53/0.96    $false | ~spl2_143),
% 4.53/0.96    inference(unit_resulting_resolution,[],[f557,f98,f3912,f105])).
% 4.53/0.96  fof(f105,plain,(
% 4.53/0.96    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(cnf_transformation,[],[f59])).
% 4.53/0.96  fof(f59,plain,(
% 4.53/0.96    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.53/0.96    inference(flattening,[],[f58])).
% 4.53/0.96  fof(f58,plain,(
% 4.53/0.96    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.53/0.96    inference(ennf_transformation,[],[f16])).
% 4.53/0.96  fof(f16,axiom,(
% 4.53/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 4.53/0.96  fof(f3912,plain,(
% 4.53/0.96    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_143),
% 4.53/0.96    inference(avatar_component_clause,[],[f3911])).
% 4.53/0.96  fof(f3911,plain,(
% 4.53/0.96    spl2_143 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_143])])).
% 4.53/0.96  fof(f98,plain,(
% 4.53/0.96    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(cnf_transformation,[],[f22])).
% 4.53/0.96  fof(f22,axiom,(
% 4.53/0.96    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 4.53/0.96  fof(f557,plain,(
% 4.53/0.96    ( ! [X11] : (m1_subset_1(X11,k1_zfmisc_1(X11))) )),
% 4.53/0.96    inference(subsumption_resolution,[],[f556,f98])).
% 4.53/0.96  fof(f556,plain,(
% 4.53/0.96    ( ! [X11] : (m1_subset_1(X11,k1_zfmisc_1(X11)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11))) )),
% 4.53/0.96    inference(superposition,[],[f217,f86])).
% 4.53/0.96  fof(f86,plain,(
% 4.53/0.96    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.53/0.96    inference(cnf_transformation,[],[f10])).
% 4.53/0.96  fof(f10,axiom,(
% 4.53/0.96    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 4.53/0.96  fof(f217,plain,(
% 4.53/0.96    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 4.53/0.96    inference(duplicate_literal_removal,[],[f215])).
% 4.53/0.96  fof(f215,plain,(
% 4.53/0.96    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 4.53/0.96    inference(superposition,[],[f97,f81])).
% 4.53/0.96  fof(f81,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(cnf_transformation,[],[f39])).
% 4.53/0.96  fof(f39,plain,(
% 4.53/0.96    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.53/0.96    inference(ennf_transformation,[],[f14])).
% 4.53/0.96  fof(f14,axiom,(
% 4.53/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 4.53/0.96  fof(f97,plain,(
% 4.53/0.96    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(cnf_transformation,[],[f51])).
% 4.53/0.96  fof(f51,plain,(
% 4.53/0.96    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.53/0.96    inference(ennf_transformation,[],[f15])).
% 4.53/0.96  fof(f15,axiom,(
% 4.53/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 4.53/0.96  fof(f6061,plain,(
% 4.53/0.96    spl2_138 | ~spl2_3 | ~spl2_4 | ~spl2_215),
% 4.53/0.96    inference(avatar_split_clause,[],[f6060,f6014,f126,f121,f3597])).
% 4.53/0.96  fof(f3597,plain,(
% 4.53/0.96    spl2_138 <=> sK1 = k1_tops_1(sK0,sK1)),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).
% 4.53/0.96  fof(f121,plain,(
% 4.53/0.96    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 4.53/0.96  fof(f126,plain,(
% 4.53/0.96    spl2_4 <=> l1_pre_topc(sK0)),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 4.53/0.96  fof(f6014,plain,(
% 4.53/0.96    spl2_215 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_215])])).
% 4.53/0.96  fof(f6060,plain,(
% 4.53/0.96    sK1 = k1_tops_1(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_215)),
% 4.53/0.96    inference(subsumption_resolution,[],[f6059,f128])).
% 4.53/0.96  fof(f128,plain,(
% 4.53/0.96    l1_pre_topc(sK0) | ~spl2_4),
% 4.53/0.96    inference(avatar_component_clause,[],[f126])).
% 4.53/0.96  fof(f6059,plain,(
% 4.53/0.96    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_215)),
% 4.53/0.96    inference(subsumption_resolution,[],[f6031,f123])).
% 4.53/0.96  fof(f123,plain,(
% 4.53/0.96    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 4.53/0.96    inference(avatar_component_clause,[],[f121])).
% 4.53/0.96  fof(f6031,plain,(
% 4.53/0.96    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_215),
% 4.53/0.96    inference(superposition,[],[f276,f6016])).
% 4.53/0.96  fof(f6016,plain,(
% 4.53/0.96    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_215),
% 4.53/0.96    inference(avatar_component_clause,[],[f6014])).
% 4.53/0.96  fof(f276,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.53/0.96    inference(duplicate_literal_removal,[],[f275])).
% 4.53/0.96  fof(f275,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.53/0.96    inference(superposition,[],[f74,f90])).
% 4.53/0.96  fof(f90,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f43])).
% 4.53/0.96  fof(f43,plain,(
% 4.53/0.96    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.53/0.96    inference(ennf_transformation,[],[f32])).
% 4.53/0.96  fof(f32,axiom,(
% 4.53/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 4.53/0.96  fof(f74,plain,(
% 4.53/0.96    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(cnf_transformation,[],[f37])).
% 4.53/0.96  fof(f37,plain,(
% 4.53/0.96    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.53/0.96    inference(ennf_transformation,[],[f20])).
% 4.53/0.96  fof(f20,axiom,(
% 4.53/0.96    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 4.53/0.96  fof(f6017,plain,(
% 4.53/0.96    spl2_143 | spl2_215 | ~spl2_30 | ~spl2_31),
% 4.53/0.96    inference(avatar_split_clause,[],[f6012,f835,f830,f6014,f3911])).
% 4.53/0.96  fof(f830,plain,(
% 4.53/0.96    spl2_30 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 4.53/0.96  fof(f835,plain,(
% 4.53/0.96    spl2_31 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 4.53/0.96  fof(f6012,plain,(
% 4.53/0.96    ( ! [X18] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl2_30 | ~spl2_31)),
% 4.53/0.96    inference(subsumption_resolution,[],[f5979,f832])).
% 4.53/0.96  fof(f832,plain,(
% 4.53/0.96    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_30),
% 4.53/0.96    inference(avatar_component_clause,[],[f830])).
% 4.53/0.96  fof(f5979,plain,(
% 4.53/0.96    ( ! [X18] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_31),
% 4.53/0.96    inference(superposition,[],[f981,f837])).
% 4.53/0.96  fof(f837,plain,(
% 4.53/0.96    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_31),
% 4.53/0.96    inference(avatar_component_clause,[],[f835])).
% 4.53/0.96  fof(f981,plain,(
% 4.53/0.96    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 4.53/0.96    inference(subsumption_resolution,[],[f976,f97])).
% 4.53/0.96  fof(f976,plain,(
% 4.53/0.96    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 4.53/0.96    inference(superposition,[],[f302,f74])).
% 4.53/0.96  fof(f302,plain,(
% 4.53/0.96    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 4.53/0.96    inference(subsumption_resolution,[],[f298,f97])).
% 4.53/0.96  fof(f298,plain,(
% 4.53/0.96    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 4.53/0.96    inference(superposition,[],[f88,f104])).
% 4.53/0.96  fof(f104,plain,(
% 4.53/0.96    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(cnf_transformation,[],[f57])).
% 4.53/0.96  fof(f57,plain,(
% 4.53/0.96    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.53/0.96    inference(ennf_transformation,[],[f17])).
% 4.53/0.96  fof(f17,axiom,(
% 4.53/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 4.53/0.96  fof(f88,plain,(
% 4.53/0.96    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(cnf_transformation,[],[f41])).
% 4.53/0.96  fof(f41,plain,(
% 4.53/0.96    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.53/0.96    inference(ennf_transformation,[],[f21])).
% 4.53/0.96  fof(f21,axiom,(
% 4.53/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 4.53/0.96  fof(f3867,plain,(
% 4.53/0.96    ~spl2_137 | spl2_138 | ~spl2_78),
% 4.53/0.96    inference(avatar_split_clause,[],[f3866,f2521,f3597,f3593])).
% 4.53/0.96  fof(f3593,plain,(
% 4.53/0.96    spl2_137 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).
% 4.53/0.96  fof(f2521,plain,(
% 4.53/0.96    spl2_78 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 4.53/0.96  fof(f3866,plain,(
% 4.53/0.96    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl2_78),
% 4.53/0.96    inference(resolution,[],[f2522,f79])).
% 4.53/0.96  fof(f79,plain,(
% 4.53/0.96    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f67])).
% 4.53/0.96  fof(f67,plain,(
% 4.53/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.53/0.96    inference(flattening,[],[f66])).
% 4.53/0.96  fof(f66,plain,(
% 4.53/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.53/0.96    inference(nnf_transformation,[],[f2])).
% 4.53/0.96  fof(f2,axiom,(
% 4.53/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.53/0.96  fof(f2522,plain,(
% 4.53/0.96    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_78),
% 4.53/0.96    inference(avatar_component_clause,[],[f2521])).
% 4.53/0.96  fof(f3857,plain,(
% 4.53/0.96    spl2_31 | ~spl2_10 | ~spl2_29),
% 4.53/0.96    inference(avatar_split_clause,[],[f3856,f826,f231,f835])).
% 4.53/0.96  fof(f231,plain,(
% 4.53/0.96    spl2_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 4.53/0.96  fof(f826,plain,(
% 4.53/0.96    spl2_29 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 4.53/0.96  fof(f3856,plain,(
% 4.53/0.96    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_10 | ~spl2_29)),
% 4.53/0.96    inference(subsumption_resolution,[],[f3838,f827])).
% 4.53/0.96  fof(f827,plain,(
% 4.53/0.96    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_29),
% 4.53/0.96    inference(avatar_component_clause,[],[f826])).
% 4.53/0.96  fof(f3838,plain,(
% 4.53/0.96    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_10),
% 4.53/0.96    inference(superposition,[],[f218,f233])).
% 4.53/0.96  fof(f233,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_10),
% 4.53/0.96    inference(avatar_component_clause,[],[f231])).
% 4.53/0.96  fof(f218,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(duplicate_literal_removal,[],[f214])).
% 4.53/0.96  fof(f214,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(superposition,[],[f80,f81])).
% 4.53/0.96  fof(f80,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(cnf_transformation,[],[f38])).
% 4.53/0.96  fof(f38,plain,(
% 4.53/0.96    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.53/0.96    inference(ennf_transformation,[],[f18])).
% 4.53/0.96  fof(f18,axiom,(
% 4.53/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 4.53/0.96  fof(f3855,plain,(
% 4.53/0.96    spl2_30 | ~spl2_10 | ~spl2_29),
% 4.53/0.96    inference(avatar_split_clause,[],[f3854,f826,f231,f830])).
% 4.53/0.96  fof(f3854,plain,(
% 4.53/0.96    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | (~spl2_10 | ~spl2_29)),
% 4.53/0.96    inference(subsumption_resolution,[],[f3837,f827])).
% 4.53/0.96  fof(f3837,plain,(
% 4.53/0.96    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_10),
% 4.53/0.96    inference(superposition,[],[f217,f233])).
% 4.53/0.96  fof(f3821,plain,(
% 4.53/0.96    spl2_10 | ~spl2_2 | ~spl2_9),
% 4.53/0.96    inference(avatar_split_clause,[],[f3820,f227,f115,f231])).
% 4.53/0.96  fof(f115,plain,(
% 4.53/0.96    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 4.53/0.96  fof(f227,plain,(
% 4.53/0.96    spl2_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 4.53/0.96  fof(f3820,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_2 | ~spl2_9)),
% 4.53/0.96    inference(subsumption_resolution,[],[f3817,f228])).
% 4.53/0.96  fof(f228,plain,(
% 4.53/0.96    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 4.53/0.96    inference(avatar_component_clause,[],[f227])).
% 4.53/0.96  fof(f3817,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 4.53/0.96    inference(superposition,[],[f74,f116])).
% 4.53/0.96  fof(f116,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 4.53/0.96    inference(avatar_component_clause,[],[f115])).
% 4.53/0.96  fof(f3811,plain,(
% 4.53/0.96    ~spl2_3 | ~spl2_4 | spl2_10 | ~spl2_138),
% 4.53/0.96    inference(avatar_contradiction_clause,[],[f3810])).
% 4.53/0.96  fof(f3810,plain,(
% 4.53/0.96    $false | (~spl2_3 | ~spl2_4 | spl2_10 | ~spl2_138)),
% 4.53/0.96    inference(subsumption_resolution,[],[f3809,f128])).
% 4.53/0.96  fof(f3809,plain,(
% 4.53/0.96    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_10 | ~spl2_138)),
% 4.53/0.96    inference(subsumption_resolution,[],[f3808,f123])).
% 4.53/0.96  fof(f3808,plain,(
% 4.53/0.96    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_10 | ~spl2_138)),
% 4.53/0.96    inference(subsumption_resolution,[],[f3805,f232])).
% 4.53/0.96  fof(f232,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl2_10),
% 4.53/0.96    inference(avatar_component_clause,[],[f231])).
% 4.53/0.96  fof(f3805,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_138),
% 4.53/0.96    inference(superposition,[],[f1123,f3599])).
% 4.53/0.96  fof(f3599,plain,(
% 4.53/0.96    sK1 = k1_tops_1(sK0,sK1) | ~spl2_138),
% 4.53/0.96    inference(avatar_component_clause,[],[f3597])).
% 4.53/0.96  fof(f1123,plain,(
% 4.53/0.96    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.53/0.96    inference(subsumption_resolution,[],[f308,f291])).
% 4.53/0.96  fof(f291,plain,(
% 4.53/0.96    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.53/0.96    inference(subsumption_resolution,[],[f284,f92])).
% 4.53/0.96  fof(f92,plain,(
% 4.53/0.96    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f46])).
% 4.53/0.96  fof(f46,plain,(
% 4.53/0.96    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.53/0.96    inference(flattening,[],[f45])).
% 4.53/0.96  fof(f45,plain,(
% 4.53/0.96    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.53/0.96    inference(ennf_transformation,[],[f26])).
% 4.53/0.96  fof(f26,axiom,(
% 4.53/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 4.53/0.96  fof(f284,plain,(
% 4.53/0.96    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.53/0.96    inference(duplicate_literal_removal,[],[f283])).
% 4.53/0.96  fof(f283,plain,(
% 4.53/0.96    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.53/0.96    inference(superposition,[],[f105,f91])).
% 4.53/0.96  fof(f91,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f44])).
% 4.53/0.96  fof(f44,plain,(
% 4.53/0.96    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.53/0.96    inference(ennf_transformation,[],[f31])).
% 4.53/0.96  fof(f31,axiom,(
% 4.53/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 4.53/0.96  fof(f308,plain,(
% 4.53/0.96    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 4.53/0.96    inference(superposition,[],[f89,f74])).
% 4.53/0.96  fof(f89,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f42])).
% 4.53/0.96  fof(f42,plain,(
% 4.53/0.96    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.53/0.96    inference(ennf_transformation,[],[f28])).
% 4.53/0.96  fof(f28,axiom,(
% 4.53/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 4.53/0.96  fof(f3797,plain,(
% 4.53/0.96    ~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_6 | spl2_137),
% 4.53/0.96    inference(avatar_contradiction_clause,[],[f3796])).
% 4.53/0.96  fof(f3796,plain,(
% 4.53/0.96    $false | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_6 | spl2_137)),
% 4.53/0.96    inference(subsumption_resolution,[],[f3795,f108])).
% 4.53/0.96  fof(f108,plain,(
% 4.53/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.53/0.96    inference(equality_resolution,[],[f78])).
% 4.53/0.96  fof(f78,plain,(
% 4.53/0.96    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.53/0.96    inference(cnf_transformation,[],[f67])).
% 4.53/0.96  fof(f3795,plain,(
% 4.53/0.96    ~r1_tarski(sK1,sK1) | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_6 | spl2_137)),
% 4.53/0.96    inference(subsumption_resolution,[],[f3787,f112])).
% 4.53/0.96  fof(f112,plain,(
% 4.53/0.96    v3_pre_topc(sK1,sK0) | ~spl2_1),
% 4.53/0.96    inference(avatar_component_clause,[],[f111])).
% 4.53/0.96  fof(f111,plain,(
% 4.53/0.96    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 4.53/0.96  fof(f3787,plain,(
% 4.53/0.96    ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_6 | spl2_137)),
% 4.53/0.96    inference(resolution,[],[f3595,f328])).
% 4.53/0.96  fof(f328,plain,(
% 4.53/0.96    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1)) ) | (~spl2_3 | ~spl2_4 | ~spl2_6)),
% 4.53/0.96    inference(subsumption_resolution,[],[f322,f201])).
% 4.53/0.96  fof(f201,plain,(
% 4.53/0.96    ( ! [X7] : (r1_tarski(X7,u1_struct_0(sK0)) | ~r1_tarski(X7,sK1)) ) | ~spl2_6),
% 4.53/0.96    inference(resolution,[],[f101,f149])).
% 4.53/0.96  fof(f149,plain,(
% 4.53/0.96    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_6),
% 4.53/0.96    inference(avatar_component_clause,[],[f147])).
% 4.53/0.96  fof(f147,plain,(
% 4.53/0.96    spl2_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 4.53/0.96  fof(f101,plain,(
% 4.53/0.96    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f53])).
% 4.53/0.96  fof(f53,plain,(
% 4.53/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.53/0.96    inference(flattening,[],[f52])).
% 4.53/0.96  fof(f52,plain,(
% 4.53/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.53/0.96    inference(ennf_transformation,[],[f6])).
% 4.53/0.96  fof(f6,axiom,(
% 4.53/0.96    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.53/0.96  fof(f322,plain,(
% 4.53/0.96    ( ! [X0] : (~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl2_3 | ~spl2_4)),
% 4.53/0.96    inference(resolution,[],[f317,f96])).
% 4.53/0.96  fof(f96,plain,(
% 4.53/0.96    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f68])).
% 4.53/0.96  fof(f68,plain,(
% 4.53/0.96    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.53/0.96    inference(nnf_transformation,[],[f24])).
% 4.53/0.96  fof(f24,axiom,(
% 4.53/0.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 4.53/0.96  fof(f317,plain,(
% 4.53/0.96    ( ! [X15] : (~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X15,sK0) | r1_tarski(X15,k1_tops_1(sK0,sK1)) | ~r1_tarski(X15,sK1)) ) | (~spl2_3 | ~spl2_4)),
% 4.53/0.96    inference(subsumption_resolution,[],[f315,f128])).
% 4.53/0.96  fof(f315,plain,(
% 4.53/0.96    ( ! [X15] : (~r1_tarski(X15,sK1) | ~v3_pre_topc(X15,sK0) | r1_tarski(X15,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_3),
% 4.53/0.96    inference(resolution,[],[f94,f123])).
% 4.53/0.96  fof(f94,plain,(
% 4.53/0.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f50])).
% 4.53/0.96  fof(f50,plain,(
% 4.53/0.96    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.53/0.96    inference(flattening,[],[f49])).
% 4.53/0.96  fof(f49,plain,(
% 4.53/0.96    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.53/0.96    inference(ennf_transformation,[],[f29])).
% 4.53/0.96  fof(f29,axiom,(
% 4.53/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 4.53/0.96  fof(f3595,plain,(
% 4.53/0.96    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl2_137),
% 4.53/0.96    inference(avatar_component_clause,[],[f3593])).
% 4.53/0.96  fof(f3573,plain,(
% 4.53/0.96    spl2_82 | ~spl2_3 | ~spl2_4),
% 4.53/0.96    inference(avatar_split_clause,[],[f3572,f126,f121,f2603])).
% 4.53/0.96  fof(f2603,plain,(
% 4.53/0.96    spl2_82 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).
% 4.53/0.96  fof(f3572,plain,(
% 4.53/0.96    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 4.53/0.96    inference(subsumption_resolution,[],[f3553,f128])).
% 4.53/0.96  fof(f3553,plain,(
% 4.53/0.96    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_3),
% 4.53/0.96    inference(resolution,[],[f876,f123])).
% 4.53/0.96  fof(f876,plain,(
% 4.53/0.96    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) | r1_tarski(X8,k2_pre_topc(X9,X8)) | ~l1_pre_topc(X9)) )),
% 4.53/0.96    inference(superposition,[],[f154,f289])).
% 4.53/0.96  fof(f289,plain,(
% 4.53/0.96    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 4.53/0.96    inference(subsumption_resolution,[],[f286,f92])).
% 4.53/0.96  fof(f286,plain,(
% 4.53/0.96    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 4.53/0.96    inference(duplicate_literal_removal,[],[f281])).
% 4.53/0.96  fof(f281,plain,(
% 4.53/0.96    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 4.53/0.96    inference(superposition,[],[f91,f103])).
% 4.53/0.96  fof(f103,plain,(
% 4.53/0.96    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.53/0.96    inference(cnf_transformation,[],[f56])).
% 4.53/0.96  fof(f56,plain,(
% 4.53/0.96    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.53/0.96    inference(flattening,[],[f55])).
% 4.53/0.96  fof(f55,plain,(
% 4.53/0.96    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.53/0.96    inference(ennf_transformation,[],[f19])).
% 4.53/0.96  fof(f19,axiom,(
% 4.53/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 4.53/0.96  fof(f154,plain,(
% 4.53/0.96    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X1,X2))) )),
% 4.53/0.96    inference(trivial_inequality_removal,[],[f153])).
% 4.53/0.96  fof(f153,plain,(
% 4.53/0.96    ( ! [X2,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X1,k2_xboole_0(X1,X2))) )),
% 4.53/0.96    inference(superposition,[],[f75,f84])).
% 4.53/0.96  fof(f84,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.53/0.96    inference(cnf_transformation,[],[f11])).
% 4.53/0.96  fof(f11,axiom,(
% 4.53/0.96    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 4.53/0.96  fof(f75,plain,(
% 4.53/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f65])).
% 4.53/0.96  fof(f65,plain,(
% 4.53/0.96    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.53/0.96    inference(nnf_transformation,[],[f3])).
% 4.53/0.96  fof(f3,axiom,(
% 4.53/0.96    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.53/0.96  fof(f3541,plain,(
% 4.53/0.96    spl2_78 | ~spl2_3 | ~spl2_4),
% 4.53/0.96    inference(avatar_split_clause,[],[f3540,f126,f121,f2521])).
% 4.53/0.96  fof(f3540,plain,(
% 4.53/0.96    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 4.53/0.96    inference(subsumption_resolution,[],[f3531,f128])).
% 4.53/0.96  fof(f3531,plain,(
% 4.53/0.96    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 4.53/0.96    inference(resolution,[],[f852,f123])).
% 4.53/0.96  fof(f852,plain,(
% 4.53/0.96    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) | r1_tarski(k1_tops_1(X9,X8),X8) | ~l1_pre_topc(X9)) )),
% 4.53/0.96    inference(superposition,[],[f100,f276])).
% 4.53/0.96  fof(f100,plain,(
% 4.53/0.96    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f8])).
% 4.53/0.96  fof(f8,axiom,(
% 4.53/0.96    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.53/0.96  fof(f2747,plain,(
% 4.53/0.96    ~spl2_82 | spl2_29),
% 4.53/0.96    inference(avatar_split_clause,[],[f2746,f826,f2603])).
% 4.53/0.96  fof(f2746,plain,(
% 4.53/0.96    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl2_29),
% 4.53/0.96    inference(resolution,[],[f828,f96])).
% 4.53/0.96  fof(f828,plain,(
% 4.53/0.96    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_29),
% 4.53/0.96    inference(avatar_component_clause,[],[f826])).
% 4.53/0.96  fof(f2729,plain,(
% 4.53/0.96    ~spl2_10 | spl2_2 | ~spl2_9),
% 4.53/0.96    inference(avatar_split_clause,[],[f2728,f227,f115,f231])).
% 4.53/0.96  fof(f2728,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl2_2 | ~spl2_9)),
% 4.53/0.96    inference(subsumption_resolution,[],[f2727,f228])).
% 4.53/0.96  fof(f2727,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 4.53/0.96    inference(superposition,[],[f117,f74])).
% 4.53/0.96  fof(f117,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 4.53/0.96    inference(avatar_component_clause,[],[f115])).
% 4.53/0.96  fof(f2667,plain,(
% 4.53/0.96    spl2_6 | ~spl2_3),
% 4.53/0.96    inference(avatar_split_clause,[],[f2665,f121,f147])).
% 4.53/0.96  fof(f2665,plain,(
% 4.53/0.96    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 4.53/0.96    inference(resolution,[],[f123,f95])).
% 4.53/0.96  fof(f95,plain,(
% 4.53/0.96    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f68])).
% 4.53/0.96  fof(f733,plain,(
% 4.53/0.96    ~spl2_3 | ~spl2_4 | spl2_9),
% 4.53/0.96    inference(avatar_contradiction_clause,[],[f732])).
% 4.53/0.96  fof(f732,plain,(
% 4.53/0.96    $false | (~spl2_3 | ~spl2_4 | spl2_9)),
% 4.53/0.96    inference(subsumption_resolution,[],[f731,f128])).
% 4.53/0.96  fof(f731,plain,(
% 4.53/0.96    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_9)),
% 4.53/0.96    inference(subsumption_resolution,[],[f724,f123])).
% 4.53/0.96  fof(f724,plain,(
% 4.53/0.96    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_9),
% 4.53/0.96    inference(resolution,[],[f291,f229])).
% 4.53/0.96  fof(f229,plain,(
% 4.53/0.96    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_9),
% 4.53/0.96    inference(avatar_component_clause,[],[f227])).
% 4.53/0.96  fof(f255,plain,(
% 4.53/0.96    spl2_12 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 4.53/0.96    inference(avatar_split_clause,[],[f250,f131,f126,f121,f252])).
% 4.53/0.96  fof(f252,plain,(
% 4.53/0.96    spl2_12 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 4.53/0.96  fof(f131,plain,(
% 4.53/0.96    spl2_5 <=> v2_pre_topc(sK0)),
% 4.53/0.96    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 4.53/0.96  fof(f250,plain,(
% 4.53/0.96    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 4.53/0.96    inference(subsumption_resolution,[],[f249,f133])).
% 4.53/0.96  fof(f133,plain,(
% 4.53/0.96    v2_pre_topc(sK0) | ~spl2_5),
% 4.53/0.96    inference(avatar_component_clause,[],[f131])).
% 4.53/0.96  fof(f249,plain,(
% 4.53/0.96    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl2_3 | ~spl2_4)),
% 4.53/0.96    inference(subsumption_resolution,[],[f247,f128])).
% 4.53/0.96  fof(f247,plain,(
% 4.53/0.96    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_3),
% 4.53/0.96    inference(resolution,[],[f93,f123])).
% 4.53/0.96  fof(f93,plain,(
% 4.53/0.96    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.53/0.96    inference(cnf_transformation,[],[f48])).
% 4.53/0.96  fof(f48,plain,(
% 4.53/0.96    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.53/0.96    inference(flattening,[],[f47])).
% 4.53/0.96  fof(f47,plain,(
% 4.53/0.96    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.53/0.96    inference(ennf_transformation,[],[f27])).
% 4.53/0.96  fof(f27,axiom,(
% 4.53/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 4.53/0.96  fof(f134,plain,(
% 4.53/0.96    spl2_5),
% 4.53/0.96    inference(avatar_split_clause,[],[f69,f131])).
% 4.53/0.96  fof(f69,plain,(
% 4.53/0.96    v2_pre_topc(sK0)),
% 4.53/0.96    inference(cnf_transformation,[],[f64])).
% 4.53/0.96  fof(f64,plain,(
% 4.53/0.96    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.53/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f61,f63,f62])).
% 4.53/0.96  fof(f62,plain,(
% 4.53/0.96    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.53/0.96    introduced(choice_axiom,[])).
% 4.53/0.96  fof(f63,plain,(
% 4.53/0.96    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.53/0.96    introduced(choice_axiom,[])).
% 4.53/0.96  fof(f61,plain,(
% 4.53/0.96    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.53/0.96    inference(flattening,[],[f60])).
% 4.53/0.96  fof(f60,plain,(
% 4.53/0.96    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.53/0.96    inference(nnf_transformation,[],[f36])).
% 4.53/0.96  fof(f36,plain,(
% 4.53/0.96    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.53/0.96    inference(flattening,[],[f35])).
% 4.53/0.96  fof(f35,plain,(
% 4.53/0.96    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.53/0.96    inference(ennf_transformation,[],[f34])).
% 4.53/0.96  fof(f34,negated_conjecture,(
% 4.53/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 4.53/0.96    inference(negated_conjecture,[],[f33])).
% 4.53/0.96  fof(f33,conjecture,(
% 4.53/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 4.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 4.53/0.96  fof(f129,plain,(
% 4.53/0.96    spl2_4),
% 4.53/0.96    inference(avatar_split_clause,[],[f70,f126])).
% 4.53/0.96  fof(f70,plain,(
% 4.53/0.96    l1_pre_topc(sK0)),
% 4.53/0.96    inference(cnf_transformation,[],[f64])).
% 4.53/0.96  fof(f124,plain,(
% 4.53/0.96    spl2_3),
% 4.53/0.96    inference(avatar_split_clause,[],[f71,f121])).
% 4.53/0.96  fof(f71,plain,(
% 4.53/0.96    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.53/0.96    inference(cnf_transformation,[],[f64])).
% 4.53/0.96  fof(f119,plain,(
% 4.53/0.96    spl2_1 | spl2_2),
% 4.53/0.96    inference(avatar_split_clause,[],[f72,f115,f111])).
% 4.53/0.96  fof(f72,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 4.53/0.96    inference(cnf_transformation,[],[f64])).
% 4.53/0.96  fof(f118,plain,(
% 4.53/0.96    ~spl2_1 | ~spl2_2),
% 4.53/0.96    inference(avatar_split_clause,[],[f73,f115,f111])).
% 4.53/0.96  fof(f73,plain,(
% 4.53/0.96    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 4.53/0.96    inference(cnf_transformation,[],[f64])).
% 4.53/0.96  % SZS output end Proof for theBenchmark
% 4.53/0.96  % (16803)------------------------------
% 4.53/0.96  % (16803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/0.96  % (16803)Termination reason: Refutation
% 4.53/0.96  
% 4.53/0.96  % (16803)Memory used [KB]: 9722
% 4.53/0.96  % (16803)Time elapsed: 0.554 s
% 4.53/0.96  % (16803)------------------------------
% 4.53/0.96  % (16803)------------------------------
% 4.53/0.96  % (16781)Success in time 0.603 s
%------------------------------------------------------------------------------
