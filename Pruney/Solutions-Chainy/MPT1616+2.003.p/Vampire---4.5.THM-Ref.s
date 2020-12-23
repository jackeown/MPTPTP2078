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
% DateTime   : Thu Dec  3 13:16:43 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 293 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :   31
%              Number of atoms          :  358 (1194 expanded)
%              Number of equality atoms :   45 ( 148 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(global_subsumption,[],[f52,f51,f310])).

fof(f310,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f307,f88])).

fof(f88,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f56,f70])).

fof(f70,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f31,f30,f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ( sP0(X0)
        & ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP1(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f56,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ v2_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP1(X0) )
        & ( sP1(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f307,plain,(
    ~ sP1(sK3) ),
    inference(resolution,[],[f306,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
          & r1_tarski(sK4(X0),u1_pre_topc(X0))
          & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X2] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r1_tarski(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
        & r1_tarski(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X1] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            & r1_tarski(X1,u1_pre_topc(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X2] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r1_tarski(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f306,plain,(
    ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK3)) ),
    inference(resolution,[],[f305,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ sP7(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f83,f86_D])).

fof(f86,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f86_D])).

fof(f86_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f305,plain,(
    sP7(u1_pre_topc(sK3)) ),
    inference(resolution,[],[f304,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f304,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_pre_topc(sK3))
      | sP7(X0) ) ),
    inference(resolution,[],[f303,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f303,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK3)))
      | sP7(X0) ) ),
    inference(global_subsumption,[],[f52,f51,f302])).

fof(f302,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK3)))
      | sP7(X0)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f289,f88])).

fof(f289,plain,(
    ! [X0] :
      ( ~ sP1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK3)))
      | sP7(X0) ) ),
    inference(resolution,[],[f288,f86])).

fof(f288,plain,
    ( v1_xboole_0(u1_pre_topc(sK3))
    | ~ sP1(sK3) ),
    inference(resolution,[],[f271,f58])).

fof(f271,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v1_xboole_0(u1_pre_topc(sK3)) ),
    inference(global_subsumption,[],[f53,f249])).

fof(f249,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | u1_struct_0(sK3) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK3)))
    | v1_xboole_0(u1_pre_topc(sK3)) ),
    inference(superposition,[],[f54,f247])).

fof(f247,plain,(
    u1_struct_0(sK3) = k3_tarski(u1_pre_topc(sK3)) ),
    inference(global_subsumption,[],[f52,f51,f246])).

fof(f246,plain,
    ( u1_struct_0(sK3) = k3_tarski(u1_pre_topc(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f244,f88])).

fof(f244,plain,
    ( ~ sP1(sK3)
    | u1_struct_0(sK3) = k3_tarski(u1_pre_topc(sK3)) ),
    inference(resolution,[],[f243,f114])).

fof(f114,plain,(
    ! [X0] :
      ( m1_setfam_1(u1_pre_topc(X0),u1_struct_0(X0))
      | ~ sP1(X0) ) ),
    inference(resolution,[],[f111,f58])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_setfam_1(X1,X0) ) ),
    inference(resolution,[],[f109,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f109,plain,(
    ! [X4,X3] :
      ( r1_tarski(X3,k3_tarski(X4))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f82,f84])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f243,plain,
    ( ~ m1_setfam_1(u1_pre_topc(sK3),u1_struct_0(sK3))
    | u1_struct_0(sK3) = k3_tarski(u1_pre_topc(sK3)) ),
    inference(global_subsumption,[],[f52,f242])).

fof(f242,plain,
    ( u1_struct_0(sK3) = k3_tarski(u1_pre_topc(sK3))
    | ~ m1_setfam_1(u1_pre_topc(sK3),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f183,f99])).

fof(f99,plain,(
    ! [X0] :
      ( r1_tarski(u1_pre_topc(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f55,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f183,plain,(
    ! [X17] :
      ( ~ r1_tarski(X17,k1_zfmisc_1(u1_struct_0(sK3)))
      | u1_struct_0(sK3) = k3_tarski(X17)
      | ~ m1_setfam_1(X17,u1_struct_0(sK3)) ) ),
    inference(superposition,[],[f124,f166])).

fof(f166,plain,(
    u1_struct_0(sK3) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_subsumption,[],[f52,f165])).

fof(f165,plain,
    ( u1_struct_0(sK3) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f162,f99])).

fof(f162,plain,
    ( ~ r1_tarski(u1_pre_topc(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f160,f155])).

fof(f155,plain,(
    ! [X0] :
      ( m1_setfam_1(X0,u1_struct_0(sK3))
      | ~ r1_tarski(u1_pre_topc(sK3),X0) ) ),
    inference(global_subsumption,[],[f52,f154])).

fof(f154,plain,(
    ! [X0] :
      ( m1_setfam_1(X0,u1_struct_0(sK3))
      | ~ r1_tarski(u1_pre_topc(sK3),X0)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f137,f51])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | m1_setfam_1(X1,u1_struct_0(X0))
      | ~ r1_tarski(u1_pre_topc(X0),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f135,f88])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ r1_tarski(u1_pre_topc(X0),X1)
      | m1_setfam_1(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f119,f79])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),k3_tarski(X1))
      | ~ r1_tarski(u1_pre_topc(X0),X1)
      | ~ sP1(X0) ) ),
    inference(resolution,[],[f108,f58])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X2))
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f82,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(k1_zfmisc_1(X0),X0)
      | k3_tarski(k1_zfmisc_1(X0)) = X0 ) ),
    inference(forward_demodulation,[],[f158,f122])).

fof(f122,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = k5_setfam_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f117,f84])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(X1))
      | k3_tarski(X0) = k5_setfam_1(X1,X0) ) ),
    inference(resolution,[],[f72,f81])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f158,plain,(
    ! [X0] :
      ( k5_setfam_1(X0,k1_zfmisc_1(X0)) = X0
      | ~ m1_setfam_1(k1_zfmisc_1(X0),X0) ) ),
    inference(resolution,[],[f156,f84])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(X1))
      | k5_setfam_1(X1,X0) = X1
      | ~ m1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f73,f81])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_setfam_1(X1,X0)
      | k5_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( m1_setfam_1(X1,X0)
          | k5_setfam_1(X0,X1) != X0 )
        & ( k5_setfam_1(X0,X1) = X0
          | ~ m1_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X0,k3_tarski(X1))
      | k3_tarski(X0) = k3_tarski(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f103,f71])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_tarski(X1),X2)
      | k3_tarski(X1) = X2
      | ~ m1_setfam_1(X1,X2) ) ),
    inference(resolution,[],[f77,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f53,plain,(
    u1_struct_0(sK3) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( u1_struct_0(sK3) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK3) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK3)))
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f51,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:24:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (9620)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (9620)Refutation not found, incomplete strategy% (9620)------------------------------
% 0.20/0.50  % (9620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9620)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (9620)Memory used [KB]: 10490
% 0.20/0.50  % (9620)Time elapsed: 0.081 s
% 0.20/0.50  % (9620)------------------------------
% 0.20/0.50  % (9620)------------------------------
% 0.20/0.50  % (9626)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (9618)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (9625)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.14/0.51  % (9626)Refutation found. Thanks to Tanya!
% 1.14/0.51  % SZS status Theorem for theBenchmark
% 1.14/0.51  % SZS output start Proof for theBenchmark
% 1.14/0.51  fof(f311,plain,(
% 1.14/0.51    $false),
% 1.14/0.51    inference(global_subsumption,[],[f52,f51,f310])).
% 1.14/0.52  fof(f310,plain,(
% 1.14/0.52    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3)),
% 1.14/0.52    inference(resolution,[],[f307,f88])).
% 1.14/0.52  fof(f88,plain,(
% 1.14/0.52    ( ! [X0] : (sP1(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.14/0.52    inference(resolution,[],[f56,f70])).
% 1.14/0.52  fof(f70,plain,(
% 1.14/0.52    ( ! [X0] : (sP2(X0) | ~l1_pre_topc(X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f32])).
% 1.14/0.52  fof(f32,plain,(
% 1.14/0.52    ! [X0] : (sP2(X0) | ~l1_pre_topc(X0))),
% 1.14/0.52    inference(definition_folding,[],[f22,f31,f30,f29])).
% 1.14/0.52  fof(f29,plain,(
% 1.14/0.52    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.14/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.14/0.52  fof(f30,plain,(
% 1.14/0.52    ! [X0] : (sP1(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 1.14/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.14/0.52  fof(f31,plain,(
% 1.14/0.52    ! [X0] : ((v2_pre_topc(X0) <=> sP1(X0)) | ~sP2(X0))),
% 1.14/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.14/0.52  fof(f22,plain,(
% 1.14/0.52    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.14/0.52    inference(flattening,[],[f21])).
% 1.14/0.52  fof(f21,plain,(
% 1.14/0.52    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.14/0.52    inference(ennf_transformation,[],[f14])).
% 1.14/0.52  fof(f14,plain,(
% 1.14/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.14/0.52    inference(rectify,[],[f9])).
% 1.14/0.52  fof(f9,axiom,(
% 1.14/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 1.14/0.52  fof(f56,plain,(
% 1.14/0.52    ( ! [X0] : (~sP2(X0) | ~v2_pre_topc(X0) | sP1(X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f35])).
% 1.14/0.52  fof(f35,plain,(
% 1.14/0.52    ! [X0] : (((v2_pre_topc(X0) | ~sP1(X0)) & (sP1(X0) | ~v2_pre_topc(X0))) | ~sP2(X0))),
% 1.14/0.52    inference(nnf_transformation,[],[f31])).
% 1.14/0.52  fof(f307,plain,(
% 1.14/0.52    ~sP1(sK3)),
% 1.14/0.52    inference(resolution,[],[f306,f58])).
% 1.14/0.52  fof(f58,plain,(
% 1.14/0.52    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP1(X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f40])).
% 1.14/0.52  fof(f40,plain,(
% 1.14/0.52    ! [X0] : ((sP1(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 1.14/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 1.14/0.52  fof(f39,plain,(
% 1.14/0.52    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.14/0.52    introduced(choice_axiom,[])).
% 1.14/0.52  fof(f38,plain,(
% 1.14/0.52    ! [X0] : ((sP1(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 1.14/0.52    inference(rectify,[],[f37])).
% 1.14/0.52  fof(f37,plain,(
% 1.14/0.52    ! [X0] : ((sP1(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 1.14/0.52    inference(flattening,[],[f36])).
% 1.14/0.52  fof(f36,plain,(
% 1.14/0.52    ! [X0] : ((sP1(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 1.14/0.52    inference(nnf_transformation,[],[f30])).
% 1.14/0.52  fof(f306,plain,(
% 1.14/0.52    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK3))) )),
% 1.14/0.52    inference(resolution,[],[f305,f87])).
% 1.14/0.52  fof(f87,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~sP7(X1) | ~r2_hidden(X0,X1)) )),
% 1.14/0.52    inference(general_splitting,[],[f83,f86_D])).
% 1.14/0.52  fof(f86,plain,(
% 1.14/0.52    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP7(X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f86_D])).
% 1.14/0.52  fof(f86_D,plain,(
% 1.14/0.52    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP7(X1)) )),
% 1.14/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.14/0.52  fof(f83,plain,(
% 1.14/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f28])).
% 1.14/0.52  fof(f28,plain,(
% 1.14/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.14/0.52    inference(ennf_transformation,[],[f7])).
% 1.14/0.52  fof(f7,axiom,(
% 1.14/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.14/0.52  fof(f305,plain,(
% 1.14/0.52    sP7(u1_pre_topc(sK3))),
% 1.14/0.52    inference(resolution,[],[f304,f84])).
% 1.14/0.52  fof(f84,plain,(
% 1.14/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.14/0.52    inference(equality_resolution,[],[f76])).
% 1.14/0.52  fof(f76,plain,(
% 1.14/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.14/0.52    inference(cnf_transformation,[],[f48])).
% 1.14/0.52  fof(f48,plain,(
% 1.14/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.14/0.52    inference(flattening,[],[f47])).
% 1.14/0.52  fof(f47,plain,(
% 1.14/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.14/0.52    inference(nnf_transformation,[],[f1])).
% 1.14/0.52  fof(f1,axiom,(
% 1.14/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.14/0.52  fof(f304,plain,(
% 1.14/0.52    ( ! [X0] : (~r1_tarski(X0,u1_pre_topc(sK3)) | sP7(X0)) )),
% 1.14/0.52    inference(resolution,[],[f303,f81])).
% 1.14/0.52  fof(f81,plain,(
% 1.14/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f50])).
% 1.14/0.52  fof(f50,plain,(
% 1.14/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.14/0.52    inference(nnf_transformation,[],[f5])).
% 1.14/0.52  fof(f5,axiom,(
% 1.14/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.14/0.52  fof(f303,plain,(
% 1.14/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK3))) | sP7(X0)) )),
% 1.14/0.52    inference(global_subsumption,[],[f52,f51,f302])).
% 1.14/0.52  fof(f302,plain,(
% 1.14/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK3))) | sP7(X0) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3)) )),
% 1.14/0.52    inference(resolution,[],[f289,f88])).
% 1.14/0.52  fof(f289,plain,(
% 1.14/0.52    ( ! [X0] : (~sP1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK3))) | sP7(X0)) )),
% 1.14/0.52    inference(resolution,[],[f288,f86])).
% 1.14/0.52  fof(f288,plain,(
% 1.14/0.52    v1_xboole_0(u1_pre_topc(sK3)) | ~sP1(sK3)),
% 1.14/0.52    inference(resolution,[],[f271,f58])).
% 1.14/0.52  fof(f271,plain,(
% 1.14/0.52    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | v1_xboole_0(u1_pre_topc(sK3))),
% 1.14/0.52    inference(global_subsumption,[],[f53,f249])).
% 1.14/0.52  fof(f249,plain,(
% 1.14/0.52    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | u1_struct_0(sK3) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK3))) | v1_xboole_0(u1_pre_topc(sK3))),
% 1.14/0.52    inference(superposition,[],[f54,f247])).
% 1.14/0.52  fof(f247,plain,(
% 1.14/0.52    u1_struct_0(sK3) = k3_tarski(u1_pre_topc(sK3))),
% 1.14/0.52    inference(global_subsumption,[],[f52,f51,f246])).
% 1.14/0.52  fof(f246,plain,(
% 1.14/0.52    u1_struct_0(sK3) = k3_tarski(u1_pre_topc(sK3)) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3)),
% 1.14/0.52    inference(resolution,[],[f244,f88])).
% 1.14/0.52  fof(f244,plain,(
% 1.14/0.52    ~sP1(sK3) | u1_struct_0(sK3) = k3_tarski(u1_pre_topc(sK3))),
% 1.14/0.52    inference(resolution,[],[f243,f114])).
% 1.14/0.52  fof(f114,plain,(
% 1.14/0.52    ( ! [X0] : (m1_setfam_1(u1_pre_topc(X0),u1_struct_0(X0)) | ~sP1(X0)) )),
% 1.14/0.52    inference(resolution,[],[f111,f58])).
% 1.14/0.52  fof(f111,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_setfam_1(X1,X0)) )),
% 1.14/0.52    inference(resolution,[],[f109,f79])).
% 1.14/0.52  fof(f79,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) | m1_setfam_1(X1,X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f49])).
% 1.14/0.52  fof(f49,plain,(
% 1.14/0.52    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 1.14/0.52    inference(nnf_transformation,[],[f3])).
% 1.14/0.52  fof(f3,axiom,(
% 1.14/0.52    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 1.14/0.52  fof(f109,plain,(
% 1.14/0.52    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(X4)) | ~r2_hidden(X3,X4)) )),
% 1.14/0.52    inference(resolution,[],[f82,f84])).
% 1.14/0.52  fof(f82,plain,(
% 1.14/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f27])).
% 1.14/0.52  fof(f27,plain,(
% 1.14/0.52    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 1.14/0.52    inference(flattening,[],[f26])).
% 1.14/0.52  fof(f26,plain,(
% 1.14/0.52    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 1.14/0.52    inference(ennf_transformation,[],[f6])).
% 1.14/0.52  fof(f6,axiom,(
% 1.14/0.52    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).
% 1.14/0.52  fof(f243,plain,(
% 1.14/0.52    ~m1_setfam_1(u1_pre_topc(sK3),u1_struct_0(sK3)) | u1_struct_0(sK3) = k3_tarski(u1_pre_topc(sK3))),
% 1.14/0.52    inference(global_subsumption,[],[f52,f242])).
% 1.14/0.52  fof(f242,plain,(
% 1.14/0.52    u1_struct_0(sK3) = k3_tarski(u1_pre_topc(sK3)) | ~m1_setfam_1(u1_pre_topc(sK3),u1_struct_0(sK3)) | ~l1_pre_topc(sK3)),
% 1.14/0.52    inference(resolution,[],[f183,f99])).
% 1.14/0.52  fof(f99,plain,(
% 1.14/0.52    ( ! [X0] : (r1_tarski(u1_pre_topc(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.14/0.52    inference(resolution,[],[f55,f80])).
% 1.14/0.52  fof(f80,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f50])).
% 1.14/0.52  fof(f55,plain,(
% 1.14/0.52    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f20])).
% 1.14/0.52  fof(f20,plain,(
% 1.14/0.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.14/0.52    inference(ennf_transformation,[],[f10])).
% 1.14/0.52  fof(f10,axiom,(
% 1.14/0.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.14/0.52  fof(f183,plain,(
% 1.14/0.52    ( ! [X17] : (~r1_tarski(X17,k1_zfmisc_1(u1_struct_0(sK3))) | u1_struct_0(sK3) = k3_tarski(X17) | ~m1_setfam_1(X17,u1_struct_0(sK3))) )),
% 1.14/0.52    inference(superposition,[],[f124,f166])).
% 1.14/0.52  fof(f166,plain,(
% 1.14/0.52    u1_struct_0(sK3) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.14/0.52    inference(global_subsumption,[],[f52,f165])).
% 1.14/0.52  fof(f165,plain,(
% 1.14/0.52    u1_struct_0(sK3) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3)),
% 1.14/0.52    inference(resolution,[],[f162,f99])).
% 1.14/0.52  fof(f162,plain,(
% 1.14/0.52    ~r1_tarski(u1_pre_topc(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | u1_struct_0(sK3) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.14/0.52    inference(resolution,[],[f160,f155])).
% 1.14/0.52  fof(f155,plain,(
% 1.14/0.52    ( ! [X0] : (m1_setfam_1(X0,u1_struct_0(sK3)) | ~r1_tarski(u1_pre_topc(sK3),X0)) )),
% 1.14/0.52    inference(global_subsumption,[],[f52,f154])).
% 1.14/0.52  fof(f154,plain,(
% 1.14/0.52    ( ! [X0] : (m1_setfam_1(X0,u1_struct_0(sK3)) | ~r1_tarski(u1_pre_topc(sK3),X0) | ~l1_pre_topc(sK3)) )),
% 1.14/0.52    inference(resolution,[],[f137,f51])).
% 1.14/0.52  fof(f137,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | m1_setfam_1(X1,u1_struct_0(X0)) | ~r1_tarski(u1_pre_topc(X0),X1) | ~l1_pre_topc(X0)) )),
% 1.14/0.52    inference(resolution,[],[f135,f88])).
% 1.14/0.52  fof(f135,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~sP1(X0) | ~r1_tarski(u1_pre_topc(X0),X1) | m1_setfam_1(X1,u1_struct_0(X0))) )),
% 1.14/0.52    inference(resolution,[],[f119,f79])).
% 1.14/0.52  fof(f119,plain,(
% 1.14/0.52    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),k3_tarski(X1)) | ~r1_tarski(u1_pre_topc(X0),X1) | ~sP1(X0)) )),
% 1.14/0.52    inference(resolution,[],[f108,f58])).
% 1.14/0.52  fof(f108,plain,(
% 1.14/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X2)) | ~r1_tarski(X1,X2)) )),
% 1.14/0.52    inference(resolution,[],[f82,f71])).
% 1.14/0.52  fof(f71,plain,(
% 1.14/0.52    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f23])).
% 1.14/0.52  fof(f23,plain,(
% 1.14/0.52    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 1.14/0.52    inference(ennf_transformation,[],[f2])).
% 1.14/0.52  fof(f2,axiom,(
% 1.14/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 1.14/0.52  fof(f160,plain,(
% 1.14/0.52    ( ! [X0] : (~m1_setfam_1(k1_zfmisc_1(X0),X0) | k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.14/0.52    inference(forward_demodulation,[],[f158,f122])).
% 1.14/0.52  fof(f122,plain,(
% 1.14/0.52    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = k5_setfam_1(X0,k1_zfmisc_1(X0))) )),
% 1.14/0.52    inference(resolution,[],[f117,f84])).
% 1.14/0.52  fof(f117,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_zfmisc_1(X1)) | k3_tarski(X0) = k5_setfam_1(X1,X0)) )),
% 1.14/0.52    inference(resolution,[],[f72,f81])).
% 1.14/0.52  fof(f72,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f24])).
% 1.14/0.52  fof(f24,plain,(
% 1.14/0.52    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.14/0.52    inference(ennf_transformation,[],[f4])).
% 1.14/0.52  fof(f4,axiom,(
% 1.14/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 1.14/0.52  fof(f158,plain,(
% 1.14/0.52    ( ! [X0] : (k5_setfam_1(X0,k1_zfmisc_1(X0)) = X0 | ~m1_setfam_1(k1_zfmisc_1(X0),X0)) )),
% 1.14/0.52    inference(resolution,[],[f156,f84])).
% 1.14/0.52  fof(f156,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_zfmisc_1(X1)) | k5_setfam_1(X1,X0) = X1 | ~m1_setfam_1(X0,X1)) )),
% 1.14/0.52    inference(resolution,[],[f73,f81])).
% 1.14/0.52  fof(f73,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) = X0) )),
% 1.14/0.52    inference(cnf_transformation,[],[f46])).
% 1.14/0.52  fof(f46,plain,(
% 1.14/0.52    ! [X0,X1] : (((m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) != X0) & (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.14/0.52    inference(nnf_transformation,[],[f25])).
% 1.14/0.52  fof(f25,plain,(
% 1.14/0.52    ! [X0,X1] : ((m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.14/0.52    inference(ennf_transformation,[],[f8])).
% 1.14/0.52  fof(f8,axiom,(
% 1.14/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).
% 1.14/0.52  fof(f124,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~m1_setfam_1(X0,k3_tarski(X1)) | k3_tarski(X0) = k3_tarski(X1) | ~r1_tarski(X0,X1)) )),
% 1.14/0.52    inference(resolution,[],[f103,f71])).
% 1.14/0.52  fof(f103,plain,(
% 1.14/0.52    ( ! [X2,X1] : (~r1_tarski(k3_tarski(X1),X2) | k3_tarski(X1) = X2 | ~m1_setfam_1(X1,X2)) )),
% 1.14/0.52    inference(resolution,[],[f77,f78])).
% 1.14/0.52  fof(f78,plain,(
% 1.14/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f49])).
% 1.14/0.52  fof(f77,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f48])).
% 1.14/0.52  fof(f54,plain,(
% 1.14/0.52    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f19])).
% 1.14/0.52  fof(f19,plain,(
% 1.14/0.52    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 1.14/0.52    inference(flattening,[],[f18])).
% 1.14/0.52  fof(f18,plain,(
% 1.14/0.52    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 1.14/0.52    inference(ennf_transformation,[],[f11])).
% 1.14/0.52  fof(f11,axiom,(
% 1.14/0.52    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 1.14/0.52  fof(f53,plain,(
% 1.14/0.52    u1_struct_0(sK3) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK3)))),
% 1.14/0.52    inference(cnf_transformation,[],[f34])).
% 1.14/0.52  fof(f34,plain,(
% 1.14/0.52    u1_struct_0(sK3) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 1.14/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f33])).
% 1.14/0.52  fof(f33,plain,(
% 1.14/0.52    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK3) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 1.14/0.52    introduced(choice_axiom,[])).
% 1.14/0.52  fof(f17,plain,(
% 1.14/0.52    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.14/0.52    inference(flattening,[],[f16])).
% 1.14/0.52  fof(f16,plain,(
% 1.14/0.52    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.14/0.52    inference(ennf_transformation,[],[f15])).
% 1.14/0.52  fof(f15,plain,(
% 1.14/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.14/0.52    inference(pure_predicate_removal,[],[f13])).
% 1.14/0.52  fof(f13,negated_conjecture,(
% 1.14/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.14/0.52    inference(negated_conjecture,[],[f12])).
% 1.14/0.52  fof(f12,conjecture,(
% 1.14/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).
% 1.14/0.52  fof(f51,plain,(
% 1.14/0.52    v2_pre_topc(sK3)),
% 1.14/0.52    inference(cnf_transformation,[],[f34])).
% 1.14/0.52  fof(f52,plain,(
% 1.14/0.52    l1_pre_topc(sK3)),
% 1.14/0.52    inference(cnf_transformation,[],[f34])).
% 1.14/0.52  % SZS output end Proof for theBenchmark
% 1.14/0.52  % (9626)------------------------------
% 1.14/0.52  % (9626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.52  % (9626)Termination reason: Refutation
% 1.14/0.52  
% 1.14/0.52  % (9626)Memory used [KB]: 6524
% 1.14/0.52  % (9626)Time elapsed: 0.102 s
% 1.14/0.52  % (9626)------------------------------
% 1.14/0.52  % (9626)------------------------------
% 1.14/0.52  % (9612)Success in time 0.156 s
%------------------------------------------------------------------------------
