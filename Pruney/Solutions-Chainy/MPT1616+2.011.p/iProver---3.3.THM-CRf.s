%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:27 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 168 expanded)
%              Number of clauses        :   60 (  63 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  487 ( 739 expanded)
%              Number of equality atoms :   90 ( 136 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f48,f47,f46])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK2(X0,X1),X3)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f98,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(rectify,[],[f11])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f27,f36])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
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
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
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
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
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
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0))
        & r1_tarski(sK8(X0),u1_pre_topc(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0))
            & r1_tarski(sK8(X0),u1_pre_topc(X0))
            & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f59,f60])).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
      & l1_pre_topc(sK9)
      & v2_pre_topc(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
    & l1_pre_topc(sK9)
    & v2_pre_topc(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f35,f62])).

fof(f102,plain,(
    u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1972,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_24020,plain,
    ( ~ m1_subset_1(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(X0))
    | r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1972])).

cnf(c_24022,plain,
    ( ~ m1_subset_1(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
    | r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
    | v1_xboole_0(u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_24020])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2135,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
    | ~ r2_hidden(X0,X1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2666,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
    | ~ r2_hidden(X0,u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_10153,plain,
    ( m1_subset_1(sK3(u1_pre_topc(sK9),u1_struct_0(sK9)),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
    | ~ r2_hidden(sK3(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_2666])).

cnf(c_2776,plain,
    ( m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_10095,plain,
    ( ~ m1_subset_1(sK3(u1_pre_topc(sK9),u1_struct_0(sK9)),k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(X0))
    | ~ r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),sK3(u1_pre_topc(sK9),u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_2776])).

cnf(c_10097,plain,
    ( ~ m1_subset_1(sK3(u1_pre_topc(sK9),u1_struct_0(sK9)),k1_zfmisc_1(u1_struct_0(sK9)))
    | m1_subset_1(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
    | ~ r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),sK3(u1_pre_topc(sK9),u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_10095])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(X1,X2),X0)
    | ~ r2_hidden(sK2(X1,X2),X2)
    | k3_tarski(X1) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2701,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(X1,u1_struct_0(X2)),X0)
    | ~ r2_hidden(sK2(X1,u1_struct_0(X2)),u1_struct_0(X2))
    | k3_tarski(X1) = u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7209,plain,
    ( ~ r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(X0)),u1_struct_0(X0))
    | ~ r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(X0)),u1_struct_0(sK9))
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2701])).

cnf(c_7211,plain,
    ( ~ r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_7209])).

cnf(c_1205,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1802,plain,
    ( X0 != X1
    | u1_struct_0(sK9) != X1
    | u1_struct_0(sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_1934,plain,
    ( X0 != u1_struct_0(sK9)
    | u1_struct_0(sK9) = X0
    | u1_struct_0(sK9) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_2087,plain,
    ( u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK9) = k3_tarski(X0)
    | k3_tarski(X0) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_5682,plain,
    ( u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK9) = k3_tarski(u1_pre_topc(sK9))
    | k3_tarski(u1_pre_topc(sK9)) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2087])).

cnf(c_1892,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != X0
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = u1_struct_0(X1)
    | u1_struct_0(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_5343,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = u1_struct_0(X0)
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != k3_tarski(u1_pre_topc(sK9))
    | u1_struct_0(X0) != k3_tarski(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_5344,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = u1_struct_0(sK9)
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != k3_tarski(u1_pre_topc(sK9))
    | u1_struct_0(sK9) != k3_tarski(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_5343])).

cnf(c_6,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r2_hidden(sK2(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2501,plain,
    ( r2_hidden(sK3(X0,u1_struct_0(sK9)),X0)
    | r2_hidden(sK2(X0,u1_struct_0(sK9)),u1_struct_0(sK9))
    | k3_tarski(X0) = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3918,plain,
    ( r2_hidden(sK3(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_pre_topc(sK9))
    | r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
    | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2501])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),sK3(X0,X1))
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2500,plain,
    ( r2_hidden(sK2(X0,u1_struct_0(sK9)),sK3(X0,u1_struct_0(sK9)))
    | r2_hidden(sK2(X0,u1_struct_0(sK9)),u1_struct_0(sK9))
    | k3_tarski(X0) = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3909,plain,
    ( r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),sK3(u1_pre_topc(sK9),u1_struct_0(sK9)))
    | r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
    | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2500])).

cnf(c_1207,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1954,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
    | u1_pre_topc(sK9) != X1
    | k3_tarski(u1_pre_topc(sK9)) != X0 ),
    inference(instantiation,[status(thm)],[c_1207])).

cnf(c_2282,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK9))
    | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
    | u1_pre_topc(sK9) != u1_pre_topc(sK9)
    | k3_tarski(u1_pre_topc(sK9)) != X0 ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_2898,plain,
    ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
    | u1_pre_topc(sK9) != u1_pre_topc(sK9)
    | k3_tarski(u1_pre_topc(sK9)) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2282])).

cnf(c_34,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1838,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
    | v1_xboole_0(u1_pre_topc(sK9))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = k3_tarski(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1765,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != X0
    | u1_struct_0(sK9) != X0
    | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_1808,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != u1_struct_0(sK9)
    | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
    | u1_struct_0(sK9) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1765])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1787,plain,
    ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ v1_xboole_0(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1215,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_1228,plain,
    ( u1_pre_topc(sK9) = u1_pre_topc(sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_1213,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1226,plain,
    ( u1_struct_0(sK9) = u1_struct_0(sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1213])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_129,plain,
    ( ~ r1_tarski(sK9,sK9)
    | sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_125,plain,
    ( r1_tarski(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_30,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_55,plain,
    ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_31,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_52,plain,
    ( l1_struct_0(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_32,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_49,plain,
    ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
    | ~ l1_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_33,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_46,plain,
    ( v2_struct_0(sK9)
    | ~ l1_struct_0(sK9)
    | ~ v1_xboole_0(u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_35,negated_conjecture,
    ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f99])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24022,c_10153,c_10097,c_7211,c_5682,c_5344,c_3918,c_3909,c_2898,c_1838,c_1808,c_1787,c_1228,c_1226,c_129,c_125,c_55,c_52,c_49,c_46,c_35,c_36,c_37,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.73/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.73/1.52  
% 7.73/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.52  
% 7.73/1.52  ------  iProver source info
% 7.73/1.52  
% 7.73/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.52  git: non_committed_changes: false
% 7.73/1.52  git: last_make_outside_of_git: false
% 7.73/1.52  
% 7.73/1.52  ------ 
% 7.73/1.52  
% 7.73/1.52  ------ Input Options
% 7.73/1.52  
% 7.73/1.52  --out_options                           all
% 7.73/1.52  --tptp_safe_out                         true
% 7.73/1.52  --problem_path                          ""
% 7.73/1.52  --include_path                          ""
% 7.73/1.52  --clausifier                            res/vclausify_rel
% 7.73/1.52  --clausifier_options                    ""
% 7.73/1.52  --stdin                                 false
% 7.73/1.52  --stats_out                             all
% 7.73/1.52  
% 7.73/1.52  ------ General Options
% 7.73/1.52  
% 7.73/1.52  --fof                                   false
% 7.73/1.52  --time_out_real                         305.
% 7.73/1.52  --time_out_virtual                      -1.
% 7.73/1.52  --symbol_type_check                     false
% 7.73/1.52  --clausify_out                          false
% 7.73/1.52  --sig_cnt_out                           false
% 7.73/1.52  --trig_cnt_out                          false
% 7.73/1.52  --trig_cnt_out_tolerance                1.
% 7.73/1.52  --trig_cnt_out_sk_spl                   false
% 7.73/1.52  --abstr_cl_out                          false
% 7.73/1.52  
% 7.73/1.52  ------ Global Options
% 7.73/1.52  
% 7.73/1.52  --schedule                              default
% 7.73/1.52  --add_important_lit                     false
% 7.73/1.52  --prop_solver_per_cl                    1000
% 7.73/1.52  --min_unsat_core                        false
% 7.73/1.52  --soft_assumptions                      false
% 7.73/1.52  --soft_lemma_size                       3
% 7.73/1.52  --prop_impl_unit_size                   0
% 7.73/1.52  --prop_impl_unit                        []
% 7.73/1.52  --share_sel_clauses                     true
% 7.73/1.52  --reset_solvers                         false
% 7.73/1.52  --bc_imp_inh                            [conj_cone]
% 7.73/1.52  --conj_cone_tolerance                   3.
% 7.73/1.52  --extra_neg_conj                        none
% 7.73/1.52  --large_theory_mode                     true
% 7.73/1.52  --prolific_symb_bound                   200
% 7.73/1.52  --lt_threshold                          2000
% 7.73/1.52  --clause_weak_htbl                      true
% 7.73/1.52  --gc_record_bc_elim                     false
% 7.73/1.52  
% 7.73/1.52  ------ Preprocessing Options
% 7.73/1.52  
% 7.73/1.52  --preprocessing_flag                    true
% 7.73/1.52  --time_out_prep_mult                    0.1
% 7.73/1.52  --splitting_mode                        input
% 7.73/1.52  --splitting_grd                         true
% 7.73/1.52  --splitting_cvd                         false
% 7.73/1.52  --splitting_cvd_svl                     false
% 7.73/1.52  --splitting_nvd                         32
% 7.73/1.52  --sub_typing                            true
% 7.73/1.52  --prep_gs_sim                           true
% 7.73/1.52  --prep_unflatten                        true
% 7.73/1.52  --prep_res_sim                          true
% 7.73/1.52  --prep_upred                            true
% 7.73/1.52  --prep_sem_filter                       exhaustive
% 7.73/1.52  --prep_sem_filter_out                   false
% 7.73/1.52  --pred_elim                             true
% 7.73/1.52  --res_sim_input                         true
% 7.73/1.52  --eq_ax_congr_red                       true
% 7.73/1.52  --pure_diseq_elim                       true
% 7.73/1.52  --brand_transform                       false
% 7.73/1.52  --non_eq_to_eq                          false
% 7.73/1.52  --prep_def_merge                        true
% 7.73/1.52  --prep_def_merge_prop_impl              false
% 7.73/1.52  --prep_def_merge_mbd                    true
% 7.73/1.52  --prep_def_merge_tr_red                 false
% 7.73/1.52  --prep_def_merge_tr_cl                  false
% 7.73/1.52  --smt_preprocessing                     true
% 7.73/1.52  --smt_ac_axioms                         fast
% 7.73/1.52  --preprocessed_out                      false
% 7.73/1.52  --preprocessed_stats                    false
% 7.73/1.52  
% 7.73/1.52  ------ Abstraction refinement Options
% 7.73/1.52  
% 7.73/1.52  --abstr_ref                             []
% 7.73/1.52  --abstr_ref_prep                        false
% 7.73/1.52  --abstr_ref_until_sat                   false
% 7.73/1.52  --abstr_ref_sig_restrict                funpre
% 7.73/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.52  --abstr_ref_under                       []
% 7.73/1.52  
% 7.73/1.52  ------ SAT Options
% 7.73/1.52  
% 7.73/1.52  --sat_mode                              false
% 7.73/1.52  --sat_fm_restart_options                ""
% 7.73/1.52  --sat_gr_def                            false
% 7.73/1.52  --sat_epr_types                         true
% 7.73/1.52  --sat_non_cyclic_types                  false
% 7.73/1.52  --sat_finite_models                     false
% 7.73/1.52  --sat_fm_lemmas                         false
% 7.73/1.52  --sat_fm_prep                           false
% 7.73/1.52  --sat_fm_uc_incr                        true
% 7.73/1.52  --sat_out_model                         small
% 7.73/1.52  --sat_out_clauses                       false
% 7.73/1.52  
% 7.73/1.52  ------ QBF Options
% 7.73/1.52  
% 7.73/1.52  --qbf_mode                              false
% 7.73/1.52  --qbf_elim_univ                         false
% 7.73/1.52  --qbf_dom_inst                          none
% 7.73/1.52  --qbf_dom_pre_inst                      false
% 7.73/1.52  --qbf_sk_in                             false
% 7.73/1.52  --qbf_pred_elim                         true
% 7.73/1.52  --qbf_split                             512
% 7.73/1.52  
% 7.73/1.52  ------ BMC1 Options
% 7.73/1.52  
% 7.73/1.52  --bmc1_incremental                      false
% 7.73/1.52  --bmc1_axioms                           reachable_all
% 7.73/1.52  --bmc1_min_bound                        0
% 7.73/1.52  --bmc1_max_bound                        -1
% 7.73/1.52  --bmc1_max_bound_default                -1
% 7.73/1.52  --bmc1_symbol_reachability              true
% 7.73/1.52  --bmc1_property_lemmas                  false
% 7.73/1.52  --bmc1_k_induction                      false
% 7.73/1.52  --bmc1_non_equiv_states                 false
% 7.73/1.52  --bmc1_deadlock                         false
% 7.73/1.52  --bmc1_ucm                              false
% 7.73/1.52  --bmc1_add_unsat_core                   none
% 7.73/1.52  --bmc1_unsat_core_children              false
% 7.73/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.52  --bmc1_out_stat                         full
% 7.73/1.52  --bmc1_ground_init                      false
% 7.73/1.52  --bmc1_pre_inst_next_state              false
% 7.73/1.52  --bmc1_pre_inst_state                   false
% 7.73/1.52  --bmc1_pre_inst_reach_state             false
% 7.73/1.52  --bmc1_out_unsat_core                   false
% 7.73/1.52  --bmc1_aig_witness_out                  false
% 7.73/1.52  --bmc1_verbose                          false
% 7.73/1.52  --bmc1_dump_clauses_tptp                false
% 7.73/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.52  --bmc1_dump_file                        -
% 7.73/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.52  --bmc1_ucm_extend_mode                  1
% 7.73/1.52  --bmc1_ucm_init_mode                    2
% 7.73/1.52  --bmc1_ucm_cone_mode                    none
% 7.73/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.52  --bmc1_ucm_relax_model                  4
% 7.73/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.52  --bmc1_ucm_layered_model                none
% 7.73/1.52  --bmc1_ucm_max_lemma_size               10
% 7.73/1.52  
% 7.73/1.52  ------ AIG Options
% 7.73/1.52  
% 7.73/1.52  --aig_mode                              false
% 7.73/1.52  
% 7.73/1.52  ------ Instantiation Options
% 7.73/1.52  
% 7.73/1.52  --instantiation_flag                    true
% 7.73/1.52  --inst_sos_flag                         true
% 7.73/1.52  --inst_sos_phase                        true
% 7.73/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.52  --inst_lit_sel_side                     num_symb
% 7.73/1.52  --inst_solver_per_active                1400
% 7.73/1.52  --inst_solver_calls_frac                1.
% 7.73/1.52  --inst_passive_queue_type               priority_queues
% 7.73/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.52  --inst_passive_queues_freq              [25;2]
% 7.73/1.52  --inst_dismatching                      true
% 7.73/1.52  --inst_eager_unprocessed_to_passive     true
% 7.73/1.52  --inst_prop_sim_given                   true
% 7.73/1.52  --inst_prop_sim_new                     false
% 7.73/1.52  --inst_subs_new                         false
% 7.73/1.52  --inst_eq_res_simp                      false
% 7.73/1.52  --inst_subs_given                       false
% 7.73/1.52  --inst_orphan_elimination               true
% 7.73/1.52  --inst_learning_loop_flag               true
% 7.73/1.52  --inst_learning_start                   3000
% 7.73/1.52  --inst_learning_factor                  2
% 7.73/1.52  --inst_start_prop_sim_after_learn       3
% 7.73/1.52  --inst_sel_renew                        solver
% 7.73/1.52  --inst_lit_activity_flag                true
% 7.73/1.52  --inst_restr_to_given                   false
% 7.73/1.52  --inst_activity_threshold               500
% 7.73/1.52  --inst_out_proof                        true
% 7.73/1.52  
% 7.73/1.52  ------ Resolution Options
% 7.73/1.52  
% 7.73/1.52  --resolution_flag                       true
% 7.73/1.52  --res_lit_sel                           adaptive
% 7.73/1.52  --res_lit_sel_side                      none
% 7.73/1.52  --res_ordering                          kbo
% 7.73/1.52  --res_to_prop_solver                    active
% 7.73/1.52  --res_prop_simpl_new                    false
% 7.73/1.52  --res_prop_simpl_given                  true
% 7.73/1.52  --res_passive_queue_type                priority_queues
% 7.73/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.52  --res_passive_queues_freq               [15;5]
% 7.73/1.52  --res_forward_subs                      full
% 7.73/1.52  --res_backward_subs                     full
% 7.73/1.52  --res_forward_subs_resolution           true
% 7.73/1.52  --res_backward_subs_resolution          true
% 7.73/1.52  --res_orphan_elimination                true
% 7.73/1.52  --res_time_limit                        2.
% 7.73/1.52  --res_out_proof                         true
% 7.73/1.52  
% 7.73/1.52  ------ Superposition Options
% 7.73/1.52  
% 7.73/1.52  --superposition_flag                    true
% 7.73/1.52  --sup_passive_queue_type                priority_queues
% 7.73/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.52  --demod_completeness_check              fast
% 7.73/1.52  --demod_use_ground                      true
% 7.73/1.52  --sup_to_prop_solver                    passive
% 7.73/1.52  --sup_prop_simpl_new                    true
% 7.73/1.52  --sup_prop_simpl_given                  true
% 7.73/1.52  --sup_fun_splitting                     true
% 7.73/1.52  --sup_smt_interval                      50000
% 7.73/1.52  
% 7.73/1.52  ------ Superposition Simplification Setup
% 7.73/1.52  
% 7.73/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.73/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.73/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.73/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.73/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.73/1.52  --sup_immed_triv                        [TrivRules]
% 7.73/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.52  --sup_immed_bw_main                     []
% 7.73/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.73/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.52  --sup_input_bw                          []
% 7.73/1.52  
% 7.73/1.52  ------ Combination Options
% 7.73/1.52  
% 7.73/1.52  --comb_res_mult                         3
% 7.73/1.52  --comb_sup_mult                         2
% 7.73/1.52  --comb_inst_mult                        10
% 7.73/1.52  
% 7.73/1.52  ------ Debug Options
% 7.73/1.52  
% 7.73/1.52  --dbg_backtrace                         false
% 7.73/1.52  --dbg_dump_prop_clauses                 false
% 7.73/1.52  --dbg_dump_prop_clauses_file            -
% 7.73/1.52  --dbg_out_stat                          false
% 7.73/1.52  ------ Parsing...
% 7.73/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.52  
% 7.73/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.73/1.52  
% 7.73/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.52  
% 7.73/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.52  ------ Proving...
% 7.73/1.52  ------ Problem Properties 
% 7.73/1.52  
% 7.73/1.52  
% 7.73/1.52  clauses                                 31
% 7.73/1.52  conjectures                             1
% 7.73/1.52  EPR                                     6
% 7.73/1.52  Horn                                    21
% 7.73/1.52  unary                                   8
% 7.73/1.52  binary                                  13
% 7.73/1.52  lits                                    68
% 7.73/1.52  lits eq                                 7
% 7.73/1.52  fd_pure                                 0
% 7.73/1.52  fd_pseudo                               0
% 7.73/1.52  fd_cond                                 0
% 7.73/1.52  fd_pseudo_cond                          4
% 7.73/1.52  AC symbols                              0
% 7.73/1.52  
% 7.73/1.52  ------ Schedule dynamic 5 is on 
% 7.73/1.52  
% 7.73/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.73/1.52  
% 7.73/1.52  
% 7.73/1.52  ------ 
% 7.73/1.52  Current options:
% 7.73/1.52  ------ 
% 7.73/1.52  
% 7.73/1.52  ------ Input Options
% 7.73/1.52  
% 7.73/1.52  --out_options                           all
% 7.73/1.52  --tptp_safe_out                         true
% 7.73/1.52  --problem_path                          ""
% 7.73/1.52  --include_path                          ""
% 7.73/1.52  --clausifier                            res/vclausify_rel
% 7.73/1.52  --clausifier_options                    ""
% 7.73/1.52  --stdin                                 false
% 7.73/1.52  --stats_out                             all
% 7.73/1.52  
% 7.73/1.52  ------ General Options
% 7.73/1.52  
% 7.73/1.52  --fof                                   false
% 7.73/1.52  --time_out_real                         305.
% 7.73/1.52  --time_out_virtual                      -1.
% 7.73/1.52  --symbol_type_check                     false
% 7.73/1.52  --clausify_out                          false
% 7.73/1.52  --sig_cnt_out                           false
% 7.73/1.52  --trig_cnt_out                          false
% 7.73/1.52  --trig_cnt_out_tolerance                1.
% 7.73/1.52  --trig_cnt_out_sk_spl                   false
% 7.73/1.52  --abstr_cl_out                          false
% 7.73/1.52  
% 7.73/1.52  ------ Global Options
% 7.73/1.52  
% 7.73/1.52  --schedule                              default
% 7.73/1.52  --add_important_lit                     false
% 7.73/1.52  --prop_solver_per_cl                    1000
% 7.73/1.52  --min_unsat_core                        false
% 7.73/1.52  --soft_assumptions                      false
% 7.73/1.52  --soft_lemma_size                       3
% 7.73/1.52  --prop_impl_unit_size                   0
% 7.73/1.52  --prop_impl_unit                        []
% 7.73/1.52  --share_sel_clauses                     true
% 7.73/1.52  --reset_solvers                         false
% 7.73/1.52  --bc_imp_inh                            [conj_cone]
% 7.73/1.52  --conj_cone_tolerance                   3.
% 7.73/1.52  --extra_neg_conj                        none
% 7.73/1.52  --large_theory_mode                     true
% 7.73/1.52  --prolific_symb_bound                   200
% 7.73/1.52  --lt_threshold                          2000
% 7.73/1.52  --clause_weak_htbl                      true
% 7.73/1.52  --gc_record_bc_elim                     false
% 7.73/1.52  
% 7.73/1.52  ------ Preprocessing Options
% 7.73/1.52  
% 7.73/1.52  --preprocessing_flag                    true
% 7.73/1.52  --time_out_prep_mult                    0.1
% 7.73/1.52  --splitting_mode                        input
% 7.73/1.52  --splitting_grd                         true
% 7.73/1.52  --splitting_cvd                         false
% 7.73/1.52  --splitting_cvd_svl                     false
% 7.73/1.52  --splitting_nvd                         32
% 7.73/1.52  --sub_typing                            true
% 7.73/1.52  --prep_gs_sim                           true
% 7.73/1.52  --prep_unflatten                        true
% 7.73/1.52  --prep_res_sim                          true
% 7.73/1.52  --prep_upred                            true
% 7.73/1.52  --prep_sem_filter                       exhaustive
% 7.73/1.52  --prep_sem_filter_out                   false
% 7.73/1.52  --pred_elim                             true
% 7.73/1.52  --res_sim_input                         true
% 7.73/1.52  --eq_ax_congr_red                       true
% 7.73/1.52  --pure_diseq_elim                       true
% 7.73/1.52  --brand_transform                       false
% 7.73/1.52  --non_eq_to_eq                          false
% 7.73/1.52  --prep_def_merge                        true
% 7.73/1.52  --prep_def_merge_prop_impl              false
% 7.73/1.52  --prep_def_merge_mbd                    true
% 7.73/1.52  --prep_def_merge_tr_red                 false
% 7.73/1.52  --prep_def_merge_tr_cl                  false
% 7.73/1.52  --smt_preprocessing                     true
% 7.73/1.52  --smt_ac_axioms                         fast
% 7.73/1.52  --preprocessed_out                      false
% 7.73/1.52  --preprocessed_stats                    false
% 7.73/1.52  
% 7.73/1.52  ------ Abstraction refinement Options
% 7.73/1.52  
% 7.73/1.52  --abstr_ref                             []
% 7.73/1.52  --abstr_ref_prep                        false
% 7.73/1.52  --abstr_ref_until_sat                   false
% 7.73/1.52  --abstr_ref_sig_restrict                funpre
% 7.73/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.52  --abstr_ref_under                       []
% 7.73/1.52  
% 7.73/1.52  ------ SAT Options
% 7.73/1.52  
% 7.73/1.52  --sat_mode                              false
% 7.73/1.52  --sat_fm_restart_options                ""
% 7.73/1.52  --sat_gr_def                            false
% 7.73/1.52  --sat_epr_types                         true
% 7.73/1.52  --sat_non_cyclic_types                  false
% 7.73/1.52  --sat_finite_models                     false
% 7.73/1.52  --sat_fm_lemmas                         false
% 7.73/1.52  --sat_fm_prep                           false
% 7.73/1.52  --sat_fm_uc_incr                        true
% 7.73/1.52  --sat_out_model                         small
% 7.73/1.52  --sat_out_clauses                       false
% 7.73/1.52  
% 7.73/1.52  ------ QBF Options
% 7.73/1.52  
% 7.73/1.52  --qbf_mode                              false
% 7.73/1.52  --qbf_elim_univ                         false
% 7.73/1.52  --qbf_dom_inst                          none
% 7.73/1.52  --qbf_dom_pre_inst                      false
% 7.73/1.52  --qbf_sk_in                             false
% 7.73/1.52  --qbf_pred_elim                         true
% 7.73/1.52  --qbf_split                             512
% 7.73/1.52  
% 7.73/1.52  ------ BMC1 Options
% 7.73/1.52  
% 7.73/1.52  --bmc1_incremental                      false
% 7.73/1.52  --bmc1_axioms                           reachable_all
% 7.73/1.52  --bmc1_min_bound                        0
% 7.73/1.52  --bmc1_max_bound                        -1
% 7.73/1.52  --bmc1_max_bound_default                -1
% 7.73/1.52  --bmc1_symbol_reachability              true
% 7.73/1.52  --bmc1_property_lemmas                  false
% 7.73/1.52  --bmc1_k_induction                      false
% 7.73/1.52  --bmc1_non_equiv_states                 false
% 7.73/1.52  --bmc1_deadlock                         false
% 7.73/1.52  --bmc1_ucm                              false
% 7.73/1.52  --bmc1_add_unsat_core                   none
% 7.73/1.52  --bmc1_unsat_core_children              false
% 7.73/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.52  --bmc1_out_stat                         full
% 7.73/1.52  --bmc1_ground_init                      false
% 7.73/1.52  --bmc1_pre_inst_next_state              false
% 7.73/1.52  --bmc1_pre_inst_state                   false
% 7.73/1.52  --bmc1_pre_inst_reach_state             false
% 7.73/1.52  --bmc1_out_unsat_core                   false
% 7.73/1.52  --bmc1_aig_witness_out                  false
% 7.73/1.52  --bmc1_verbose                          false
% 7.73/1.52  --bmc1_dump_clauses_tptp                false
% 7.73/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.52  --bmc1_dump_file                        -
% 7.73/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.52  --bmc1_ucm_extend_mode                  1
% 7.73/1.52  --bmc1_ucm_init_mode                    2
% 7.73/1.52  --bmc1_ucm_cone_mode                    none
% 7.73/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.52  --bmc1_ucm_relax_model                  4
% 7.73/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.52  --bmc1_ucm_layered_model                none
% 7.73/1.52  --bmc1_ucm_max_lemma_size               10
% 7.73/1.52  
% 7.73/1.52  ------ AIG Options
% 7.73/1.52  
% 7.73/1.52  --aig_mode                              false
% 7.73/1.52  
% 7.73/1.52  ------ Instantiation Options
% 7.73/1.52  
% 7.73/1.52  --instantiation_flag                    true
% 7.73/1.52  --inst_sos_flag                         true
% 7.73/1.52  --inst_sos_phase                        true
% 7.73/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.52  --inst_lit_sel_side                     none
% 7.73/1.52  --inst_solver_per_active                1400
% 7.73/1.52  --inst_solver_calls_frac                1.
% 7.73/1.52  --inst_passive_queue_type               priority_queues
% 7.73/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.52  --inst_passive_queues_freq              [25;2]
% 7.73/1.52  --inst_dismatching                      true
% 7.73/1.52  --inst_eager_unprocessed_to_passive     true
% 7.73/1.52  --inst_prop_sim_given                   true
% 7.73/1.52  --inst_prop_sim_new                     false
% 7.73/1.52  --inst_subs_new                         false
% 7.73/1.52  --inst_eq_res_simp                      false
% 7.73/1.52  --inst_subs_given                       false
% 7.73/1.52  --inst_orphan_elimination               true
% 7.73/1.52  --inst_learning_loop_flag               true
% 7.73/1.52  --inst_learning_start                   3000
% 7.73/1.52  --inst_learning_factor                  2
% 7.73/1.52  --inst_start_prop_sim_after_learn       3
% 7.73/1.52  --inst_sel_renew                        solver
% 7.73/1.52  --inst_lit_activity_flag                true
% 7.73/1.52  --inst_restr_to_given                   false
% 7.73/1.52  --inst_activity_threshold               500
% 7.73/1.52  --inst_out_proof                        true
% 7.73/1.52  
% 7.73/1.52  ------ Resolution Options
% 7.73/1.52  
% 7.73/1.52  --resolution_flag                       false
% 7.73/1.52  --res_lit_sel                           adaptive
% 7.73/1.52  --res_lit_sel_side                      none
% 7.73/1.52  --res_ordering                          kbo
% 7.73/1.52  --res_to_prop_solver                    active
% 7.73/1.52  --res_prop_simpl_new                    false
% 7.73/1.52  --res_prop_simpl_given                  true
% 7.73/1.52  --res_passive_queue_type                priority_queues
% 7.73/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.52  --res_passive_queues_freq               [15;5]
% 7.73/1.52  --res_forward_subs                      full
% 7.73/1.52  --res_backward_subs                     full
% 7.73/1.52  --res_forward_subs_resolution           true
% 7.73/1.52  --res_backward_subs_resolution          true
% 7.73/1.52  --res_orphan_elimination                true
% 7.73/1.52  --res_time_limit                        2.
% 7.73/1.52  --res_out_proof                         true
% 7.73/1.52  
% 7.73/1.52  ------ Superposition Options
% 7.73/1.52  
% 7.73/1.52  --superposition_flag                    true
% 7.73/1.52  --sup_passive_queue_type                priority_queues
% 7.73/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.52  --demod_completeness_check              fast
% 7.73/1.52  --demod_use_ground                      true
% 7.73/1.52  --sup_to_prop_solver                    passive
% 7.73/1.52  --sup_prop_simpl_new                    true
% 7.73/1.52  --sup_prop_simpl_given                  true
% 7.73/1.52  --sup_fun_splitting                     true
% 7.73/1.52  --sup_smt_interval                      50000
% 7.73/1.52  
% 7.73/1.52  ------ Superposition Simplification Setup
% 7.73/1.52  
% 7.73/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.73/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.73/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.73/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.73/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.73/1.52  --sup_immed_triv                        [TrivRules]
% 7.73/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.52  --sup_immed_bw_main                     []
% 7.73/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.73/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.52  --sup_input_bw                          []
% 7.73/1.52  
% 7.73/1.52  ------ Combination Options
% 7.73/1.52  
% 7.73/1.52  --comb_res_mult                         3
% 7.73/1.52  --comb_sup_mult                         2
% 7.73/1.52  --comb_inst_mult                        10
% 7.73/1.52  
% 7.73/1.52  ------ Debug Options
% 7.73/1.52  
% 7.73/1.52  --dbg_backtrace                         false
% 7.73/1.52  --dbg_dump_prop_clauses                 false
% 7.73/1.52  --dbg_dump_prop_clauses_file            -
% 7.73/1.52  --dbg_out_stat                          false
% 7.73/1.52  
% 7.73/1.52  
% 7.73/1.52  
% 7.73/1.52  
% 7.73/1.52  ------ Proving...
% 7.73/1.52  
% 7.73/1.52  
% 7.73/1.52  % SZS status Theorem for theBenchmark.p
% 7.73/1.52  
% 7.73/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.52  
% 7.73/1.52  fof(f8,axiom,(
% 7.73/1.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f21,plain,(
% 7.73/1.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.73/1.52    inference(ennf_transformation,[],[f8])).
% 7.73/1.52  
% 7.73/1.52  fof(f22,plain,(
% 7.73/1.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.73/1.52    inference(flattening,[],[f21])).
% 7.73/1.52  
% 7.73/1.52  fof(f80,plain,(
% 7.73/1.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f22])).
% 7.73/1.52  
% 7.73/1.52  fof(f9,axiom,(
% 7.73/1.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f23,plain,(
% 7.73/1.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.73/1.52    inference(ennf_transformation,[],[f9])).
% 7.73/1.52  
% 7.73/1.52  fof(f24,plain,(
% 7.73/1.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.73/1.52    inference(flattening,[],[f23])).
% 7.73/1.52  
% 7.73/1.52  fof(f81,plain,(
% 7.73/1.52    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f24])).
% 7.73/1.52  
% 7.73/1.52  fof(f3,axiom,(
% 7.73/1.52    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f44,plain,(
% 7.73/1.52    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 7.73/1.52    inference(nnf_transformation,[],[f3])).
% 7.73/1.52  
% 7.73/1.52  fof(f45,plain,(
% 7.73/1.52    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.73/1.52    inference(rectify,[],[f44])).
% 7.73/1.52  
% 7.73/1.52  fof(f48,plain,(
% 7.73/1.52    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 7.73/1.52    introduced(choice_axiom,[])).
% 7.73/1.52  
% 7.73/1.52  fof(f47,plain,(
% 7.73/1.52    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(X2,sK3(X0,X1))))) )),
% 7.73/1.52    introduced(choice_axiom,[])).
% 7.73/1.52  
% 7.73/1.52  fof(f46,plain,(
% 7.73/1.52    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 7.73/1.52    introduced(choice_axiom,[])).
% 7.73/1.52  
% 7.73/1.52  fof(f49,plain,(
% 7.73/1.52    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.73/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f48,f47,f46])).
% 7.73/1.52  
% 7.73/1.52  fof(f74,plain,(
% 7.73/1.52    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f49])).
% 7.73/1.52  
% 7.73/1.52  fof(f73,plain,(
% 7.73/1.52    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK3(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f49])).
% 7.73/1.52  
% 7.73/1.52  fof(f72,plain,(
% 7.73/1.52    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(sK2(X0,X1),X1)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f49])).
% 7.73/1.52  
% 7.73/1.52  fof(f15,axiom,(
% 7.73/1.52    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f32,plain,(
% 7.73/1.52    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 7.73/1.52    inference(ennf_transformation,[],[f15])).
% 7.73/1.52  
% 7.73/1.52  fof(f33,plain,(
% 7.73/1.52    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 7.73/1.52    inference(flattening,[],[f32])).
% 7.73/1.52  
% 7.73/1.52  fof(f98,plain,(
% 7.73/1.52    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f33])).
% 7.73/1.52  
% 7.73/1.52  fof(f1,axiom,(
% 7.73/1.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f38,plain,(
% 7.73/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.52    inference(nnf_transformation,[],[f1])).
% 7.73/1.52  
% 7.73/1.52  fof(f39,plain,(
% 7.73/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.52    inference(rectify,[],[f38])).
% 7.73/1.52  
% 7.73/1.52  fof(f40,plain,(
% 7.73/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.73/1.52    introduced(choice_axiom,[])).
% 7.73/1.52  
% 7.73/1.52  fof(f41,plain,(
% 7.73/1.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 7.73/1.52  
% 7.73/1.52  fof(f64,plain,(
% 7.73/1.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f41])).
% 7.73/1.52  
% 7.73/1.52  fof(f2,axiom,(
% 7.73/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f42,plain,(
% 7.73/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.52    inference(nnf_transformation,[],[f2])).
% 7.73/1.52  
% 7.73/1.52  fof(f43,plain,(
% 7.73/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.52    inference(flattening,[],[f42])).
% 7.73/1.52  
% 7.73/1.52  fof(f68,plain,(
% 7.73/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f43])).
% 7.73/1.52  
% 7.73/1.52  fof(f66,plain,(
% 7.73/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.73/1.52    inference(cnf_transformation,[],[f43])).
% 7.73/1.52  
% 7.73/1.52  fof(f104,plain,(
% 7.73/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.73/1.52    inference(equality_resolution,[],[f66])).
% 7.73/1.52  
% 7.73/1.52  fof(f11,axiom,(
% 7.73/1.52    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f18,plain,(
% 7.73/1.52    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.73/1.52    inference(rectify,[],[f11])).
% 7.73/1.52  
% 7.73/1.52  fof(f26,plain,(
% 7.73/1.52    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.73/1.52    inference(ennf_transformation,[],[f18])).
% 7.73/1.52  
% 7.73/1.52  fof(f27,plain,(
% 7.73/1.52    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.73/1.52    inference(flattening,[],[f26])).
% 7.73/1.52  
% 7.73/1.52  fof(f36,plain,(
% 7.73/1.52    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.73/1.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.73/1.52  
% 7.73/1.52  fof(f37,plain,(
% 7.73/1.52    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.73/1.52    inference(definition_folding,[],[f27,f36])).
% 7.73/1.52  
% 7.73/1.52  fof(f57,plain,(
% 7.73/1.52    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.73/1.52    inference(nnf_transformation,[],[f37])).
% 7.73/1.52  
% 7.73/1.52  fof(f58,plain,(
% 7.73/1.52    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.73/1.52    inference(flattening,[],[f57])).
% 7.73/1.52  
% 7.73/1.52  fof(f59,plain,(
% 7.73/1.52    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.73/1.52    inference(rectify,[],[f58])).
% 7.73/1.52  
% 7.73/1.52  fof(f60,plain,(
% 7.73/1.52    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0)) & r1_tarski(sK8(X0),u1_pre_topc(X0)) & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.73/1.52    introduced(choice_axiom,[])).
% 7.73/1.52  
% 7.73/1.52  fof(f61,plain,(
% 7.73/1.52    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0)) & r1_tarski(sK8(X0),u1_pre_topc(X0)) & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.73/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f59,f60])).
% 7.73/1.52  
% 7.73/1.52  fof(f89,plain,(
% 7.73/1.52    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f61])).
% 7.73/1.52  
% 7.73/1.52  fof(f12,axiom,(
% 7.73/1.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f28,plain,(
% 7.73/1.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.73/1.52    inference(ennf_transformation,[],[f12])).
% 7.73/1.52  
% 7.73/1.52  fof(f95,plain,(
% 7.73/1.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f28])).
% 7.73/1.52  
% 7.73/1.52  fof(f13,axiom,(
% 7.73/1.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f29,plain,(
% 7.73/1.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.73/1.52    inference(ennf_transformation,[],[f13])).
% 7.73/1.52  
% 7.73/1.52  fof(f96,plain,(
% 7.73/1.52    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f29])).
% 7.73/1.52  
% 7.73/1.52  fof(f14,axiom,(
% 7.73/1.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f30,plain,(
% 7.73/1.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.73/1.52    inference(ennf_transformation,[],[f14])).
% 7.73/1.52  
% 7.73/1.52  fof(f31,plain,(
% 7.73/1.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.73/1.52    inference(flattening,[],[f30])).
% 7.73/1.52  
% 7.73/1.52  fof(f97,plain,(
% 7.73/1.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.73/1.52    inference(cnf_transformation,[],[f31])).
% 7.73/1.52  
% 7.73/1.52  fof(f16,conjecture,(
% 7.73/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 7.73/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.52  
% 7.73/1.52  fof(f17,negated_conjecture,(
% 7.73/1.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 7.73/1.52    inference(negated_conjecture,[],[f16])).
% 7.73/1.52  
% 7.73/1.52  fof(f34,plain,(
% 7.73/1.52    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.73/1.52    inference(ennf_transformation,[],[f17])).
% 7.73/1.52  
% 7.73/1.52  fof(f35,plain,(
% 7.73/1.52    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.73/1.52    inference(flattening,[],[f34])).
% 7.73/1.52  
% 7.73/1.52  fof(f62,plain,(
% 7.73/1.52    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) & l1_pre_topc(sK9) & v2_pre_topc(sK9) & ~v2_struct_0(sK9))),
% 7.73/1.52    introduced(choice_axiom,[])).
% 7.73/1.52  
% 7.73/1.52  fof(f63,plain,(
% 7.73/1.52    u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) & l1_pre_topc(sK9) & v2_pre_topc(sK9) & ~v2_struct_0(sK9)),
% 7.73/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f35,f62])).
% 7.73/1.52  
% 7.73/1.52  fof(f102,plain,(
% 7.73/1.52    u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))),
% 7.73/1.52    inference(cnf_transformation,[],[f63])).
% 7.73/1.52  
% 7.73/1.52  fof(f101,plain,(
% 7.73/1.52    l1_pre_topc(sK9)),
% 7.73/1.52    inference(cnf_transformation,[],[f63])).
% 7.73/1.52  
% 7.73/1.52  fof(f100,plain,(
% 7.73/1.52    v2_pre_topc(sK9)),
% 7.73/1.52    inference(cnf_transformation,[],[f63])).
% 7.73/1.52  
% 7.73/1.52  fof(f99,plain,(
% 7.73/1.52    ~v2_struct_0(sK9)),
% 7.73/1.52    inference(cnf_transformation,[],[f63])).
% 7.73/1.52  
% 7.73/1.52  cnf(c_16,plain,
% 7.73/1.52      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.73/1.52      inference(cnf_transformation,[],[f80]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1972,plain,
% 7.73/1.52      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.73/1.52      | r2_hidden(X0,u1_struct_0(X1))
% 7.73/1.52      | v1_xboole_0(u1_struct_0(X1)) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_16]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_24020,plain,
% 7.73/1.52      ( ~ m1_subset_1(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(X0))
% 7.73/1.52      | r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(X0))
% 7.73/1.52      | v1_xboole_0(u1_struct_0(X0)) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1972]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_24022,plain,
% 7.73/1.52      ( ~ m1_subset_1(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
% 7.73/1.52      | r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
% 7.73/1.52      | v1_xboole_0(u1_struct_0(sK9)) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_24020]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_17,plain,
% 7.73/1.52      ( m1_subset_1(X0,X1)
% 7.73/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.73/1.52      | ~ r2_hidden(X0,X2) ),
% 7.73/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_2135,plain,
% 7.73/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
% 7.73/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
% 7.73/1.52      | ~ r2_hidden(X0,X1) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_17]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_2666,plain,
% 7.73/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
% 7.73/1.52      | ~ m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
% 7.73/1.52      | ~ r2_hidden(X0,u1_pre_topc(sK9)) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_2135]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_10153,plain,
% 7.73/1.52      ( m1_subset_1(sK3(u1_pre_topc(sK9),u1_struct_0(sK9)),k1_zfmisc_1(u1_struct_0(sK9)))
% 7.73/1.52      | ~ m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
% 7.73/1.52      | ~ r2_hidden(sK3(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_pre_topc(sK9)) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_2666]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_2776,plain,
% 7.73/1.52      ( m1_subset_1(X0,u1_struct_0(X1))
% 7.73/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.73/1.52      | ~ r2_hidden(X0,X2) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_17]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_10095,plain,
% 7.73/1.52      ( ~ m1_subset_1(sK3(u1_pre_topc(sK9),u1_struct_0(sK9)),k1_zfmisc_1(u1_struct_0(X0)))
% 7.73/1.52      | m1_subset_1(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(X0))
% 7.73/1.52      | ~ r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),sK3(u1_pre_topc(sK9),u1_struct_0(sK9))) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_2776]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_10097,plain,
% 7.73/1.52      ( ~ m1_subset_1(sK3(u1_pre_topc(sK9),u1_struct_0(sK9)),k1_zfmisc_1(u1_struct_0(sK9)))
% 7.73/1.52      | m1_subset_1(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
% 7.73/1.52      | ~ r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),sK3(u1_pre_topc(sK9),u1_struct_0(sK9))) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_10095]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_5,plain,
% 7.73/1.52      ( ~ r2_hidden(X0,X1)
% 7.73/1.52      | ~ r2_hidden(sK2(X1,X2),X0)
% 7.73/1.52      | ~ r2_hidden(sK2(X1,X2),X2)
% 7.73/1.52      | k3_tarski(X1) = X2 ),
% 7.73/1.52      inference(cnf_transformation,[],[f74]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_2701,plain,
% 7.73/1.52      ( ~ r2_hidden(X0,X1)
% 7.73/1.52      | ~ r2_hidden(sK2(X1,u1_struct_0(X2)),X0)
% 7.73/1.52      | ~ r2_hidden(sK2(X1,u1_struct_0(X2)),u1_struct_0(X2))
% 7.73/1.52      | k3_tarski(X1) = u1_struct_0(X2) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_5]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_7209,plain,
% 7.73/1.52      ( ~ r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(X0)),u1_struct_0(X0))
% 7.73/1.52      | ~ r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(X0)),u1_struct_0(sK9))
% 7.73/1.52      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 7.73/1.52      | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(X0) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_2701]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_7211,plain,
% 7.73/1.52      ( ~ r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
% 7.73/1.52      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 7.73/1.52      | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_7209]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1205,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1802,plain,
% 7.73/1.52      ( X0 != X1 | u1_struct_0(sK9) != X1 | u1_struct_0(sK9) = X0 ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1205]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1934,plain,
% 7.73/1.52      ( X0 != u1_struct_0(sK9)
% 7.73/1.52      | u1_struct_0(sK9) = X0
% 7.73/1.52      | u1_struct_0(sK9) != u1_struct_0(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1802]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_2087,plain,
% 7.73/1.52      ( u1_struct_0(sK9) != u1_struct_0(sK9)
% 7.73/1.52      | u1_struct_0(sK9) = k3_tarski(X0)
% 7.73/1.52      | k3_tarski(X0) != u1_struct_0(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1934]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_5682,plain,
% 7.73/1.52      ( u1_struct_0(sK9) != u1_struct_0(sK9)
% 7.73/1.52      | u1_struct_0(sK9) = k3_tarski(u1_pre_topc(sK9))
% 7.73/1.52      | k3_tarski(u1_pre_topc(sK9)) != u1_struct_0(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_2087]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1892,plain,
% 7.73/1.52      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != X0
% 7.73/1.52      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = u1_struct_0(X1)
% 7.73/1.52      | u1_struct_0(X1) != X0 ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1205]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_5343,plain,
% 7.73/1.52      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = u1_struct_0(X0)
% 7.73/1.52      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != k3_tarski(u1_pre_topc(sK9))
% 7.73/1.52      | u1_struct_0(X0) != k3_tarski(u1_pre_topc(sK9)) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1892]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_5344,plain,
% 7.73/1.52      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = u1_struct_0(sK9)
% 7.73/1.52      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != k3_tarski(u1_pre_topc(sK9))
% 7.73/1.52      | u1_struct_0(sK9) != k3_tarski(u1_pre_topc(sK9)) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_5343]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_6,plain,
% 7.73/1.52      ( r2_hidden(sK3(X0,X1),X0)
% 7.73/1.52      | r2_hidden(sK2(X0,X1),X1)
% 7.73/1.52      | k3_tarski(X0) = X1 ),
% 7.73/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_2501,plain,
% 7.73/1.52      ( r2_hidden(sK3(X0,u1_struct_0(sK9)),X0)
% 7.73/1.52      | r2_hidden(sK2(X0,u1_struct_0(sK9)),u1_struct_0(sK9))
% 7.73/1.52      | k3_tarski(X0) = u1_struct_0(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_3918,plain,
% 7.73/1.52      ( r2_hidden(sK3(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_pre_topc(sK9))
% 7.73/1.52      | r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
% 7.73/1.52      | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_2501]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_7,plain,
% 7.73/1.52      ( r2_hidden(sK2(X0,X1),X1)
% 7.73/1.52      | r2_hidden(sK2(X0,X1),sK3(X0,X1))
% 7.73/1.52      | k3_tarski(X0) = X1 ),
% 7.73/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_2500,plain,
% 7.73/1.52      ( r2_hidden(sK2(X0,u1_struct_0(sK9)),sK3(X0,u1_struct_0(sK9)))
% 7.73/1.52      | r2_hidden(sK2(X0,u1_struct_0(sK9)),u1_struct_0(sK9))
% 7.73/1.52      | k3_tarski(X0) = u1_struct_0(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_7]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_3909,plain,
% 7.73/1.52      ( r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),sK3(u1_pre_topc(sK9),u1_struct_0(sK9)))
% 7.73/1.52      | r2_hidden(sK2(u1_pre_topc(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
% 7.73/1.52      | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_2500]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1207,plain,
% 7.73/1.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.73/1.52      theory(equality) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1954,plain,
% 7.73/1.52      ( ~ r2_hidden(X0,X1)
% 7.73/1.52      | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
% 7.73/1.52      | u1_pre_topc(sK9) != X1
% 7.73/1.52      | k3_tarski(u1_pre_topc(sK9)) != X0 ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1207]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_2282,plain,
% 7.73/1.52      ( ~ r2_hidden(X0,u1_pre_topc(sK9))
% 7.73/1.52      | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
% 7.73/1.52      | u1_pre_topc(sK9) != u1_pre_topc(sK9)
% 7.73/1.52      | k3_tarski(u1_pre_topc(sK9)) != X0 ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1954]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_2898,plain,
% 7.73/1.52      ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 7.73/1.52      | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
% 7.73/1.52      | u1_pre_topc(sK9) != u1_pre_topc(sK9)
% 7.73/1.52      | k3_tarski(u1_pre_topc(sK9)) != u1_struct_0(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_2282]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_34,plain,
% 7.73/1.52      ( ~ r2_hidden(k3_tarski(X0),X0)
% 7.73/1.52      | v1_xboole_0(X0)
% 7.73/1.52      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 7.73/1.52      inference(cnf_transformation,[],[f98]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1838,plain,
% 7.73/1.52      ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
% 7.73/1.52      | v1_xboole_0(u1_pre_topc(sK9))
% 7.73/1.52      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = k3_tarski(u1_pre_topc(sK9)) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_34]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1765,plain,
% 7.73/1.52      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != X0
% 7.73/1.52      | u1_struct_0(sK9) != X0
% 7.73/1.52      | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1205]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1808,plain,
% 7.73/1.52      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != u1_struct_0(sK9)
% 7.73/1.52      | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
% 7.73/1.52      | u1_struct_0(sK9) != u1_struct_0(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1765]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1,plain,
% 7.73/1.52      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.73/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1787,plain,
% 7.73/1.52      ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 7.73/1.52      | ~ v1_xboole_0(u1_pre_topc(sK9)) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1215,plain,
% 7.73/1.52      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 7.73/1.52      theory(equality) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1228,plain,
% 7.73/1.52      ( u1_pre_topc(sK9) = u1_pre_topc(sK9) | sK9 != sK9 ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1215]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1213,plain,
% 7.73/1.52      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 7.73/1.52      theory(equality) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_1226,plain,
% 7.73/1.52      ( u1_struct_0(sK9) = u1_struct_0(sK9) | sK9 != sK9 ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_1213]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_2,plain,
% 7.73/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.73/1.52      inference(cnf_transformation,[],[f68]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_129,plain,
% 7.73/1.52      ( ~ r1_tarski(sK9,sK9) | sK9 = sK9 ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_4,plain,
% 7.73/1.52      ( r1_tarski(X0,X0) ),
% 7.73/1.52      inference(cnf_transformation,[],[f104]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_125,plain,
% 7.73/1.52      ( r1_tarski(sK9,sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_4]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_30,plain,
% 7.73/1.52      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 7.73/1.52      | ~ l1_pre_topc(X0)
% 7.73/1.52      | ~ v2_pre_topc(X0) ),
% 7.73/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_55,plain,
% 7.73/1.52      ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 7.73/1.52      | ~ l1_pre_topc(sK9)
% 7.73/1.52      | ~ v2_pre_topc(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_30]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_31,plain,
% 7.73/1.52      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.73/1.52      inference(cnf_transformation,[],[f95]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_52,plain,
% 7.73/1.52      ( l1_struct_0(sK9) | ~ l1_pre_topc(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_31]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_32,plain,
% 7.73/1.52      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.73/1.52      | ~ l1_pre_topc(X0) ),
% 7.73/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_49,plain,
% 7.73/1.52      ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
% 7.73/1.52      | ~ l1_pre_topc(sK9) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_32]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_33,plain,
% 7.73/1.52      ( v2_struct_0(X0)
% 7.73/1.52      | ~ l1_struct_0(X0)
% 7.73/1.52      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 7.73/1.52      inference(cnf_transformation,[],[f97]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_46,plain,
% 7.73/1.52      ( v2_struct_0(sK9)
% 7.73/1.52      | ~ l1_struct_0(sK9)
% 7.73/1.52      | ~ v1_xboole_0(u1_struct_0(sK9)) ),
% 7.73/1.52      inference(instantiation,[status(thm)],[c_33]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_35,negated_conjecture,
% 7.73/1.52      ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
% 7.73/1.52      inference(cnf_transformation,[],[f102]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_36,negated_conjecture,
% 7.73/1.52      ( l1_pre_topc(sK9) ),
% 7.73/1.52      inference(cnf_transformation,[],[f101]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_37,negated_conjecture,
% 7.73/1.52      ( v2_pre_topc(sK9) ),
% 7.73/1.52      inference(cnf_transformation,[],[f100]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(c_38,negated_conjecture,
% 7.73/1.52      ( ~ v2_struct_0(sK9) ),
% 7.73/1.52      inference(cnf_transformation,[],[f99]) ).
% 7.73/1.52  
% 7.73/1.52  cnf(contradiction,plain,
% 7.73/1.52      ( $false ),
% 7.73/1.52      inference(minisat,
% 7.73/1.52                [status(thm)],
% 7.73/1.52                [c_24022,c_10153,c_10097,c_7211,c_5682,c_5344,c_3918,
% 7.73/1.52                 c_3909,c_2898,c_1838,c_1808,c_1787,c_1228,c_1226,c_129,
% 7.73/1.52                 c_125,c_55,c_52,c_49,c_46,c_35,c_36,c_37,c_38]) ).
% 7.73/1.52  
% 7.73/1.52  
% 7.73/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.52  
% 7.73/1.52  ------                               Statistics
% 7.73/1.52  
% 7.73/1.52  ------ General
% 7.73/1.52  
% 7.73/1.52  abstr_ref_over_cycles:                  0
% 7.73/1.52  abstr_ref_under_cycles:                 0
% 7.73/1.52  gc_basic_clause_elim:                   0
% 7.73/1.52  forced_gc_time:                         0
% 7.73/1.52  parsing_time:                           0.018
% 7.73/1.52  unif_index_cands_time:                  0.
% 7.73/1.52  unif_index_add_time:                    0.
% 7.73/1.52  orderings_time:                         0.
% 7.73/1.52  out_proof_time:                         0.01
% 7.73/1.52  total_time:                             0.774
% 7.73/1.52  num_of_symbols:                         58
% 7.73/1.52  num_of_terms:                           22164
% 7.73/1.52  
% 7.73/1.52  ------ Preprocessing
% 7.73/1.52  
% 7.73/1.52  num_of_splits:                          0
% 7.73/1.52  num_of_split_atoms:                     0
% 7.73/1.52  num_of_reused_defs:                     0
% 7.73/1.52  num_eq_ax_congr_red:                    38
% 7.73/1.52  num_of_sem_filtered_clauses:            1
% 7.73/1.52  num_of_subtypes:                        0
% 7.73/1.52  monotx_restored_types:                  0
% 7.73/1.52  sat_num_of_epr_types:                   0
% 7.73/1.52  sat_num_of_non_cyclic_types:            0
% 7.73/1.52  sat_guarded_non_collapsed_types:        0
% 7.73/1.52  num_pure_diseq_elim:                    0
% 7.73/1.52  simp_replaced_by:                       0
% 7.73/1.52  res_preprocessed:                       162
% 7.73/1.52  prep_upred:                             0
% 7.73/1.52  prep_unflattend:                        30
% 7.73/1.52  smt_new_axioms:                         0
% 7.73/1.52  pred_elim_cands:                        5
% 7.73/1.52  pred_elim:                              4
% 7.73/1.52  pred_elim_cl:                           7
% 7.73/1.52  pred_elim_cycles:                       8
% 7.73/1.52  merged_defs:                            0
% 7.73/1.52  merged_defs_ncl:                        0
% 7.73/1.52  bin_hyper_res:                          0
% 7.73/1.52  prep_cycles:                            4
% 7.73/1.52  pred_elim_time:                         0.011
% 7.73/1.52  splitting_time:                         0.
% 7.73/1.52  sem_filter_time:                        0.
% 7.73/1.52  monotx_time:                            0.
% 7.73/1.52  subtype_inf_time:                       0.
% 7.73/1.52  
% 7.73/1.52  ------ Problem properties
% 7.73/1.52  
% 7.73/1.52  clauses:                                31
% 7.73/1.52  conjectures:                            1
% 7.73/1.52  epr:                                    6
% 7.73/1.52  horn:                                   21
% 7.73/1.52  ground:                                 5
% 7.73/1.52  unary:                                  8
% 7.73/1.52  binary:                                 13
% 7.73/1.52  lits:                                   68
% 7.73/1.52  lits_eq:                                7
% 7.73/1.52  fd_pure:                                0
% 7.73/1.52  fd_pseudo:                              0
% 7.73/1.52  fd_cond:                                0
% 7.73/1.52  fd_pseudo_cond:                         4
% 7.73/1.52  ac_symbols:                             0
% 7.73/1.52  
% 7.73/1.52  ------ Propositional Solver
% 7.73/1.52  
% 7.73/1.52  prop_solver_calls:                      30
% 7.73/1.52  prop_fast_solver_calls:                 1562
% 7.73/1.52  smt_solver_calls:                       0
% 7.73/1.52  smt_fast_solver_calls:                  0
% 7.73/1.52  prop_num_of_clauses:                    10610
% 7.73/1.52  prop_preprocess_simplified:             23679
% 7.73/1.52  prop_fo_subsumed:                       27
% 7.73/1.52  prop_solver_time:                       0.
% 7.73/1.52  smt_solver_time:                        0.
% 7.73/1.52  smt_fast_solver_time:                   0.
% 7.73/1.52  prop_fast_solver_time:                  0.
% 7.73/1.52  prop_unsat_core_time:                   0.001
% 7.73/1.52  
% 7.73/1.52  ------ QBF
% 7.73/1.52  
% 7.73/1.52  qbf_q_res:                              0
% 7.73/1.52  qbf_num_tautologies:                    0
% 7.73/1.52  qbf_prep_cycles:                        0
% 7.73/1.52  
% 7.73/1.52  ------ BMC1
% 7.73/1.52  
% 7.73/1.52  bmc1_current_bound:                     -1
% 7.73/1.52  bmc1_last_solved_bound:                 -1
% 7.73/1.52  bmc1_unsat_core_size:                   -1
% 7.73/1.52  bmc1_unsat_core_parents_size:           -1
% 7.73/1.52  bmc1_merge_next_fun:                    0
% 7.73/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.73/1.52  
% 7.73/1.52  ------ Instantiation
% 7.73/1.52  
% 7.73/1.52  inst_num_of_clauses:                    2670
% 7.73/1.52  inst_num_in_passive:                    1303
% 7.73/1.52  inst_num_in_active:                     936
% 7.73/1.52  inst_num_in_unprocessed:                430
% 7.73/1.52  inst_num_of_loops:                      1260
% 7.73/1.52  inst_num_of_learning_restarts:          0
% 7.73/1.52  inst_num_moves_active_passive:          323
% 7.73/1.52  inst_lit_activity:                      0
% 7.73/1.52  inst_lit_activity_moves:                0
% 7.73/1.52  inst_num_tautologies:                   0
% 7.73/1.52  inst_num_prop_implied:                  0
% 7.73/1.52  inst_num_existing_simplified:           0
% 7.73/1.52  inst_num_eq_res_simplified:             0
% 7.73/1.52  inst_num_child_elim:                    0
% 7.73/1.52  inst_num_of_dismatching_blockings:      1748
% 7.73/1.52  inst_num_of_non_proper_insts:           3373
% 7.73/1.52  inst_num_of_duplicates:                 0
% 7.73/1.52  inst_inst_num_from_inst_to_res:         0
% 7.73/1.52  inst_dismatching_checking_time:         0.
% 7.73/1.52  
% 7.73/1.52  ------ Resolution
% 7.73/1.52  
% 7.73/1.52  res_num_of_clauses:                     0
% 7.73/1.52  res_num_in_passive:                     0
% 7.73/1.52  res_num_in_active:                      0
% 7.73/1.52  res_num_of_loops:                       166
% 7.73/1.52  res_forward_subset_subsumed:            263
% 7.73/1.52  res_backward_subset_subsumed:           0
% 7.73/1.52  res_forward_subsumed:                   0
% 7.73/1.52  res_backward_subsumed:                  0
% 7.73/1.52  res_forward_subsumption_resolution:     0
% 7.73/1.52  res_backward_subsumption_resolution:    0
% 7.73/1.52  res_clause_to_clause_subsumption:       4880
% 7.73/1.52  res_orphan_elimination:                 0
% 7.73/1.52  res_tautology_del:                      286
% 7.73/1.52  res_num_eq_res_simplified:              0
% 7.73/1.52  res_num_sel_changes:                    0
% 7.73/1.52  res_moves_from_active_to_pass:          0
% 7.73/1.52  
% 7.73/1.52  ------ Superposition
% 7.73/1.52  
% 7.73/1.52  sup_time_total:                         0.
% 7.73/1.52  sup_time_generating:                    0.
% 7.73/1.52  sup_time_sim_full:                      0.
% 7.73/1.52  sup_time_sim_immed:                     0.
% 7.73/1.52  
% 7.73/1.52  sup_num_of_clauses:                     1153
% 7.73/1.52  sup_num_in_active:                      238
% 7.73/1.52  sup_num_in_passive:                     915
% 7.73/1.52  sup_num_of_loops:                       250
% 7.73/1.52  sup_fw_superposition:                   610
% 7.73/1.52  sup_bw_superposition:                   758
% 7.73/1.52  sup_immediate_simplified:               127
% 7.73/1.52  sup_given_eliminated:                   1
% 7.73/1.52  comparisons_done:                       0
% 7.73/1.52  comparisons_avoided:                    0
% 7.73/1.52  
% 7.73/1.52  ------ Simplifications
% 7.73/1.52  
% 7.73/1.52  
% 7.73/1.52  sim_fw_subset_subsumed:                 69
% 7.73/1.52  sim_bw_subset_subsumed:                 10
% 7.73/1.52  sim_fw_subsumed:                        27
% 7.73/1.52  sim_bw_subsumed:                        11
% 7.73/1.52  sim_fw_subsumption_res:                 0
% 7.73/1.52  sim_bw_subsumption_res:                 0
% 7.73/1.52  sim_tautology_del:                      9
% 7.73/1.52  sim_eq_tautology_del:                   10
% 7.73/1.52  sim_eq_res_simp:                        0
% 7.73/1.52  sim_fw_demodulated:                     25
% 7.73/1.52  sim_bw_demodulated:                     0
% 7.73/1.52  sim_light_normalised:                   6
% 7.73/1.52  sim_joinable_taut:                      0
% 7.73/1.52  sim_joinable_simp:                      0
% 7.73/1.52  sim_ac_normalised:                      0
% 7.73/1.52  sim_smt_subsumption:                    0
% 7.73/1.52  
%------------------------------------------------------------------------------
