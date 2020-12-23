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
% DateTime   : Thu Dec  3 12:20:29 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 500 expanded)
%              Number of clauses        :   80 ( 164 expanded)
%              Number of leaves         :   19 (  92 expanded)
%              Depth                    :   25
%              Number of atoms          :  534 (1953 expanded)
%              Number of equality atoms :  113 ( 329 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f39,f38,f37])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f63])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8)))
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8)))
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f26,f53])).

fof(f91,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f54])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f27])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
        & r1_tarski(sK7(X0),u1_pre_topc(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
            & r1_tarski(sK7(X0),u1_pre_topc(X0))
            & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f50,f51])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f89,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2346,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK8),X0),X0)
    | r1_tarski(u1_struct_0(sK8),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_11686,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK8),k3_tarski(X0)),k3_tarski(X0))
    | r1_tarski(u1_struct_0(sK8),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_30647,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))),k3_tarski(u1_pre_topc(sK8)))
    | r1_tarski(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))) ),
    inference(instantiation,[status(thm)],[c_11686])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3964,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK8))
    | r2_hidden(X0,k3_tarski(u1_pre_topc(sK8)))
    | ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_13567,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))),u1_struct_0(sK8))
    | r2_hidden(sK1(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))),k3_tarski(u1_pre_topc(sK8)))
    | ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(instantiation,[status(thm)],[c_3964])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_18,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_286,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_285])).

cnf(c_355,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_20,c_286])).

cnf(c_1887,plain,
    ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | ~ r1_tarski(u1_pre_topc(sK8),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_7662,plain,
    ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | ~ r1_tarski(u1_pre_topc(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_1887])).

cnf(c_33,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_479,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_36])).

cnf(c_480,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_1821,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1833,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3634,plain,
    ( r2_hidden(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_1833])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_38,plain,
    ( v2_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_39,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_43,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_45,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_32,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_46,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_48,plain,
    ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) = iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1947,plain,
    ( r1_tarski(u1_pre_topc(sK8),u1_pre_topc(sK8)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1948,plain,
    ( r1_tarski(u1_pre_topc(sK8),u1_pre_topc(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1947])).

cnf(c_2195,plain,
    ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | ~ r1_tarski(u1_pre_topc(sK8),u1_pre_topc(sK8))
    | ~ v1_xboole_0(u1_pre_topc(sK8)) ),
    inference(instantiation,[status(thm)],[c_1887])).

cnf(c_2196,plain,
    ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) != iProver_top
    | r1_tarski(u1_pre_topc(sK8),u1_pre_topc(sK8)) != iProver_top
    | v1_xboole_0(u1_pre_topc(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2195])).

cnf(c_2267,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | r2_hidden(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2268,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
    | r2_hidden(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2267])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1835,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3152,plain,
    ( v1_xboole_0(u1_pre_topc(sK8)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_1835])).

cnf(c_4101,plain,
    ( r2_hidden(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3634,c_38,c_39,c_45,c_48,c_1948,c_2196,c_2268,c_3152])).

cnf(c_12,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1832,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2756,plain,
    ( k5_setfam_1(u1_struct_0(sK8),u1_pre_topc(sK8)) = k3_tarski(u1_pre_topc(sK8)) ),
    inference(superposition,[status(thm)],[c_1821,c_1832])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_36])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK8),X0),u1_pre_topc(sK8))
    | ~ r1_tarski(X0,u1_pre_topc(sK8))
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_519,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(sK8))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK8),X0),u1_pre_topc(sK8))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_37])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK8),X0),u1_pre_topc(sK8))
    | ~ r1_tarski(X0,u1_pre_topc(sK8)) ),
    inference(renaming,[status(thm)],[c_519])).

cnf(c_1818,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK8),X0),u1_pre_topc(sK8)) = iProver_top
    | r1_tarski(X0,u1_pre_topc(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_2760,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
    | r2_hidden(k3_tarski(u1_pre_topc(sK8)),u1_pre_topc(sK8)) = iProver_top
    | r1_tarski(u1_pre_topc(sK8),u1_pre_topc(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_1818])).

cnf(c_2784,plain,
    ( r2_hidden(k3_tarski(u1_pre_topc(sK8)),u1_pre_topc(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2760,c_39,c_45,c_1948])).

cnf(c_1839,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,k3_tarski(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3749,plain,
    ( r2_hidden(u1_pre_topc(sK8),X0) != iProver_top
    | r2_hidden(k3_tarski(u1_pre_topc(sK8)),k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2784,c_1839])).

cnf(c_4681,plain,
    ( r2_hidden(u1_pre_topc(sK8),k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(k3_tarski(u1_pre_topc(sK8)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_3749])).

cnf(c_5164,plain,
    ( r2_hidden(k3_tarski(u1_pre_topc(sK8)),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_4681])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1834,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5290,plain,
    ( m1_subset_1(k3_tarski(u1_pre_topc(sK8)),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5164,c_1834])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1830,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6682,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK8)),u1_struct_0(sK8)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5290,c_1830])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1844,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6685,plain,
    ( k3_tarski(u1_pre_topc(sK8)) = u1_struct_0(sK8)
    | r1_tarski(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6682,c_1844])).

cnf(c_6686,plain,
    ( ~ r1_tarski(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8)))
    | k3_tarski(u1_pre_topc(sK8)) = u1_struct_0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6685])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2347,plain,
    ( r2_hidden(sK1(u1_struct_0(sK8),X0),u1_struct_0(sK8))
    | r1_tarski(u1_struct_0(sK8),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6246,plain,
    ( r2_hidden(sK1(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))),u1_struct_0(sK8))
    | r1_tarski(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))) ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_34,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1823,plain,
    ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
    | r2_hidden(k3_tarski(X0),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2788,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) = k3_tarski(u1_pre_topc(sK8))
    | v1_xboole_0(u1_pre_topc(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2784,c_1823])).

cnf(c_2791,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) = k3_tarski(u1_pre_topc(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2788,c_38,c_39,c_48,c_1948,c_2196])).

cnf(c_35,negated_conjecture,
    ( u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2793,plain,
    ( k3_tarski(u1_pre_topc(sK8)) != u1_struct_0(sK8) ),
    inference(demodulation,[status(thm)],[c_2791,c_35])).

cnf(c_2209,plain,
    ( r1_tarski(u1_pre_topc(sK8),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_1830])).

cnf(c_2210,plain,
    ( r1_tarski(u1_pre_topc(sK8),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2209])).

cnf(c_47,plain,
    ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30647,c_13567,c_7662,c_6686,c_6246,c_2793,c_2210,c_47,c_36,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:45:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.83/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.83/1.50  
% 7.83/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.83/1.50  
% 7.83/1.50  ------  iProver source info
% 7.83/1.50  
% 7.83/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.83/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.83/1.50  git: non_committed_changes: false
% 7.83/1.50  git: last_make_outside_of_git: false
% 7.83/1.50  
% 7.83/1.50  ------ 
% 7.83/1.50  
% 7.83/1.50  ------ Input Options
% 7.83/1.50  
% 7.83/1.50  --out_options                           all
% 7.83/1.50  --tptp_safe_out                         true
% 7.83/1.50  --problem_path                          ""
% 7.83/1.50  --include_path                          ""
% 7.83/1.50  --clausifier                            res/vclausify_rel
% 7.83/1.50  --clausifier_options                    ""
% 7.83/1.50  --stdin                                 false
% 7.83/1.50  --stats_out                             all
% 7.83/1.50  
% 7.83/1.50  ------ General Options
% 7.83/1.50  
% 7.83/1.50  --fof                                   false
% 7.83/1.50  --time_out_real                         305.
% 7.83/1.50  --time_out_virtual                      -1.
% 7.83/1.50  --symbol_type_check                     false
% 7.83/1.50  --clausify_out                          false
% 7.83/1.50  --sig_cnt_out                           false
% 7.83/1.50  --trig_cnt_out                          false
% 7.83/1.50  --trig_cnt_out_tolerance                1.
% 7.83/1.50  --trig_cnt_out_sk_spl                   false
% 7.83/1.50  --abstr_cl_out                          false
% 7.83/1.50  
% 7.83/1.50  ------ Global Options
% 7.83/1.50  
% 7.83/1.50  --schedule                              default
% 7.83/1.50  --add_important_lit                     false
% 7.83/1.50  --prop_solver_per_cl                    1000
% 7.83/1.50  --min_unsat_core                        false
% 7.83/1.50  --soft_assumptions                      false
% 7.83/1.50  --soft_lemma_size                       3
% 7.83/1.50  --prop_impl_unit_size                   0
% 7.83/1.50  --prop_impl_unit                        []
% 7.83/1.50  --share_sel_clauses                     true
% 7.83/1.50  --reset_solvers                         false
% 7.83/1.50  --bc_imp_inh                            [conj_cone]
% 7.83/1.50  --conj_cone_tolerance                   3.
% 7.83/1.50  --extra_neg_conj                        none
% 7.83/1.50  --large_theory_mode                     true
% 7.83/1.50  --prolific_symb_bound                   200
% 7.83/1.50  --lt_threshold                          2000
% 7.83/1.50  --clause_weak_htbl                      true
% 7.83/1.50  --gc_record_bc_elim                     false
% 7.83/1.50  
% 7.83/1.50  ------ Preprocessing Options
% 7.83/1.50  
% 7.83/1.50  --preprocessing_flag                    true
% 7.83/1.50  --time_out_prep_mult                    0.1
% 7.83/1.50  --splitting_mode                        input
% 7.83/1.50  --splitting_grd                         true
% 7.83/1.50  --splitting_cvd                         false
% 7.83/1.50  --splitting_cvd_svl                     false
% 7.83/1.50  --splitting_nvd                         32
% 7.83/1.50  --sub_typing                            true
% 7.83/1.50  --prep_gs_sim                           true
% 7.83/1.50  --prep_unflatten                        true
% 7.83/1.50  --prep_res_sim                          true
% 7.83/1.50  --prep_upred                            true
% 7.83/1.50  --prep_sem_filter                       exhaustive
% 7.83/1.50  --prep_sem_filter_out                   false
% 7.83/1.50  --pred_elim                             true
% 7.83/1.50  --res_sim_input                         true
% 7.83/1.50  --eq_ax_congr_red                       true
% 7.83/1.50  --pure_diseq_elim                       true
% 7.83/1.50  --brand_transform                       false
% 7.83/1.50  --non_eq_to_eq                          false
% 7.83/1.50  --prep_def_merge                        true
% 7.83/1.50  --prep_def_merge_prop_impl              false
% 7.83/1.50  --prep_def_merge_mbd                    true
% 7.83/1.50  --prep_def_merge_tr_red                 false
% 7.83/1.50  --prep_def_merge_tr_cl                  false
% 7.83/1.50  --smt_preprocessing                     true
% 7.83/1.50  --smt_ac_axioms                         fast
% 7.83/1.50  --preprocessed_out                      false
% 7.83/1.50  --preprocessed_stats                    false
% 7.83/1.50  
% 7.83/1.50  ------ Abstraction refinement Options
% 7.83/1.50  
% 7.83/1.50  --abstr_ref                             []
% 7.83/1.50  --abstr_ref_prep                        false
% 7.83/1.50  --abstr_ref_until_sat                   false
% 7.83/1.50  --abstr_ref_sig_restrict                funpre
% 7.83/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.83/1.50  --abstr_ref_under                       []
% 7.83/1.50  
% 7.83/1.50  ------ SAT Options
% 7.83/1.50  
% 7.83/1.50  --sat_mode                              false
% 7.83/1.50  --sat_fm_restart_options                ""
% 7.83/1.50  --sat_gr_def                            false
% 7.83/1.50  --sat_epr_types                         true
% 7.83/1.50  --sat_non_cyclic_types                  false
% 7.83/1.50  --sat_finite_models                     false
% 7.83/1.50  --sat_fm_lemmas                         false
% 7.83/1.50  --sat_fm_prep                           false
% 7.83/1.50  --sat_fm_uc_incr                        true
% 7.83/1.50  --sat_out_model                         small
% 7.83/1.50  --sat_out_clauses                       false
% 7.83/1.50  
% 7.83/1.50  ------ QBF Options
% 7.83/1.50  
% 7.83/1.50  --qbf_mode                              false
% 7.83/1.50  --qbf_elim_univ                         false
% 7.83/1.50  --qbf_dom_inst                          none
% 7.83/1.50  --qbf_dom_pre_inst                      false
% 7.83/1.50  --qbf_sk_in                             false
% 7.83/1.50  --qbf_pred_elim                         true
% 7.83/1.50  --qbf_split                             512
% 7.83/1.50  
% 7.83/1.50  ------ BMC1 Options
% 7.83/1.50  
% 7.83/1.50  --bmc1_incremental                      false
% 7.83/1.50  --bmc1_axioms                           reachable_all
% 7.83/1.50  --bmc1_min_bound                        0
% 7.83/1.50  --bmc1_max_bound                        -1
% 7.83/1.50  --bmc1_max_bound_default                -1
% 7.83/1.50  --bmc1_symbol_reachability              true
% 7.83/1.50  --bmc1_property_lemmas                  false
% 7.83/1.50  --bmc1_k_induction                      false
% 7.83/1.50  --bmc1_non_equiv_states                 false
% 7.83/1.50  --bmc1_deadlock                         false
% 7.83/1.50  --bmc1_ucm                              false
% 7.83/1.50  --bmc1_add_unsat_core                   none
% 7.83/1.50  --bmc1_unsat_core_children              false
% 7.83/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.83/1.50  --bmc1_out_stat                         full
% 7.83/1.50  --bmc1_ground_init                      false
% 7.83/1.50  --bmc1_pre_inst_next_state              false
% 7.83/1.50  --bmc1_pre_inst_state                   false
% 7.83/1.50  --bmc1_pre_inst_reach_state             false
% 7.83/1.50  --bmc1_out_unsat_core                   false
% 7.83/1.50  --bmc1_aig_witness_out                  false
% 7.83/1.50  --bmc1_verbose                          false
% 7.83/1.50  --bmc1_dump_clauses_tptp                false
% 7.83/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.83/1.50  --bmc1_dump_file                        -
% 7.83/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.83/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.83/1.50  --bmc1_ucm_extend_mode                  1
% 7.83/1.50  --bmc1_ucm_init_mode                    2
% 7.83/1.50  --bmc1_ucm_cone_mode                    none
% 7.83/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.83/1.50  --bmc1_ucm_relax_model                  4
% 7.83/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.83/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.83/1.50  --bmc1_ucm_layered_model                none
% 7.83/1.50  --bmc1_ucm_max_lemma_size               10
% 7.83/1.50  
% 7.83/1.50  ------ AIG Options
% 7.83/1.50  
% 7.83/1.50  --aig_mode                              false
% 7.83/1.50  
% 7.83/1.50  ------ Instantiation Options
% 7.83/1.50  
% 7.83/1.50  --instantiation_flag                    true
% 7.83/1.50  --inst_sos_flag                         true
% 7.83/1.50  --inst_sos_phase                        true
% 7.83/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.83/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.83/1.50  --inst_lit_sel_side                     num_symb
% 7.83/1.50  --inst_solver_per_active                1400
% 7.83/1.50  --inst_solver_calls_frac                1.
% 7.83/1.50  --inst_passive_queue_type               priority_queues
% 7.83/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.83/1.50  --inst_passive_queues_freq              [25;2]
% 7.83/1.50  --inst_dismatching                      true
% 7.83/1.50  --inst_eager_unprocessed_to_passive     true
% 7.83/1.50  --inst_prop_sim_given                   true
% 7.83/1.50  --inst_prop_sim_new                     false
% 7.83/1.50  --inst_subs_new                         false
% 7.83/1.50  --inst_eq_res_simp                      false
% 7.83/1.50  --inst_subs_given                       false
% 7.83/1.50  --inst_orphan_elimination               true
% 7.83/1.50  --inst_learning_loop_flag               true
% 7.83/1.50  --inst_learning_start                   3000
% 7.83/1.50  --inst_learning_factor                  2
% 7.83/1.50  --inst_start_prop_sim_after_learn       3
% 7.83/1.50  --inst_sel_renew                        solver
% 7.83/1.50  --inst_lit_activity_flag                true
% 7.83/1.50  --inst_restr_to_given                   false
% 7.83/1.50  --inst_activity_threshold               500
% 7.83/1.50  --inst_out_proof                        true
% 7.83/1.50  
% 7.83/1.50  ------ Resolution Options
% 7.83/1.50  
% 7.83/1.50  --resolution_flag                       true
% 7.83/1.50  --res_lit_sel                           adaptive
% 7.83/1.50  --res_lit_sel_side                      none
% 7.83/1.50  --res_ordering                          kbo
% 7.83/1.50  --res_to_prop_solver                    active
% 7.83/1.50  --res_prop_simpl_new                    false
% 7.83/1.50  --res_prop_simpl_given                  true
% 7.83/1.50  --res_passive_queue_type                priority_queues
% 7.83/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.83/1.50  --res_passive_queues_freq               [15;5]
% 7.83/1.50  --res_forward_subs                      full
% 7.83/1.50  --res_backward_subs                     full
% 7.83/1.50  --res_forward_subs_resolution           true
% 7.83/1.50  --res_backward_subs_resolution          true
% 7.83/1.50  --res_orphan_elimination                true
% 7.83/1.50  --res_time_limit                        2.
% 7.83/1.50  --res_out_proof                         true
% 7.83/1.50  
% 7.83/1.50  ------ Superposition Options
% 7.83/1.50  
% 7.83/1.50  --superposition_flag                    true
% 7.83/1.50  --sup_passive_queue_type                priority_queues
% 7.83/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.83/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.83/1.50  --demod_completeness_check              fast
% 7.83/1.50  --demod_use_ground                      true
% 7.83/1.50  --sup_to_prop_solver                    passive
% 7.83/1.50  --sup_prop_simpl_new                    true
% 7.83/1.50  --sup_prop_simpl_given                  true
% 7.83/1.50  --sup_fun_splitting                     true
% 7.83/1.50  --sup_smt_interval                      50000
% 7.83/1.50  
% 7.83/1.50  ------ Superposition Simplification Setup
% 7.83/1.50  
% 7.83/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.83/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.83/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.83/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.83/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.83/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.83/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.83/1.50  --sup_immed_triv                        [TrivRules]
% 7.83/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.50  --sup_immed_bw_main                     []
% 7.83/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.83/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.83/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.50  --sup_input_bw                          []
% 7.83/1.50  
% 7.83/1.50  ------ Combination Options
% 7.83/1.50  
% 7.83/1.50  --comb_res_mult                         3
% 7.83/1.50  --comb_sup_mult                         2
% 7.83/1.50  --comb_inst_mult                        10
% 7.83/1.50  
% 7.83/1.50  ------ Debug Options
% 7.83/1.50  
% 7.83/1.50  --dbg_backtrace                         false
% 7.83/1.50  --dbg_dump_prop_clauses                 false
% 7.83/1.50  --dbg_dump_prop_clauses_file            -
% 7.83/1.50  --dbg_out_stat                          false
% 7.83/1.50  ------ Parsing...
% 7.83/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.83/1.50  
% 7.83/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.83/1.50  
% 7.83/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.83/1.50  
% 7.83/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.50  ------ Proving...
% 7.83/1.50  ------ Problem Properties 
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  clauses                                 32
% 7.83/1.50  conjectures                             1
% 7.83/1.50  EPR                                     9
% 7.83/1.50  Horn                                    22
% 7.83/1.50  unary                                   6
% 7.83/1.50  binary                                  12
% 7.83/1.50  lits                                    76
% 7.83/1.50  lits eq                                 8
% 7.83/1.50  fd_pure                                 0
% 7.83/1.50  fd_pseudo                               0
% 7.83/1.50  fd_cond                                 0
% 7.83/1.50  fd_pseudo_cond                          4
% 7.83/1.50  AC symbols                              0
% 7.83/1.50  
% 7.83/1.50  ------ Schedule dynamic 5 is on 
% 7.83/1.50  
% 7.83/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  ------ 
% 7.83/1.50  Current options:
% 7.83/1.50  ------ 
% 7.83/1.50  
% 7.83/1.50  ------ Input Options
% 7.83/1.50  
% 7.83/1.50  --out_options                           all
% 7.83/1.50  --tptp_safe_out                         true
% 7.83/1.50  --problem_path                          ""
% 7.83/1.50  --include_path                          ""
% 7.83/1.50  --clausifier                            res/vclausify_rel
% 7.83/1.50  --clausifier_options                    ""
% 7.83/1.50  --stdin                                 false
% 7.83/1.50  --stats_out                             all
% 7.83/1.50  
% 7.83/1.50  ------ General Options
% 7.83/1.50  
% 7.83/1.50  --fof                                   false
% 7.83/1.50  --time_out_real                         305.
% 7.83/1.50  --time_out_virtual                      -1.
% 7.83/1.50  --symbol_type_check                     false
% 7.83/1.50  --clausify_out                          false
% 7.83/1.50  --sig_cnt_out                           false
% 7.83/1.50  --trig_cnt_out                          false
% 7.83/1.50  --trig_cnt_out_tolerance                1.
% 7.83/1.50  --trig_cnt_out_sk_spl                   false
% 7.83/1.50  --abstr_cl_out                          false
% 7.83/1.50  
% 7.83/1.50  ------ Global Options
% 7.83/1.50  
% 7.83/1.50  --schedule                              default
% 7.83/1.50  --add_important_lit                     false
% 7.83/1.50  --prop_solver_per_cl                    1000
% 7.83/1.50  --min_unsat_core                        false
% 7.83/1.50  --soft_assumptions                      false
% 7.83/1.50  --soft_lemma_size                       3
% 7.83/1.50  --prop_impl_unit_size                   0
% 7.83/1.50  --prop_impl_unit                        []
% 7.83/1.50  --share_sel_clauses                     true
% 7.83/1.50  --reset_solvers                         false
% 7.83/1.50  --bc_imp_inh                            [conj_cone]
% 7.83/1.50  --conj_cone_tolerance                   3.
% 7.83/1.50  --extra_neg_conj                        none
% 7.83/1.50  --large_theory_mode                     true
% 7.83/1.50  --prolific_symb_bound                   200
% 7.83/1.50  --lt_threshold                          2000
% 7.83/1.50  --clause_weak_htbl                      true
% 7.83/1.50  --gc_record_bc_elim                     false
% 7.83/1.50  
% 7.83/1.50  ------ Preprocessing Options
% 7.83/1.50  
% 7.83/1.50  --preprocessing_flag                    true
% 7.83/1.50  --time_out_prep_mult                    0.1
% 7.83/1.50  --splitting_mode                        input
% 7.83/1.50  --splitting_grd                         true
% 7.83/1.50  --splitting_cvd                         false
% 7.83/1.50  --splitting_cvd_svl                     false
% 7.83/1.50  --splitting_nvd                         32
% 7.83/1.50  --sub_typing                            true
% 7.83/1.50  --prep_gs_sim                           true
% 7.83/1.50  --prep_unflatten                        true
% 7.83/1.50  --prep_res_sim                          true
% 7.83/1.50  --prep_upred                            true
% 7.83/1.50  --prep_sem_filter                       exhaustive
% 7.83/1.50  --prep_sem_filter_out                   false
% 7.83/1.50  --pred_elim                             true
% 7.83/1.50  --res_sim_input                         true
% 7.83/1.50  --eq_ax_congr_red                       true
% 7.83/1.50  --pure_diseq_elim                       true
% 7.83/1.50  --brand_transform                       false
% 7.83/1.50  --non_eq_to_eq                          false
% 7.83/1.50  --prep_def_merge                        true
% 7.83/1.50  --prep_def_merge_prop_impl              false
% 7.83/1.50  --prep_def_merge_mbd                    true
% 7.83/1.50  --prep_def_merge_tr_red                 false
% 7.83/1.50  --prep_def_merge_tr_cl                  false
% 7.83/1.50  --smt_preprocessing                     true
% 7.83/1.50  --smt_ac_axioms                         fast
% 7.83/1.50  --preprocessed_out                      false
% 7.83/1.50  --preprocessed_stats                    false
% 7.83/1.50  
% 7.83/1.50  ------ Abstraction refinement Options
% 7.83/1.50  
% 7.83/1.50  --abstr_ref                             []
% 7.83/1.50  --abstr_ref_prep                        false
% 7.83/1.50  --abstr_ref_until_sat                   false
% 7.83/1.50  --abstr_ref_sig_restrict                funpre
% 7.83/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.83/1.50  --abstr_ref_under                       []
% 7.83/1.50  
% 7.83/1.50  ------ SAT Options
% 7.83/1.50  
% 7.83/1.50  --sat_mode                              false
% 7.83/1.50  --sat_fm_restart_options                ""
% 7.83/1.50  --sat_gr_def                            false
% 7.83/1.50  --sat_epr_types                         true
% 7.83/1.50  --sat_non_cyclic_types                  false
% 7.83/1.50  --sat_finite_models                     false
% 7.83/1.50  --sat_fm_lemmas                         false
% 7.83/1.50  --sat_fm_prep                           false
% 7.83/1.50  --sat_fm_uc_incr                        true
% 7.83/1.50  --sat_out_model                         small
% 7.83/1.50  --sat_out_clauses                       false
% 7.83/1.50  
% 7.83/1.50  ------ QBF Options
% 7.83/1.50  
% 7.83/1.50  --qbf_mode                              false
% 7.83/1.50  --qbf_elim_univ                         false
% 7.83/1.50  --qbf_dom_inst                          none
% 7.83/1.50  --qbf_dom_pre_inst                      false
% 7.83/1.50  --qbf_sk_in                             false
% 7.83/1.50  --qbf_pred_elim                         true
% 7.83/1.50  --qbf_split                             512
% 7.83/1.50  
% 7.83/1.50  ------ BMC1 Options
% 7.83/1.50  
% 7.83/1.50  --bmc1_incremental                      false
% 7.83/1.50  --bmc1_axioms                           reachable_all
% 7.83/1.50  --bmc1_min_bound                        0
% 7.83/1.50  --bmc1_max_bound                        -1
% 7.83/1.50  --bmc1_max_bound_default                -1
% 7.83/1.50  --bmc1_symbol_reachability              true
% 7.83/1.50  --bmc1_property_lemmas                  false
% 7.83/1.50  --bmc1_k_induction                      false
% 7.83/1.50  --bmc1_non_equiv_states                 false
% 7.83/1.50  --bmc1_deadlock                         false
% 7.83/1.50  --bmc1_ucm                              false
% 7.83/1.50  --bmc1_add_unsat_core                   none
% 7.83/1.50  --bmc1_unsat_core_children              false
% 7.83/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.83/1.50  --bmc1_out_stat                         full
% 7.83/1.50  --bmc1_ground_init                      false
% 7.83/1.50  --bmc1_pre_inst_next_state              false
% 7.83/1.50  --bmc1_pre_inst_state                   false
% 7.83/1.50  --bmc1_pre_inst_reach_state             false
% 7.83/1.50  --bmc1_out_unsat_core                   false
% 7.83/1.50  --bmc1_aig_witness_out                  false
% 7.83/1.50  --bmc1_verbose                          false
% 7.83/1.50  --bmc1_dump_clauses_tptp                false
% 7.83/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.83/1.50  --bmc1_dump_file                        -
% 7.83/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.83/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.83/1.50  --bmc1_ucm_extend_mode                  1
% 7.83/1.50  --bmc1_ucm_init_mode                    2
% 7.83/1.50  --bmc1_ucm_cone_mode                    none
% 7.83/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.83/1.50  --bmc1_ucm_relax_model                  4
% 7.83/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.83/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.83/1.50  --bmc1_ucm_layered_model                none
% 7.83/1.50  --bmc1_ucm_max_lemma_size               10
% 7.83/1.50  
% 7.83/1.50  ------ AIG Options
% 7.83/1.50  
% 7.83/1.50  --aig_mode                              false
% 7.83/1.50  
% 7.83/1.50  ------ Instantiation Options
% 7.83/1.50  
% 7.83/1.50  --instantiation_flag                    true
% 7.83/1.50  --inst_sos_flag                         true
% 7.83/1.50  --inst_sos_phase                        true
% 7.83/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.83/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.83/1.50  --inst_lit_sel_side                     none
% 7.83/1.50  --inst_solver_per_active                1400
% 7.83/1.50  --inst_solver_calls_frac                1.
% 7.83/1.50  --inst_passive_queue_type               priority_queues
% 7.83/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.83/1.50  --inst_passive_queues_freq              [25;2]
% 7.83/1.50  --inst_dismatching                      true
% 7.83/1.50  --inst_eager_unprocessed_to_passive     true
% 7.83/1.50  --inst_prop_sim_given                   true
% 7.83/1.50  --inst_prop_sim_new                     false
% 7.83/1.50  --inst_subs_new                         false
% 7.83/1.50  --inst_eq_res_simp                      false
% 7.83/1.50  --inst_subs_given                       false
% 7.83/1.50  --inst_orphan_elimination               true
% 7.83/1.50  --inst_learning_loop_flag               true
% 7.83/1.50  --inst_learning_start                   3000
% 7.83/1.50  --inst_learning_factor                  2
% 7.83/1.50  --inst_start_prop_sim_after_learn       3
% 7.83/1.50  --inst_sel_renew                        solver
% 7.83/1.50  --inst_lit_activity_flag                true
% 7.83/1.50  --inst_restr_to_given                   false
% 7.83/1.50  --inst_activity_threshold               500
% 7.83/1.50  --inst_out_proof                        true
% 7.83/1.50  
% 7.83/1.50  ------ Resolution Options
% 7.83/1.50  
% 7.83/1.50  --resolution_flag                       false
% 7.83/1.50  --res_lit_sel                           adaptive
% 7.83/1.50  --res_lit_sel_side                      none
% 7.83/1.50  --res_ordering                          kbo
% 7.83/1.50  --res_to_prop_solver                    active
% 7.83/1.50  --res_prop_simpl_new                    false
% 7.83/1.50  --res_prop_simpl_given                  true
% 7.83/1.50  --res_passive_queue_type                priority_queues
% 7.83/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.83/1.50  --res_passive_queues_freq               [15;5]
% 7.83/1.50  --res_forward_subs                      full
% 7.83/1.50  --res_backward_subs                     full
% 7.83/1.50  --res_forward_subs_resolution           true
% 7.83/1.50  --res_backward_subs_resolution          true
% 7.83/1.50  --res_orphan_elimination                true
% 7.83/1.50  --res_time_limit                        2.
% 7.83/1.50  --res_out_proof                         true
% 7.83/1.50  
% 7.83/1.50  ------ Superposition Options
% 7.83/1.50  
% 7.83/1.50  --superposition_flag                    true
% 7.83/1.50  --sup_passive_queue_type                priority_queues
% 7.83/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.83/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.83/1.50  --demod_completeness_check              fast
% 7.83/1.50  --demod_use_ground                      true
% 7.83/1.50  --sup_to_prop_solver                    passive
% 7.83/1.50  --sup_prop_simpl_new                    true
% 7.83/1.50  --sup_prop_simpl_given                  true
% 7.83/1.50  --sup_fun_splitting                     true
% 7.83/1.50  --sup_smt_interval                      50000
% 7.83/1.50  
% 7.83/1.50  ------ Superposition Simplification Setup
% 7.83/1.50  
% 7.83/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.83/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.83/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.83/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.83/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.83/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.83/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.83/1.50  --sup_immed_triv                        [TrivRules]
% 7.83/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.50  --sup_immed_bw_main                     []
% 7.83/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.83/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.83/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.50  --sup_input_bw                          []
% 7.83/1.50  
% 7.83/1.50  ------ Combination Options
% 7.83/1.50  
% 7.83/1.50  --comb_res_mult                         3
% 7.83/1.50  --comb_sup_mult                         2
% 7.83/1.50  --comb_inst_mult                        10
% 7.83/1.50  
% 7.83/1.50  ------ Debug Options
% 7.83/1.50  
% 7.83/1.50  --dbg_backtrace                         false
% 7.83/1.50  --dbg_dump_prop_clauses                 false
% 7.83/1.50  --dbg_dump_prop_clauses_file            -
% 7.83/1.50  --dbg_out_stat                          false
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  ------ Proving...
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  % SZS status Theorem for theBenchmark.p
% 7.83/1.50  
% 7.83/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.83/1.50  
% 7.83/1.50  fof(f1,axiom,(
% 7.83/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f16,plain,(
% 7.83/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.83/1.50    inference(ennf_transformation,[],[f1])).
% 7.83/1.50  
% 7.83/1.50  fof(f29,plain,(
% 7.83/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.83/1.50    inference(nnf_transformation,[],[f16])).
% 7.83/1.50  
% 7.83/1.50  fof(f30,plain,(
% 7.83/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.83/1.50    inference(rectify,[],[f29])).
% 7.83/1.50  
% 7.83/1.50  fof(f31,plain,(
% 7.83/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f32,plain,(
% 7.83/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.83/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 7.83/1.50  
% 7.83/1.50  fof(f57,plain,(
% 7.83/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f32])).
% 7.83/1.50  
% 7.83/1.50  fof(f3,axiom,(
% 7.83/1.50    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f35,plain,(
% 7.83/1.50    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 7.83/1.50    inference(nnf_transformation,[],[f3])).
% 7.83/1.50  
% 7.83/1.50  fof(f36,plain,(
% 7.83/1.50    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.83/1.50    inference(rectify,[],[f35])).
% 7.83/1.50  
% 7.83/1.50  fof(f39,plain,(
% 7.83/1.50    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f38,plain,(
% 7.83/1.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(X2,sK3(X0,X1))))) )),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f37,plain,(
% 7.83/1.50    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f40,plain,(
% 7.83/1.50    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.83/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f39,f38,f37])).
% 7.83/1.50  
% 7.83/1.50  fof(f63,plain,(
% 7.83/1.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 7.83/1.50    inference(cnf_transformation,[],[f40])).
% 7.83/1.50  
% 7.83/1.50  fof(f95,plain,(
% 7.83/1.50    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 7.83/1.50    inference(equality_resolution,[],[f63])).
% 7.83/1.50  
% 7.83/1.50  fof(f8,axiom,(
% 7.83/1.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f19,plain,(
% 7.83/1.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.83/1.50    inference(ennf_transformation,[],[f8])).
% 7.83/1.50  
% 7.83/1.50  fof(f75,plain,(
% 7.83/1.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f19])).
% 7.83/1.50  
% 7.83/1.50  fof(f7,axiom,(
% 7.83/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f42,plain,(
% 7.83/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.83/1.50    inference(nnf_transformation,[],[f7])).
% 7.83/1.50  
% 7.83/1.50  fof(f74,plain,(
% 7.83/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f42])).
% 7.83/1.50  
% 7.83/1.50  fof(f10,axiom,(
% 7.83/1.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f22,plain,(
% 7.83/1.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.83/1.50    inference(ennf_transformation,[],[f10])).
% 7.83/1.50  
% 7.83/1.50  fof(f88,plain,(
% 7.83/1.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f22])).
% 7.83/1.50  
% 7.83/1.50  fof(f12,conjecture,(
% 7.83/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f13,negated_conjecture,(
% 7.83/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 7.83/1.50    inference(negated_conjecture,[],[f12])).
% 7.83/1.50  
% 7.83/1.50  fof(f15,plain,(
% 7.83/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 7.83/1.50    inference(pure_predicate_removal,[],[f13])).
% 7.83/1.50  
% 7.83/1.50  fof(f25,plain,(
% 7.83/1.50    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.83/1.50    inference(ennf_transformation,[],[f15])).
% 7.83/1.50  
% 7.83/1.50  fof(f26,plain,(
% 7.83/1.50    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.83/1.50    inference(flattening,[],[f25])).
% 7.83/1.50  
% 7.83/1.50  fof(f53,plain,(
% 7.83/1.50    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) & l1_pre_topc(sK8) & v2_pre_topc(sK8))),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f54,plain,(
% 7.83/1.50    u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) & l1_pre_topc(sK8) & v2_pre_topc(sK8)),
% 7.83/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f26,f53])).
% 7.83/1.50  
% 7.83/1.50  fof(f91,plain,(
% 7.83/1.50    l1_pre_topc(sK8)),
% 7.83/1.50    inference(cnf_transformation,[],[f54])).
% 7.83/1.50  
% 7.83/1.50  fof(f5,axiom,(
% 7.83/1.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f17,plain,(
% 7.83/1.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.83/1.50    inference(ennf_transformation,[],[f5])).
% 7.83/1.50  
% 7.83/1.50  fof(f41,plain,(
% 7.83/1.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.83/1.50    inference(nnf_transformation,[],[f17])).
% 7.83/1.50  
% 7.83/1.50  fof(f68,plain,(
% 7.83/1.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f41])).
% 7.83/1.50  
% 7.83/1.50  fof(f90,plain,(
% 7.83/1.50    v2_pre_topc(sK8)),
% 7.83/1.50    inference(cnf_transformation,[],[f54])).
% 7.83/1.50  
% 7.83/1.50  fof(f9,axiom,(
% 7.83/1.50    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f14,plain,(
% 7.83/1.50    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.83/1.50    inference(rectify,[],[f9])).
% 7.83/1.50  
% 7.83/1.50  fof(f20,plain,(
% 7.83/1.50    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.83/1.50    inference(ennf_transformation,[],[f14])).
% 7.83/1.50  
% 7.83/1.50  fof(f21,plain,(
% 7.83/1.50    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.83/1.50    inference(flattening,[],[f20])).
% 7.83/1.50  
% 7.83/1.50  fof(f27,plain,(
% 7.83/1.50    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.83/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.83/1.50  
% 7.83/1.50  fof(f28,plain,(
% 7.83/1.50    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.83/1.50    inference(definition_folding,[],[f21,f27])).
% 7.83/1.50  
% 7.83/1.50  fof(f48,plain,(
% 7.83/1.50    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.83/1.50    inference(nnf_transformation,[],[f28])).
% 7.83/1.50  
% 7.83/1.50  fof(f49,plain,(
% 7.83/1.50    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.83/1.50    inference(flattening,[],[f48])).
% 7.83/1.50  
% 7.83/1.50  fof(f50,plain,(
% 7.83/1.50    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.83/1.50    inference(rectify,[],[f49])).
% 7.83/1.50  
% 7.83/1.50  fof(f51,plain,(
% 7.83/1.50    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f52,plain,(
% 7.83/1.50    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.83/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f50,f51])).
% 7.83/1.50  
% 7.83/1.50  fof(f82,plain,(
% 7.83/1.50    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f52])).
% 7.83/1.50  
% 7.83/1.50  fof(f2,axiom,(
% 7.83/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f33,plain,(
% 7.83/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.83/1.50    inference(nnf_transformation,[],[f2])).
% 7.83/1.50  
% 7.83/1.50  fof(f34,plain,(
% 7.83/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.83/1.50    inference(flattening,[],[f33])).
% 7.83/1.50  
% 7.83/1.50  fof(f58,plain,(
% 7.83/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.83/1.50    inference(cnf_transformation,[],[f34])).
% 7.83/1.50  
% 7.83/1.50  fof(f94,plain,(
% 7.83/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.83/1.50    inference(equality_resolution,[],[f58])).
% 7.83/1.50  
% 7.83/1.50  fof(f70,plain,(
% 7.83/1.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f41])).
% 7.83/1.50  
% 7.83/1.50  fof(f4,axiom,(
% 7.83/1.50    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f67,plain,(
% 7.83/1.50    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 7.83/1.50    inference(cnf_transformation,[],[f4])).
% 7.83/1.50  
% 7.83/1.50  fof(f6,axiom,(
% 7.83/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f18,plain,(
% 7.83/1.50    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.83/1.50    inference(ennf_transformation,[],[f6])).
% 7.83/1.50  
% 7.83/1.50  fof(f72,plain,(
% 7.83/1.50    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.83/1.50    inference(cnf_transformation,[],[f18])).
% 7.83/1.50  
% 7.83/1.50  fof(f83,plain,(
% 7.83/1.50    ( ! [X2,X0] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f52])).
% 7.83/1.50  
% 7.83/1.50  fof(f69,plain,(
% 7.83/1.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f41])).
% 7.83/1.50  
% 7.83/1.50  fof(f73,plain,(
% 7.83/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.83/1.50    inference(cnf_transformation,[],[f42])).
% 7.83/1.50  
% 7.83/1.50  fof(f60,plain,(
% 7.83/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f34])).
% 7.83/1.50  
% 7.83/1.50  fof(f56,plain,(
% 7.83/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f32])).
% 7.83/1.50  
% 7.83/1.50  fof(f11,axiom,(
% 7.83/1.50    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f23,plain,(
% 7.83/1.50    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 7.83/1.50    inference(ennf_transformation,[],[f11])).
% 7.83/1.50  
% 7.83/1.50  fof(f24,plain,(
% 7.83/1.50    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 7.83/1.50    inference(flattening,[],[f23])).
% 7.83/1.50  
% 7.83/1.50  fof(f89,plain,(
% 7.83/1.50    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f24])).
% 7.83/1.50  
% 7.83/1.50  fof(f92,plain,(
% 7.83/1.50    u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8)))),
% 7.83/1.50    inference(cnf_transformation,[],[f54])).
% 7.83/1.50  
% 7.83/1.50  cnf(c_0,plain,
% 7.83/1.50      ( ~ r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.83/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2346,plain,
% 7.83/1.50      ( ~ r2_hidden(sK1(u1_struct_0(sK8),X0),X0)
% 7.83/1.50      | r1_tarski(u1_struct_0(sK8),X0) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_11686,plain,
% 7.83/1.50      ( ~ r2_hidden(sK1(u1_struct_0(sK8),k3_tarski(X0)),k3_tarski(X0))
% 7.83/1.50      | r1_tarski(u1_struct_0(sK8),k3_tarski(X0)) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_2346]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_30647,plain,
% 7.83/1.50      ( ~ r2_hidden(sK1(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))),k3_tarski(u1_pre_topc(sK8)))
% 7.83/1.50      | r1_tarski(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_11686]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_9,plain,
% 7.83/1.50      ( ~ r2_hidden(X0,X1)
% 7.83/1.50      | ~ r2_hidden(X2,X0)
% 7.83/1.50      | r2_hidden(X2,k3_tarski(X1)) ),
% 7.83/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3964,plain,
% 7.83/1.50      ( ~ r2_hidden(X0,u1_struct_0(sK8))
% 7.83/1.50      | r2_hidden(X0,k3_tarski(u1_pre_topc(sK8)))
% 7.83/1.50      | ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_13567,plain,
% 7.83/1.50      ( ~ r2_hidden(sK1(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))),u1_struct_0(sK8))
% 7.83/1.50      | r2_hidden(sK1(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))),k3_tarski(u1_pre_topc(sK8)))
% 7.83/1.50      | ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_3964]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_20,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.83/1.50      | ~ r2_hidden(X2,X0)
% 7.83/1.50      | ~ v1_xboole_0(X1) ),
% 7.83/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_18,plain,
% 7.83/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.83/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_285,plain,
% 7.83/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.83/1.50      inference(prop_impl,[status(thm)],[c_18]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_286,plain,
% 7.83/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_285]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_355,plain,
% 7.83/1.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 7.83/1.50      inference(bin_hyper_res,[status(thm)],[c_20,c_286]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1887,plain,
% 7.83/1.50      ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 7.83/1.50      | ~ r1_tarski(u1_pre_topc(sK8),X0)
% 7.83/1.50      | ~ v1_xboole_0(X0) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_355]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_7662,plain,
% 7.83/1.50      ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 7.83/1.50      | ~ r1_tarski(u1_pre_topc(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
% 7.83/1.50      | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_1887]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_33,plain,
% 7.83/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.83/1.50      | ~ l1_pre_topc(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_36,negated_conjecture,
% 7.83/1.50      ( l1_pre_topc(sK8) ),
% 7.83/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_479,plain,
% 7.83/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.83/1.50      | sK8 != X0 ),
% 7.83/1.50      inference(resolution_lifted,[status(thm)],[c_33,c_36]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_480,plain,
% 7.83/1.50      ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
% 7.83/1.50      inference(unflattening,[status(thm)],[c_479]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1821,plain,
% 7.83/1.50      ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_16,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.83/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1833,plain,
% 7.83/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.83/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.83/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3634,plain,
% 7.83/1.50      ( r2_hidden(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top
% 7.83/1.50      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1821,c_1833]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_37,negated_conjecture,
% 7.83/1.50      ( v2_pre_topc(sK8) ),
% 7.83/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_38,plain,
% 7.83/1.50      ( v2_pre_topc(sK8) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_39,plain,
% 7.83/1.50      ( l1_pre_topc(sK8) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_43,plain,
% 7.83/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.83/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_45,plain,
% 7.83/1.50      ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top
% 7.83/1.50      | l1_pre_topc(sK8) != iProver_top ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_43]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_32,plain,
% 7.83/1.50      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 7.83/1.50      | ~ l1_pre_topc(X0)
% 7.83/1.50      | ~ v2_pre_topc(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_46,plain,
% 7.83/1.50      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 7.83/1.50      | l1_pre_topc(X0) != iProver_top
% 7.83/1.50      | v2_pre_topc(X0) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_48,plain,
% 7.83/1.50      ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) = iProver_top
% 7.83/1.50      | l1_pre_topc(sK8) != iProver_top
% 7.83/1.50      | v2_pre_topc(sK8) != iProver_top ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_46]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5,plain,
% 7.83/1.50      ( r1_tarski(X0,X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1947,plain,
% 7.83/1.50      ( r1_tarski(u1_pre_topc(sK8),u1_pre_topc(sK8)) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1948,plain,
% 7.83/1.50      ( r1_tarski(u1_pre_topc(sK8),u1_pre_topc(sK8)) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_1947]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2195,plain,
% 7.83/1.50      ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 7.83/1.50      | ~ r1_tarski(u1_pre_topc(sK8),u1_pre_topc(sK8))
% 7.83/1.50      | ~ v1_xboole_0(u1_pre_topc(sK8)) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_1887]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2196,plain,
% 7.83/1.50      ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) != iProver_top
% 7.83/1.50      | r1_tarski(u1_pre_topc(sK8),u1_pre_topc(sK8)) != iProver_top
% 7.83/1.50      | v1_xboole_0(u1_pre_topc(sK8)) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_2195]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2267,plain,
% 7.83/1.50      ( ~ m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
% 7.83/1.50      | r2_hidden(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
% 7.83/1.50      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2268,plain,
% 7.83/1.50      ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
% 7.83/1.50      | r2_hidden(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top
% 7.83/1.50      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_2267]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_14,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1835,plain,
% 7.83/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.83/1.50      | v1_xboole_0(X1) != iProver_top
% 7.83/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3152,plain,
% 7.83/1.50      ( v1_xboole_0(u1_pre_topc(sK8)) = iProver_top
% 7.83/1.50      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1821,c_1835]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4101,plain,
% 7.83/1.50      ( r2_hidden(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_3634,c_38,c_39,c_45,c_48,c_1948,c_2196,c_2268,c_3152]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_12,plain,
% 7.83/1.50      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 7.83/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_17,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.83/1.50      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1832,plain,
% 7.83/1.50      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 7.83/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2756,plain,
% 7.83/1.50      ( k5_setfam_1(u1_struct_0(sK8),u1_pre_topc(sK8)) = k3_tarski(u1_pre_topc(sK8)) ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1821,c_1832]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_31,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.83/1.50      | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 7.83/1.50      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 7.83/1.50      | ~ l1_pre_topc(X1)
% 7.83/1.50      | ~ v2_pre_topc(X1) ),
% 7.83/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_514,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.83/1.50      | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 7.83/1.50      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 7.83/1.50      | ~ v2_pre_topc(X1)
% 7.83/1.50      | sK8 != X1 ),
% 7.83/1.50      inference(resolution_lifted,[status(thm)],[c_31,c_36]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_515,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
% 7.83/1.50      | r2_hidden(k5_setfam_1(u1_struct_0(sK8),X0),u1_pre_topc(sK8))
% 7.83/1.50      | ~ r1_tarski(X0,u1_pre_topc(sK8))
% 7.83/1.50      | ~ v2_pre_topc(sK8) ),
% 7.83/1.50      inference(unflattening,[status(thm)],[c_514]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_519,plain,
% 7.83/1.50      ( ~ r1_tarski(X0,u1_pre_topc(sK8))
% 7.83/1.50      | r2_hidden(k5_setfam_1(u1_struct_0(sK8),X0),u1_pre_topc(sK8))
% 7.83/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_515,c_37]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_520,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
% 7.83/1.50      | r2_hidden(k5_setfam_1(u1_struct_0(sK8),X0),u1_pre_topc(sK8))
% 7.83/1.50      | ~ r1_tarski(X0,u1_pre_topc(sK8)) ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_519]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1818,plain,
% 7.83/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
% 7.83/1.50      | r2_hidden(k5_setfam_1(u1_struct_0(sK8),X0),u1_pre_topc(sK8)) = iProver_top
% 7.83/1.50      | r1_tarski(X0,u1_pre_topc(sK8)) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2760,plain,
% 7.83/1.50      ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) != iProver_top
% 7.83/1.50      | r2_hidden(k3_tarski(u1_pre_topc(sK8)),u1_pre_topc(sK8)) = iProver_top
% 7.83/1.50      | r1_tarski(u1_pre_topc(sK8),u1_pre_topc(sK8)) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_2756,c_1818]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2784,plain,
% 7.83/1.50      ( r2_hidden(k3_tarski(u1_pre_topc(sK8)),u1_pre_topc(sK8)) = iProver_top ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_2760,c_39,c_45,c_1948]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1839,plain,
% 7.83/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.83/1.50      | r2_hidden(X1,X2) != iProver_top
% 7.83/1.50      | r2_hidden(X0,k3_tarski(X2)) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3749,plain,
% 7.83/1.50      ( r2_hidden(u1_pre_topc(sK8),X0) != iProver_top
% 7.83/1.50      | r2_hidden(k3_tarski(u1_pre_topc(sK8)),k3_tarski(X0)) = iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_2784,c_1839]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4681,plain,
% 7.83/1.50      ( r2_hidden(u1_pre_topc(sK8),k1_zfmisc_1(X0)) != iProver_top
% 7.83/1.50      | r2_hidden(k3_tarski(u1_pre_topc(sK8)),X0) = iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_12,c_3749]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5164,plain,
% 7.83/1.50      ( r2_hidden(k3_tarski(u1_pre_topc(sK8)),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_4101,c_4681]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_15,plain,
% 7.83/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.83/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1834,plain,
% 7.83/1.50      ( m1_subset_1(X0,X1) = iProver_top
% 7.83/1.50      | r2_hidden(X0,X1) != iProver_top
% 7.83/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5290,plain,
% 7.83/1.50      ( m1_subset_1(k3_tarski(u1_pre_topc(sK8)),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
% 7.83/1.50      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_5164,c_1834]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_19,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.83/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1830,plain,
% 7.83/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.83/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_6682,plain,
% 7.83/1.50      ( r1_tarski(k3_tarski(u1_pre_topc(sK8)),u1_struct_0(sK8)) = iProver_top
% 7.83/1.50      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_5290,c_1830]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3,plain,
% 7.83/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.83/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1844,plain,
% 7.83/1.50      ( X0 = X1
% 7.83/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.83/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_6685,plain,
% 7.83/1.50      ( k3_tarski(u1_pre_topc(sK8)) = u1_struct_0(sK8)
% 7.83/1.50      | r1_tarski(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))) != iProver_top
% 7.83/1.50      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_6682,c_1844]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_6686,plain,
% 7.83/1.50      ( ~ r1_tarski(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8)))
% 7.83/1.50      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8)))
% 7.83/1.50      | k3_tarski(u1_pre_topc(sK8)) = u1_struct_0(sK8) ),
% 7.83/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_6685]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1,plain,
% 7.83/1.50      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.83/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2347,plain,
% 7.83/1.50      ( r2_hidden(sK1(u1_struct_0(sK8),X0),u1_struct_0(sK8))
% 7.83/1.50      | r1_tarski(u1_struct_0(sK8),X0) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_6246,plain,
% 7.83/1.50      ( r2_hidden(sK1(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))),u1_struct_0(sK8))
% 7.83/1.50      | r1_tarski(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_2347]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_34,plain,
% 7.83/1.50      ( ~ r2_hidden(k3_tarski(X0),X0)
% 7.83/1.50      | v1_xboole_0(X0)
% 7.83/1.50      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1823,plain,
% 7.83/1.50      ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
% 7.83/1.50      | r2_hidden(k3_tarski(X0),X0) != iProver_top
% 7.83/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2788,plain,
% 7.83/1.50      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) = k3_tarski(u1_pre_topc(sK8))
% 7.83/1.50      | v1_xboole_0(u1_pre_topc(sK8)) = iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_2784,c_1823]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2791,plain,
% 7.83/1.50      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) = k3_tarski(u1_pre_topc(sK8)) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_2788,c_38,c_39,c_48,c_1948,c_2196]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_35,negated_conjecture,
% 7.83/1.50      ( u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) ),
% 7.83/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2793,plain,
% 7.83/1.50      ( k3_tarski(u1_pre_topc(sK8)) != u1_struct_0(sK8) ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_2791,c_35]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2209,plain,
% 7.83/1.50      ( r1_tarski(u1_pre_topc(sK8),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1821,c_1830]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2210,plain,
% 7.83/1.50      ( r1_tarski(u1_pre_topc(sK8),k1_zfmisc_1(u1_struct_0(sK8))) ),
% 7.83/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2209]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_47,plain,
% 7.83/1.50      ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 7.83/1.50      | ~ l1_pre_topc(sK8)
% 7.83/1.50      | ~ v2_pre_topc(sK8) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_32]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(contradiction,plain,
% 7.83/1.50      ( $false ),
% 7.83/1.50      inference(minisat,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_30647,c_13567,c_7662,c_6686,c_6246,c_2793,c_2210,c_47,
% 7.83/1.50                 c_36,c_37]) ).
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.83/1.50  
% 7.83/1.50  ------                               Statistics
% 7.83/1.50  
% 7.83/1.50  ------ General
% 7.83/1.50  
% 7.83/1.50  abstr_ref_over_cycles:                  0
% 7.83/1.50  abstr_ref_under_cycles:                 0
% 7.83/1.50  gc_basic_clause_elim:                   0
% 7.83/1.50  forced_gc_time:                         0
% 7.83/1.50  parsing_time:                           0.017
% 7.83/1.50  unif_index_cands_time:                  0.
% 7.83/1.50  unif_index_add_time:                    0.
% 7.83/1.50  orderings_time:                         0.
% 7.83/1.50  out_proof_time:                         0.011
% 7.83/1.50  total_time:                             0.89
% 7.83/1.50  num_of_symbols:                         54
% 7.83/1.50  num_of_terms:                           19344
% 7.83/1.50  
% 7.83/1.50  ------ Preprocessing
% 7.83/1.50  
% 7.83/1.50  num_of_splits:                          0
% 7.83/1.50  num_of_split_atoms:                     0
% 7.83/1.50  num_of_reused_defs:                     0
% 7.83/1.50  num_eq_ax_congr_red:                    39
% 7.83/1.50  num_of_sem_filtered_clauses:            1
% 7.83/1.50  num_of_subtypes:                        0
% 7.83/1.50  monotx_restored_types:                  0
% 7.83/1.50  sat_num_of_epr_types:                   0
% 7.83/1.50  sat_num_of_non_cyclic_types:            0
% 7.83/1.50  sat_guarded_non_collapsed_types:        0
% 7.83/1.50  num_pure_diseq_elim:                    0
% 7.83/1.50  simp_replaced_by:                       0
% 7.83/1.50  res_preprocessed:                       162
% 7.83/1.50  prep_upred:                             0
% 7.83/1.50  prep_unflattend:                        19
% 7.83/1.50  smt_new_axioms:                         0
% 7.83/1.50  pred_elim_cands:                        5
% 7.83/1.50  pred_elim:                              2
% 7.83/1.50  pred_elim_cl:                           5
% 7.83/1.50  pred_elim_cycles:                       4
% 7.83/1.50  merged_defs:                            8
% 7.83/1.50  merged_defs_ncl:                        0
% 7.83/1.50  bin_hyper_res:                          9
% 7.83/1.50  prep_cycles:                            4
% 7.83/1.50  pred_elim_time:                         0.007
% 7.83/1.50  splitting_time:                         0.
% 7.83/1.50  sem_filter_time:                        0.
% 7.83/1.50  monotx_time:                            0.001
% 7.83/1.50  subtype_inf_time:                       0.
% 7.83/1.50  
% 7.83/1.50  ------ Problem properties
% 7.83/1.50  
% 7.83/1.50  clauses:                                32
% 7.83/1.50  conjectures:                            1
% 7.83/1.50  epr:                                    9
% 7.83/1.50  horn:                                   22
% 7.83/1.50  ground:                                 4
% 7.83/1.50  unary:                                  6
% 7.83/1.50  binary:                                 12
% 7.83/1.50  lits:                                   76
% 7.83/1.50  lits_eq:                                8
% 7.83/1.50  fd_pure:                                0
% 7.83/1.50  fd_pseudo:                              0
% 7.83/1.50  fd_cond:                                0
% 7.83/1.50  fd_pseudo_cond:                         4
% 7.83/1.50  ac_symbols:                             0
% 7.83/1.50  
% 7.83/1.50  ------ Propositional Solver
% 7.83/1.50  
% 7.83/1.50  prop_solver_calls:                      30
% 7.83/1.50  prop_fast_solver_calls:                 2513
% 7.83/1.50  smt_solver_calls:                       0
% 7.83/1.50  smt_fast_solver_calls:                  0
% 7.83/1.50  prop_num_of_clauses:                    13127
% 7.83/1.50  prop_preprocess_simplified:             25760
% 7.83/1.50  prop_fo_subsumed:                       132
% 7.83/1.50  prop_solver_time:                       0.
% 7.83/1.50  smt_solver_time:                        0.
% 7.83/1.50  smt_fast_solver_time:                   0.
% 7.83/1.50  prop_fast_solver_time:                  0.
% 7.83/1.50  prop_unsat_core_time:                   0.
% 7.83/1.50  
% 7.83/1.50  ------ QBF
% 7.83/1.50  
% 7.83/1.50  qbf_q_res:                              0
% 7.83/1.50  qbf_num_tautologies:                    0
% 7.83/1.50  qbf_prep_cycles:                        0
% 7.83/1.50  
% 7.83/1.50  ------ BMC1
% 7.83/1.50  
% 7.83/1.50  bmc1_current_bound:                     -1
% 7.83/1.50  bmc1_last_solved_bound:                 -1
% 7.83/1.50  bmc1_unsat_core_size:                   -1
% 7.83/1.50  bmc1_unsat_core_parents_size:           -1
% 7.83/1.50  bmc1_merge_next_fun:                    0
% 7.83/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.83/1.50  
% 7.83/1.50  ------ Instantiation
% 7.83/1.50  
% 7.83/1.50  inst_num_of_clauses:                    3115
% 7.83/1.50  inst_num_in_passive:                    1119
% 7.83/1.50  inst_num_in_active:                     1172
% 7.83/1.50  inst_num_in_unprocessed:                823
% 7.83/1.50  inst_num_of_loops:                      1771
% 7.83/1.50  inst_num_of_learning_restarts:          0
% 7.83/1.50  inst_num_moves_active_passive:          598
% 7.83/1.50  inst_lit_activity:                      0
% 7.83/1.50  inst_lit_activity_moves:                0
% 7.83/1.50  inst_num_tautologies:                   0
% 7.83/1.50  inst_num_prop_implied:                  0
% 7.83/1.50  inst_num_existing_simplified:           0
% 7.83/1.50  inst_num_eq_res_simplified:             0
% 7.83/1.50  inst_num_child_elim:                    0
% 7.83/1.50  inst_num_of_dismatching_blockings:      2222
% 7.83/1.50  inst_num_of_non_proper_insts:           4334
% 7.83/1.50  inst_num_of_duplicates:                 0
% 7.83/1.50  inst_inst_num_from_inst_to_res:         0
% 7.83/1.50  inst_dismatching_checking_time:         0.
% 7.83/1.50  
% 7.83/1.50  ------ Resolution
% 7.83/1.50  
% 7.83/1.50  res_num_of_clauses:                     0
% 7.83/1.50  res_num_in_passive:                     0
% 7.83/1.50  res_num_in_active:                      0
% 7.83/1.50  res_num_of_loops:                       166
% 7.83/1.50  res_forward_subset_subsumed:            186
% 7.83/1.50  res_backward_subset_subsumed:           0
% 7.83/1.50  res_forward_subsumed:                   0
% 7.83/1.50  res_backward_subsumed:                  0
% 7.83/1.50  res_forward_subsumption_resolution:     0
% 7.83/1.50  res_backward_subsumption_resolution:    0
% 7.83/1.50  res_clause_to_clause_subsumption:       8971
% 7.83/1.50  res_orphan_elimination:                 0
% 7.83/1.50  res_tautology_del:                      358
% 7.83/1.50  res_num_eq_res_simplified:              0
% 7.83/1.50  res_num_sel_changes:                    0
% 7.83/1.50  res_moves_from_active_to_pass:          0
% 7.83/1.50  
% 7.83/1.50  ------ Superposition
% 7.83/1.50  
% 7.83/1.50  sup_time_total:                         0.
% 7.83/1.50  sup_time_generating:                    0.
% 7.83/1.50  sup_time_sim_full:                      0.
% 7.83/1.50  sup_time_sim_immed:                     0.
% 7.83/1.50  
% 7.83/1.50  sup_num_of_clauses:                     977
% 7.83/1.50  sup_num_in_active:                      332
% 7.83/1.50  sup_num_in_passive:                     645
% 7.83/1.50  sup_num_of_loops:                       354
% 7.83/1.50  sup_fw_superposition:                   1022
% 7.83/1.50  sup_bw_superposition:                   657
% 7.83/1.50  sup_immediate_simplified:               576
% 7.83/1.50  sup_given_eliminated:                   1
% 7.83/1.50  comparisons_done:                       0
% 7.83/1.50  comparisons_avoided:                    4
% 7.83/1.50  
% 7.83/1.50  ------ Simplifications
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  sim_fw_subset_subsumed:                 240
% 7.83/1.50  sim_bw_subset_subsumed:                 53
% 7.83/1.50  sim_fw_subsumed:                        161
% 7.83/1.50  sim_bw_subsumed:                        73
% 7.83/1.50  sim_fw_subsumption_res:                 0
% 7.83/1.50  sim_bw_subsumption_res:                 0
% 7.83/1.50  sim_tautology_del:                      24
% 7.83/1.50  sim_eq_tautology_del:                   3
% 7.83/1.50  sim_eq_res_simp:                        0
% 7.83/1.50  sim_fw_demodulated:                     65
% 7.83/1.50  sim_bw_demodulated:                     1
% 7.83/1.50  sim_light_normalised:                   67
% 7.83/1.50  sim_joinable_taut:                      0
% 7.83/1.50  sim_joinable_simp:                      0
% 7.83/1.50  sim_ac_normalised:                      0
% 7.83/1.50  sim_smt_subsumption:                    0
% 7.83/1.50  
%------------------------------------------------------------------------------
