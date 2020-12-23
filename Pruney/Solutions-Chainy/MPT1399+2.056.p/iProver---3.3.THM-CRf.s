%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:42 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 466 expanded)
%              Number of clauses        :   67 (  92 expanded)
%              Number of leaves         :   28 ( 130 expanded)
%              Depth                    :   19
%              Number of atoms          :  466 (4066 expanded)
%              Number of equality atoms :  127 ( 448 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ v3_pre_topc(X3,X0) )
                & ( ( r2_hidden(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & v3_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = sK2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK2)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(sK1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f51,f50,f49])).

fof(f82,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f69,f88])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f89])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f90])).

fof(f92,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f91])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f92])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f93])).

fof(f95,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f53,f94])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f95])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f96,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = sK2 ),
    inference(definition_unfolding,[],[f54,f94,f88,f88])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f98,plain,(
    ! [X0] : k5_xboole_0(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f56,f88])).

fof(f17,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f70,f88])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f97,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(definition_unfolding,[],[f55,f88])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f78,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,(
    ! [X0] :
      ( sK2 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(definition_unfolding,[],[f57,f88])).

fof(f104,plain,(
    r1_xboole_0(sK2,sK2) ),
    inference(equality_resolution,[],[f100])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_656,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_338,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_14,c_13])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_387,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_338,c_24])).

cnf(c_388,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_674,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_656,c_388])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_660,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_662,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1029,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))) = k3_subset_1(X0,sK2) ),
    inference(superposition,[status(thm)],[c_660,c_662])).

cnf(c_0,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = sK2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2,negated_conjecture,
    ( k5_xboole_0(X0,sK2) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1034,plain,
    ( k3_subset_1(X0,sK2) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1029,c_0,c_2])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sK2 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_659,plain,
    ( sK2 = X0
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1079,plain,
    ( sK2 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_659])).

cnf(c_47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1082,plain,
    ( m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | sK2 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1079,c_47])).

cnf(c_1083,plain,
    ( sK2 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1082])).

cnf(c_1,negated_conjecture,
    ( r1_tarski(sK2,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_294,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_295,plain,
    ( ~ r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_655,plain,
    ( r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_1090,plain,
    ( sK2 = X0
    | r2_hidden(X1,X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1083,c_655])).

cnf(c_1093,plain,
    ( k2_struct_0(sK0) = sK2
    | r2_hidden(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_674,c_1090])).

cnf(c_18,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | r2_hidden(X0,sK2)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_318,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_295,c_18])).

cnf(c_16,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_372,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_373,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_375,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_24])).

cnf(c_393,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_318,c_375])).

cnf(c_394,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_17,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_361,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_362,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_396,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_24,c_362])).

cnf(c_654,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_685,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_654,c_388])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_661,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_661,c_6])).

cnf(c_688,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_685,c_679])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_303,plain,
    ( ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | X1 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_304,plain,
    ( ~ r1_xboole_0(sK2,X0)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_4,negated_conjecture,
    ( r1_xboole_0(sK2,sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_56,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_88,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ r1_tarski(sK2,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_308,plain,
    ( v1_xboole_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_4,c_56,c_88])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_281,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_282,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_326,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_308,c_282])).

cnf(c_349,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(sK0) != sK2
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_326])).

cnf(c_350,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) != sK2 ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_352,plain,
    ( u1_struct_0(sK0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_24])).

cnf(c_667,plain,
    ( k2_struct_0(sK0) != sK2 ),
    inference(light_normalisation,[status(thm)],[c_352,c_388])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1093,c_688,c_667])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:41:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.89/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.03  
% 1.89/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.89/1.03  
% 1.89/1.03  ------  iProver source info
% 1.89/1.03  
% 1.89/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.89/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.89/1.03  git: non_committed_changes: false
% 1.89/1.03  git: last_make_outside_of_git: false
% 1.89/1.03  
% 1.89/1.03  ------ 
% 1.89/1.03  
% 1.89/1.03  ------ Input Options
% 1.89/1.03  
% 1.89/1.03  --out_options                           all
% 1.89/1.03  --tptp_safe_out                         true
% 1.89/1.03  --problem_path                          ""
% 1.89/1.03  --include_path                          ""
% 1.89/1.03  --clausifier                            res/vclausify_rel
% 1.89/1.03  --clausifier_options                    --mode clausify
% 1.89/1.03  --stdin                                 false
% 1.89/1.03  --stats_out                             all
% 1.89/1.03  
% 1.89/1.03  ------ General Options
% 1.89/1.03  
% 1.89/1.03  --fof                                   false
% 1.89/1.03  --time_out_real                         305.
% 1.89/1.03  --time_out_virtual                      -1.
% 1.89/1.03  --symbol_type_check                     false
% 1.89/1.03  --clausify_out                          false
% 1.89/1.03  --sig_cnt_out                           false
% 1.89/1.03  --trig_cnt_out                          false
% 1.89/1.03  --trig_cnt_out_tolerance                1.
% 1.89/1.03  --trig_cnt_out_sk_spl                   false
% 1.89/1.03  --abstr_cl_out                          false
% 1.89/1.03  
% 1.89/1.03  ------ Global Options
% 1.89/1.03  
% 1.89/1.03  --schedule                              default
% 1.89/1.03  --add_important_lit                     false
% 1.89/1.03  --prop_solver_per_cl                    1000
% 1.89/1.03  --min_unsat_core                        false
% 1.89/1.03  --soft_assumptions                      false
% 1.89/1.03  --soft_lemma_size                       3
% 1.89/1.03  --prop_impl_unit_size                   0
% 1.89/1.03  --prop_impl_unit                        []
% 1.89/1.03  --share_sel_clauses                     true
% 1.89/1.03  --reset_solvers                         false
% 1.89/1.03  --bc_imp_inh                            [conj_cone]
% 1.89/1.03  --conj_cone_tolerance                   3.
% 1.89/1.03  --extra_neg_conj                        none
% 1.89/1.03  --large_theory_mode                     true
% 1.89/1.03  --prolific_symb_bound                   200
% 1.89/1.03  --lt_threshold                          2000
% 1.89/1.03  --clause_weak_htbl                      true
% 1.89/1.03  --gc_record_bc_elim                     false
% 1.89/1.03  
% 1.89/1.03  ------ Preprocessing Options
% 1.89/1.03  
% 1.89/1.03  --preprocessing_flag                    true
% 1.89/1.03  --time_out_prep_mult                    0.1
% 1.89/1.03  --splitting_mode                        input
% 1.89/1.03  --splitting_grd                         true
% 1.89/1.03  --splitting_cvd                         false
% 1.89/1.03  --splitting_cvd_svl                     false
% 1.89/1.03  --splitting_nvd                         32
% 1.89/1.03  --sub_typing                            true
% 1.89/1.03  --prep_gs_sim                           true
% 1.89/1.03  --prep_unflatten                        true
% 1.89/1.03  --prep_res_sim                          true
% 1.89/1.03  --prep_upred                            true
% 1.89/1.03  --prep_sem_filter                       exhaustive
% 1.89/1.03  --prep_sem_filter_out                   false
% 1.89/1.03  --pred_elim                             true
% 1.89/1.03  --res_sim_input                         true
% 1.89/1.03  --eq_ax_congr_red                       true
% 1.89/1.03  --pure_diseq_elim                       true
% 1.89/1.03  --brand_transform                       false
% 1.89/1.03  --non_eq_to_eq                          false
% 1.89/1.03  --prep_def_merge                        true
% 1.89/1.03  --prep_def_merge_prop_impl              false
% 1.89/1.03  --prep_def_merge_mbd                    true
% 1.89/1.03  --prep_def_merge_tr_red                 false
% 1.89/1.03  --prep_def_merge_tr_cl                  false
% 1.89/1.03  --smt_preprocessing                     true
% 1.89/1.03  --smt_ac_axioms                         fast
% 1.89/1.03  --preprocessed_out                      false
% 1.89/1.03  --preprocessed_stats                    false
% 1.89/1.03  
% 1.89/1.03  ------ Abstraction refinement Options
% 1.89/1.03  
% 1.89/1.03  --abstr_ref                             []
% 1.89/1.03  --abstr_ref_prep                        false
% 1.89/1.03  --abstr_ref_until_sat                   false
% 1.89/1.03  --abstr_ref_sig_restrict                funpre
% 1.89/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/1.03  --abstr_ref_under                       []
% 1.89/1.03  
% 1.89/1.03  ------ SAT Options
% 1.89/1.03  
% 1.89/1.03  --sat_mode                              false
% 1.89/1.03  --sat_fm_restart_options                ""
% 1.89/1.03  --sat_gr_def                            false
% 1.89/1.03  --sat_epr_types                         true
% 1.89/1.03  --sat_non_cyclic_types                  false
% 1.89/1.03  --sat_finite_models                     false
% 1.89/1.03  --sat_fm_lemmas                         false
% 1.89/1.03  --sat_fm_prep                           false
% 1.89/1.03  --sat_fm_uc_incr                        true
% 1.89/1.03  --sat_out_model                         small
% 1.89/1.03  --sat_out_clauses                       false
% 1.89/1.03  
% 1.89/1.03  ------ QBF Options
% 1.89/1.03  
% 1.89/1.03  --qbf_mode                              false
% 1.89/1.03  --qbf_elim_univ                         false
% 1.89/1.03  --qbf_dom_inst                          none
% 1.89/1.03  --qbf_dom_pre_inst                      false
% 1.89/1.03  --qbf_sk_in                             false
% 1.89/1.03  --qbf_pred_elim                         true
% 1.89/1.03  --qbf_split                             512
% 1.89/1.03  
% 1.89/1.03  ------ BMC1 Options
% 1.89/1.03  
% 1.89/1.03  --bmc1_incremental                      false
% 1.89/1.03  --bmc1_axioms                           reachable_all
% 1.89/1.03  --bmc1_min_bound                        0
% 1.89/1.03  --bmc1_max_bound                        -1
% 1.89/1.03  --bmc1_max_bound_default                -1
% 1.89/1.03  --bmc1_symbol_reachability              true
% 1.89/1.03  --bmc1_property_lemmas                  false
% 1.89/1.03  --bmc1_k_induction                      false
% 1.89/1.03  --bmc1_non_equiv_states                 false
% 1.89/1.03  --bmc1_deadlock                         false
% 1.89/1.03  --bmc1_ucm                              false
% 1.89/1.03  --bmc1_add_unsat_core                   none
% 1.89/1.03  --bmc1_unsat_core_children              false
% 1.89/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/1.03  --bmc1_out_stat                         full
% 1.89/1.03  --bmc1_ground_init                      false
% 1.89/1.03  --bmc1_pre_inst_next_state              false
% 1.89/1.03  --bmc1_pre_inst_state                   false
% 1.89/1.03  --bmc1_pre_inst_reach_state             false
% 1.89/1.03  --bmc1_out_unsat_core                   false
% 1.89/1.03  --bmc1_aig_witness_out                  false
% 1.89/1.03  --bmc1_verbose                          false
% 1.89/1.03  --bmc1_dump_clauses_tptp                false
% 1.89/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.89/1.03  --bmc1_dump_file                        -
% 1.89/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.89/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.89/1.03  --bmc1_ucm_extend_mode                  1
% 1.89/1.03  --bmc1_ucm_init_mode                    2
% 1.89/1.03  --bmc1_ucm_cone_mode                    none
% 1.89/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.89/1.03  --bmc1_ucm_relax_model                  4
% 1.89/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.89/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/1.03  --bmc1_ucm_layered_model                none
% 1.89/1.03  --bmc1_ucm_max_lemma_size               10
% 1.89/1.03  
% 1.89/1.03  ------ AIG Options
% 1.89/1.03  
% 1.89/1.03  --aig_mode                              false
% 1.89/1.03  
% 1.89/1.03  ------ Instantiation Options
% 1.89/1.03  
% 1.89/1.03  --instantiation_flag                    true
% 1.89/1.03  --inst_sos_flag                         false
% 1.89/1.03  --inst_sos_phase                        true
% 1.89/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/1.03  --inst_lit_sel_side                     num_symb
% 1.89/1.03  --inst_solver_per_active                1400
% 1.89/1.03  --inst_solver_calls_frac                1.
% 1.89/1.03  --inst_passive_queue_type               priority_queues
% 1.89/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/1.03  --inst_passive_queues_freq              [25;2]
% 1.89/1.03  --inst_dismatching                      true
% 1.89/1.03  --inst_eager_unprocessed_to_passive     true
% 1.89/1.03  --inst_prop_sim_given                   true
% 1.89/1.03  --inst_prop_sim_new                     false
% 1.89/1.03  --inst_subs_new                         false
% 1.89/1.03  --inst_eq_res_simp                      false
% 1.89/1.03  --inst_subs_given                       false
% 1.89/1.03  --inst_orphan_elimination               true
% 1.89/1.03  --inst_learning_loop_flag               true
% 1.89/1.03  --inst_learning_start                   3000
% 1.89/1.03  --inst_learning_factor                  2
% 1.89/1.03  --inst_start_prop_sim_after_learn       3
% 1.89/1.03  --inst_sel_renew                        solver
% 1.89/1.03  --inst_lit_activity_flag                true
% 1.89/1.03  --inst_restr_to_given                   false
% 1.89/1.03  --inst_activity_threshold               500
% 1.89/1.03  --inst_out_proof                        true
% 1.89/1.03  
% 1.89/1.03  ------ Resolution Options
% 1.89/1.03  
% 1.89/1.03  --resolution_flag                       true
% 1.89/1.03  --res_lit_sel                           adaptive
% 1.89/1.03  --res_lit_sel_side                      none
% 1.89/1.03  --res_ordering                          kbo
% 1.89/1.03  --res_to_prop_solver                    active
% 1.89/1.03  --res_prop_simpl_new                    false
% 1.89/1.03  --res_prop_simpl_given                  true
% 1.89/1.03  --res_passive_queue_type                priority_queues
% 1.89/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/1.03  --res_passive_queues_freq               [15;5]
% 1.89/1.03  --res_forward_subs                      full
% 1.89/1.03  --res_backward_subs                     full
% 1.89/1.03  --res_forward_subs_resolution           true
% 1.89/1.03  --res_backward_subs_resolution          true
% 1.89/1.03  --res_orphan_elimination                true
% 1.89/1.03  --res_time_limit                        2.
% 1.89/1.03  --res_out_proof                         true
% 1.89/1.03  
% 1.89/1.03  ------ Superposition Options
% 1.89/1.03  
% 1.89/1.03  --superposition_flag                    true
% 1.89/1.03  --sup_passive_queue_type                priority_queues
% 1.89/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.89/1.03  --demod_completeness_check              fast
% 1.89/1.03  --demod_use_ground                      true
% 1.89/1.03  --sup_to_prop_solver                    passive
% 1.89/1.03  --sup_prop_simpl_new                    true
% 1.89/1.03  --sup_prop_simpl_given                  true
% 1.89/1.03  --sup_fun_splitting                     false
% 1.89/1.03  --sup_smt_interval                      50000
% 1.89/1.03  
% 1.89/1.03  ------ Superposition Simplification Setup
% 1.89/1.03  
% 1.89/1.03  --sup_indices_passive                   []
% 1.89/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.03  --sup_full_bw                           [BwDemod]
% 1.89/1.03  --sup_immed_triv                        [TrivRules]
% 1.89/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.03  --sup_immed_bw_main                     []
% 1.89/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.03  
% 1.89/1.03  ------ Combination Options
% 1.89/1.03  
% 1.89/1.03  --comb_res_mult                         3
% 1.89/1.03  --comb_sup_mult                         2
% 1.89/1.03  --comb_inst_mult                        10
% 1.89/1.03  
% 1.89/1.03  ------ Debug Options
% 1.89/1.03  
% 1.89/1.03  --dbg_backtrace                         false
% 1.89/1.03  --dbg_dump_prop_clauses                 false
% 1.89/1.03  --dbg_dump_prop_clauses_file            -
% 1.89/1.03  --dbg_out_stat                          false
% 1.89/1.03  ------ Parsing...
% 1.89/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.89/1.03  
% 1.89/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.89/1.03  
% 1.89/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.89/1.03  
% 1.89/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.89/1.03  ------ Proving...
% 1.89/1.03  ------ Problem Properties 
% 1.89/1.03  
% 1.89/1.03  
% 1.89/1.03  clauses                                 14
% 1.89/1.03  conjectures                             6
% 1.89/1.03  EPR                                     1
% 1.89/1.03  Horn                                    13
% 1.89/1.03  unary                                   10
% 1.89/1.03  binary                                  2
% 1.89/1.03  lits                                    22
% 1.89/1.03  lits eq                                 7
% 1.89/1.03  fd_pure                                 0
% 1.89/1.03  fd_pseudo                               0
% 1.89/1.03  fd_cond                                 1
% 1.89/1.03  fd_pseudo_cond                          0
% 1.89/1.03  AC symbols                              0
% 1.89/1.03  
% 1.89/1.03  ------ Schedule dynamic 5 is on 
% 1.89/1.03  
% 1.89/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.89/1.03  
% 1.89/1.03  
% 1.89/1.03  ------ 
% 1.89/1.03  Current options:
% 1.89/1.03  ------ 
% 1.89/1.03  
% 1.89/1.03  ------ Input Options
% 1.89/1.03  
% 1.89/1.03  --out_options                           all
% 1.89/1.03  --tptp_safe_out                         true
% 1.89/1.03  --problem_path                          ""
% 1.89/1.03  --include_path                          ""
% 1.89/1.03  --clausifier                            res/vclausify_rel
% 1.89/1.03  --clausifier_options                    --mode clausify
% 1.89/1.03  --stdin                                 false
% 1.89/1.03  --stats_out                             all
% 1.89/1.03  
% 1.89/1.03  ------ General Options
% 1.89/1.03  
% 1.89/1.03  --fof                                   false
% 1.89/1.03  --time_out_real                         305.
% 1.89/1.03  --time_out_virtual                      -1.
% 1.89/1.03  --symbol_type_check                     false
% 1.89/1.03  --clausify_out                          false
% 1.89/1.03  --sig_cnt_out                           false
% 1.89/1.03  --trig_cnt_out                          false
% 1.89/1.03  --trig_cnt_out_tolerance                1.
% 1.89/1.03  --trig_cnt_out_sk_spl                   false
% 1.89/1.03  --abstr_cl_out                          false
% 1.89/1.03  
% 1.89/1.03  ------ Global Options
% 1.89/1.03  
% 1.89/1.03  --schedule                              default
% 1.89/1.03  --add_important_lit                     false
% 1.89/1.03  --prop_solver_per_cl                    1000
% 1.89/1.03  --min_unsat_core                        false
% 1.89/1.03  --soft_assumptions                      false
% 1.89/1.03  --soft_lemma_size                       3
% 1.89/1.03  --prop_impl_unit_size                   0
% 1.89/1.03  --prop_impl_unit                        []
% 1.89/1.03  --share_sel_clauses                     true
% 1.89/1.03  --reset_solvers                         false
% 1.89/1.03  --bc_imp_inh                            [conj_cone]
% 1.89/1.03  --conj_cone_tolerance                   3.
% 1.89/1.03  --extra_neg_conj                        none
% 1.89/1.03  --large_theory_mode                     true
% 1.89/1.03  --prolific_symb_bound                   200
% 1.89/1.03  --lt_threshold                          2000
% 1.89/1.03  --clause_weak_htbl                      true
% 1.89/1.03  --gc_record_bc_elim                     false
% 1.89/1.03  
% 1.89/1.03  ------ Preprocessing Options
% 1.89/1.03  
% 1.89/1.03  --preprocessing_flag                    true
% 1.89/1.03  --time_out_prep_mult                    0.1
% 1.89/1.03  --splitting_mode                        input
% 1.89/1.03  --splitting_grd                         true
% 1.89/1.03  --splitting_cvd                         false
% 1.89/1.03  --splitting_cvd_svl                     false
% 1.89/1.03  --splitting_nvd                         32
% 1.89/1.03  --sub_typing                            true
% 1.89/1.03  --prep_gs_sim                           true
% 1.89/1.03  --prep_unflatten                        true
% 1.89/1.03  --prep_res_sim                          true
% 1.89/1.03  --prep_upred                            true
% 1.89/1.03  --prep_sem_filter                       exhaustive
% 1.89/1.03  --prep_sem_filter_out                   false
% 1.89/1.03  --pred_elim                             true
% 1.89/1.03  --res_sim_input                         true
% 1.89/1.03  --eq_ax_congr_red                       true
% 1.89/1.03  --pure_diseq_elim                       true
% 1.89/1.03  --brand_transform                       false
% 1.89/1.03  --non_eq_to_eq                          false
% 1.89/1.03  --prep_def_merge                        true
% 1.89/1.03  --prep_def_merge_prop_impl              false
% 1.89/1.03  --prep_def_merge_mbd                    true
% 1.89/1.03  --prep_def_merge_tr_red                 false
% 1.89/1.03  --prep_def_merge_tr_cl                  false
% 1.89/1.03  --smt_preprocessing                     true
% 1.89/1.03  --smt_ac_axioms                         fast
% 1.89/1.03  --preprocessed_out                      false
% 1.89/1.03  --preprocessed_stats                    false
% 1.89/1.03  
% 1.89/1.03  ------ Abstraction refinement Options
% 1.89/1.03  
% 1.89/1.03  --abstr_ref                             []
% 1.89/1.03  --abstr_ref_prep                        false
% 1.89/1.03  --abstr_ref_until_sat                   false
% 1.89/1.03  --abstr_ref_sig_restrict                funpre
% 1.89/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/1.03  --abstr_ref_under                       []
% 1.89/1.03  
% 1.89/1.03  ------ SAT Options
% 1.89/1.03  
% 1.89/1.03  --sat_mode                              false
% 1.89/1.03  --sat_fm_restart_options                ""
% 1.89/1.03  --sat_gr_def                            false
% 1.89/1.03  --sat_epr_types                         true
% 1.89/1.03  --sat_non_cyclic_types                  false
% 1.89/1.03  --sat_finite_models                     false
% 1.89/1.03  --sat_fm_lemmas                         false
% 1.89/1.03  --sat_fm_prep                           false
% 1.89/1.03  --sat_fm_uc_incr                        true
% 1.89/1.03  --sat_out_model                         small
% 1.89/1.03  --sat_out_clauses                       false
% 1.89/1.03  
% 1.89/1.03  ------ QBF Options
% 1.89/1.03  
% 1.89/1.03  --qbf_mode                              false
% 1.89/1.03  --qbf_elim_univ                         false
% 1.89/1.03  --qbf_dom_inst                          none
% 1.89/1.03  --qbf_dom_pre_inst                      false
% 1.89/1.03  --qbf_sk_in                             false
% 1.89/1.03  --qbf_pred_elim                         true
% 1.89/1.03  --qbf_split                             512
% 1.89/1.03  
% 1.89/1.03  ------ BMC1 Options
% 1.89/1.03  
% 1.89/1.03  --bmc1_incremental                      false
% 1.89/1.03  --bmc1_axioms                           reachable_all
% 1.89/1.03  --bmc1_min_bound                        0
% 1.89/1.03  --bmc1_max_bound                        -1
% 1.89/1.03  --bmc1_max_bound_default                -1
% 1.89/1.03  --bmc1_symbol_reachability              true
% 1.89/1.03  --bmc1_property_lemmas                  false
% 1.89/1.03  --bmc1_k_induction                      false
% 1.89/1.03  --bmc1_non_equiv_states                 false
% 1.89/1.03  --bmc1_deadlock                         false
% 1.89/1.03  --bmc1_ucm                              false
% 1.89/1.03  --bmc1_add_unsat_core                   none
% 1.89/1.03  --bmc1_unsat_core_children              false
% 1.89/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/1.03  --bmc1_out_stat                         full
% 1.89/1.03  --bmc1_ground_init                      false
% 1.89/1.03  --bmc1_pre_inst_next_state              false
% 1.89/1.03  --bmc1_pre_inst_state                   false
% 1.89/1.03  --bmc1_pre_inst_reach_state             false
% 1.89/1.03  --bmc1_out_unsat_core                   false
% 1.89/1.03  --bmc1_aig_witness_out                  false
% 1.89/1.03  --bmc1_verbose                          false
% 1.89/1.03  --bmc1_dump_clauses_tptp                false
% 1.89/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.89/1.03  --bmc1_dump_file                        -
% 1.89/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.89/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.89/1.03  --bmc1_ucm_extend_mode                  1
% 1.89/1.03  --bmc1_ucm_init_mode                    2
% 1.89/1.03  --bmc1_ucm_cone_mode                    none
% 1.89/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.89/1.03  --bmc1_ucm_relax_model                  4
% 1.89/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.89/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/1.03  --bmc1_ucm_layered_model                none
% 1.89/1.03  --bmc1_ucm_max_lemma_size               10
% 1.89/1.03  
% 1.89/1.03  ------ AIG Options
% 1.89/1.03  
% 1.89/1.03  --aig_mode                              false
% 1.89/1.03  
% 1.89/1.03  ------ Instantiation Options
% 1.89/1.03  
% 1.89/1.03  --instantiation_flag                    true
% 1.89/1.03  --inst_sos_flag                         false
% 1.89/1.03  --inst_sos_phase                        true
% 1.89/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/1.03  --inst_lit_sel_side                     none
% 1.89/1.03  --inst_solver_per_active                1400
% 1.89/1.03  --inst_solver_calls_frac                1.
% 1.89/1.03  --inst_passive_queue_type               priority_queues
% 1.89/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/1.03  --inst_passive_queues_freq              [25;2]
% 1.89/1.03  --inst_dismatching                      true
% 1.89/1.03  --inst_eager_unprocessed_to_passive     true
% 1.89/1.03  --inst_prop_sim_given                   true
% 1.89/1.03  --inst_prop_sim_new                     false
% 1.89/1.03  --inst_subs_new                         false
% 1.89/1.03  --inst_eq_res_simp                      false
% 1.89/1.03  --inst_subs_given                       false
% 1.89/1.03  --inst_orphan_elimination               true
% 1.89/1.03  --inst_learning_loop_flag               true
% 1.89/1.03  --inst_learning_start                   3000
% 1.89/1.03  --inst_learning_factor                  2
% 1.89/1.03  --inst_start_prop_sim_after_learn       3
% 1.89/1.03  --inst_sel_renew                        solver
% 1.89/1.03  --inst_lit_activity_flag                true
% 1.89/1.03  --inst_restr_to_given                   false
% 1.89/1.03  --inst_activity_threshold               500
% 1.89/1.03  --inst_out_proof                        true
% 1.89/1.03  
% 1.89/1.03  ------ Resolution Options
% 1.89/1.03  
% 1.89/1.03  --resolution_flag                       false
% 1.89/1.03  --res_lit_sel                           adaptive
% 1.89/1.03  --res_lit_sel_side                      none
% 1.89/1.03  --res_ordering                          kbo
% 1.89/1.03  --res_to_prop_solver                    active
% 1.89/1.03  --res_prop_simpl_new                    false
% 1.89/1.03  --res_prop_simpl_given                  true
% 1.89/1.03  --res_passive_queue_type                priority_queues
% 1.89/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/1.03  --res_passive_queues_freq               [15;5]
% 1.89/1.03  --res_forward_subs                      full
% 1.89/1.03  --res_backward_subs                     full
% 1.89/1.03  --res_forward_subs_resolution           true
% 1.89/1.03  --res_backward_subs_resolution          true
% 1.89/1.03  --res_orphan_elimination                true
% 1.89/1.03  --res_time_limit                        2.
% 1.89/1.03  --res_out_proof                         true
% 1.89/1.03  
% 1.89/1.03  ------ Superposition Options
% 1.89/1.03  
% 1.89/1.03  --superposition_flag                    true
% 1.89/1.03  --sup_passive_queue_type                priority_queues
% 1.89/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.89/1.03  --demod_completeness_check              fast
% 1.89/1.03  --demod_use_ground                      true
% 1.89/1.03  --sup_to_prop_solver                    passive
% 1.89/1.03  --sup_prop_simpl_new                    true
% 1.89/1.03  --sup_prop_simpl_given                  true
% 1.89/1.03  --sup_fun_splitting                     false
% 1.89/1.03  --sup_smt_interval                      50000
% 1.89/1.03  
% 1.89/1.03  ------ Superposition Simplification Setup
% 1.89/1.03  
% 1.89/1.03  --sup_indices_passive                   []
% 1.89/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.03  --sup_full_bw                           [BwDemod]
% 1.89/1.03  --sup_immed_triv                        [TrivRules]
% 1.89/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.03  --sup_immed_bw_main                     []
% 1.89/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/1.03  
% 1.89/1.03  ------ Combination Options
% 1.89/1.03  
% 1.89/1.03  --comb_res_mult                         3
% 1.89/1.03  --comb_sup_mult                         2
% 1.89/1.03  --comb_inst_mult                        10
% 1.89/1.03  
% 1.89/1.03  ------ Debug Options
% 1.89/1.03  
% 1.89/1.03  --dbg_backtrace                         false
% 1.89/1.03  --dbg_dump_prop_clauses                 false
% 1.89/1.03  --dbg_dump_prop_clauses_file            -
% 1.89/1.03  --dbg_out_stat                          false
% 1.89/1.03  
% 1.89/1.03  
% 1.89/1.03  
% 1.89/1.03  
% 1.89/1.03  ------ Proving...
% 1.89/1.03  
% 1.89/1.03  
% 1.89/1.03  % SZS status Theorem for theBenchmark.p
% 1.89/1.03  
% 1.89/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.89/1.03  
% 1.89/1.03  fof(f26,conjecture,(
% 1.89/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f27,negated_conjecture,(
% 1.89/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.89/1.03    inference(negated_conjecture,[],[f26])).
% 1.89/1.03  
% 1.89/1.03  fof(f45,plain,(
% 1.89/1.03    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.89/1.03    inference(ennf_transformation,[],[f27])).
% 1.89/1.03  
% 1.89/1.03  fof(f46,plain,(
% 1.89/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.89/1.03    inference(flattening,[],[f45])).
% 1.89/1.03  
% 1.89/1.03  fof(f47,plain,(
% 1.89/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.89/1.03    inference(nnf_transformation,[],[f46])).
% 1.89/1.03  
% 1.89/1.03  fof(f48,plain,(
% 1.89/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.89/1.03    inference(flattening,[],[f47])).
% 1.89/1.03  
% 1.89/1.03  fof(f51,plain,(
% 1.89/1.03    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.89/1.03    introduced(choice_axiom,[])).
% 1.89/1.03  
% 1.89/1.03  fof(f50,plain,(
% 1.89/1.03    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 1.89/1.03    introduced(choice_axiom,[])).
% 1.89/1.03  
% 1.89/1.03  fof(f49,plain,(
% 1.89/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.89/1.03    introduced(choice_axiom,[])).
% 1.89/1.03  
% 1.89/1.03  fof(f52,plain,(
% 1.89/1.03    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.89/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f51,f50,f49])).
% 1.89/1.03  
% 1.89/1.03  fof(f82,plain,(
% 1.89/1.03    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.89/1.03    inference(cnf_transformation,[],[f52])).
% 1.89/1.03  
% 1.89/1.03  fof(f22,axiom,(
% 1.89/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f38,plain,(
% 1.89/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.89/1.03    inference(ennf_transformation,[],[f22])).
% 1.89/1.03  
% 1.89/1.03  fof(f75,plain,(
% 1.89/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f38])).
% 1.89/1.03  
% 1.89/1.03  fof(f21,axiom,(
% 1.89/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f37,plain,(
% 1.89/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.89/1.03    inference(ennf_transformation,[],[f21])).
% 1.89/1.03  
% 1.89/1.03  fof(f74,plain,(
% 1.89/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f37])).
% 1.89/1.03  
% 1.89/1.03  fof(f81,plain,(
% 1.89/1.03    l1_pre_topc(sK0)),
% 1.89/1.03    inference(cnf_transformation,[],[f52])).
% 1.89/1.03  
% 1.89/1.03  fof(f16,axiom,(
% 1.89/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f69,plain,(
% 1.89/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.89/1.03    inference(cnf_transformation,[],[f16])).
% 1.89/1.03  
% 1.89/1.03  fof(f88,plain,(
% 1.89/1.03    k1_xboole_0 = sK2),
% 1.89/1.03    inference(cnf_transformation,[],[f52])).
% 1.89/1.03  
% 1.89/1.03  fof(f102,plain,(
% 1.89/1.03    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 1.89/1.03    inference(definition_unfolding,[],[f69,f88])).
% 1.89/1.03  
% 1.89/1.03  fof(f14,axiom,(
% 1.89/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f31,plain,(
% 1.89/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/1.03    inference(ennf_transformation,[],[f14])).
% 1.89/1.03  
% 1.89/1.03  fof(f67,plain,(
% 1.89/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/1.03    inference(cnf_transformation,[],[f31])).
% 1.89/1.03  
% 1.89/1.03  fof(f1,axiom,(
% 1.89/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f53,plain,(
% 1.89/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.89/1.03    inference(cnf_transformation,[],[f1])).
% 1.89/1.03  
% 1.89/1.03  fof(f18,axiom,(
% 1.89/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f71,plain,(
% 1.89/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.89/1.03    inference(cnf_transformation,[],[f18])).
% 1.89/1.03  
% 1.89/1.03  fof(f7,axiom,(
% 1.89/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f60,plain,(
% 1.89/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f7])).
% 1.89/1.03  
% 1.89/1.03  fof(f8,axiom,(
% 1.89/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f61,plain,(
% 1.89/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f8])).
% 1.89/1.03  
% 1.89/1.03  fof(f9,axiom,(
% 1.89/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f62,plain,(
% 1.89/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f9])).
% 1.89/1.03  
% 1.89/1.03  fof(f10,axiom,(
% 1.89/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f63,plain,(
% 1.89/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f10])).
% 1.89/1.03  
% 1.89/1.03  fof(f11,axiom,(
% 1.89/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f64,plain,(
% 1.89/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f11])).
% 1.89/1.03  
% 1.89/1.03  fof(f12,axiom,(
% 1.89/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f65,plain,(
% 1.89/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f12])).
% 1.89/1.03  
% 1.89/1.03  fof(f89,plain,(
% 1.89/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.89/1.03    inference(definition_unfolding,[],[f64,f65])).
% 1.89/1.03  
% 1.89/1.03  fof(f90,plain,(
% 1.89/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.89/1.03    inference(definition_unfolding,[],[f63,f89])).
% 1.89/1.03  
% 1.89/1.03  fof(f91,plain,(
% 1.89/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.89/1.03    inference(definition_unfolding,[],[f62,f90])).
% 1.89/1.03  
% 1.89/1.03  fof(f92,plain,(
% 1.89/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.89/1.03    inference(definition_unfolding,[],[f61,f91])).
% 1.89/1.03  
% 1.89/1.03  fof(f93,plain,(
% 1.89/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.89/1.03    inference(definition_unfolding,[],[f60,f92])).
% 1.89/1.03  
% 1.89/1.03  fof(f94,plain,(
% 1.89/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.89/1.03    inference(definition_unfolding,[],[f71,f93])).
% 1.89/1.03  
% 1.89/1.03  fof(f95,plain,(
% 1.89/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.89/1.03    inference(definition_unfolding,[],[f53,f94])).
% 1.89/1.03  
% 1.89/1.03  fof(f101,plain,(
% 1.89/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/1.03    inference(definition_unfolding,[],[f67,f95])).
% 1.89/1.03  
% 1.89/1.03  fof(f2,axiom,(
% 1.89/1.03    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f54,plain,(
% 1.89/1.03    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.89/1.03    inference(cnf_transformation,[],[f2])).
% 1.89/1.03  
% 1.89/1.03  fof(f96,plain,(
% 1.89/1.03    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = sK2) )),
% 1.89/1.03    inference(definition_unfolding,[],[f54,f94,f88,f88])).
% 1.89/1.03  
% 1.89/1.03  fof(f4,axiom,(
% 1.89/1.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f56,plain,(
% 1.89/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.89/1.03    inference(cnf_transformation,[],[f4])).
% 1.89/1.03  
% 1.89/1.03  fof(f98,plain,(
% 1.89/1.03    ( ! [X0] : (k5_xboole_0(X0,sK2) = X0) )),
% 1.89/1.03    inference(definition_unfolding,[],[f56,f88])).
% 1.89/1.03  
% 1.89/1.03  fof(f17,axiom,(
% 1.89/1.03    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f32,plain,(
% 1.89/1.03    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.89/1.03    inference(ennf_transformation,[],[f17])).
% 1.89/1.03  
% 1.89/1.03  fof(f33,plain,(
% 1.89/1.03    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.89/1.03    inference(flattening,[],[f32])).
% 1.89/1.03  
% 1.89/1.03  fof(f70,plain,(
% 1.89/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 1.89/1.03    inference(cnf_transformation,[],[f33])).
% 1.89/1.03  
% 1.89/1.03  fof(f103,plain,(
% 1.89/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK2 = X0) )),
% 1.89/1.03    inference(definition_unfolding,[],[f70,f88])).
% 1.89/1.03  
% 1.89/1.03  fof(f3,axiom,(
% 1.89/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f55,plain,(
% 1.89/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f3])).
% 1.89/1.03  
% 1.89/1.03  fof(f97,plain,(
% 1.89/1.03    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 1.89/1.03    inference(definition_unfolding,[],[f55,f88])).
% 1.89/1.03  
% 1.89/1.03  fof(f20,axiom,(
% 1.89/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f36,plain,(
% 1.89/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.89/1.03    inference(ennf_transformation,[],[f20])).
% 1.89/1.03  
% 1.89/1.03  fof(f73,plain,(
% 1.89/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f36])).
% 1.89/1.03  
% 1.89/1.03  fof(f87,plain,(
% 1.89/1.03    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.89/1.03    inference(cnf_transformation,[],[f52])).
% 1.89/1.03  
% 1.89/1.03  fof(f24,axiom,(
% 1.89/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f41,plain,(
% 1.89/1.03    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.89/1.03    inference(ennf_transformation,[],[f24])).
% 1.89/1.03  
% 1.89/1.03  fof(f42,plain,(
% 1.89/1.03    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/1.03    inference(flattening,[],[f41])).
% 1.89/1.03  
% 1.89/1.03  fof(f77,plain,(
% 1.89/1.03    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f42])).
% 1.89/1.03  
% 1.89/1.03  fof(f80,plain,(
% 1.89/1.03    v2_pre_topc(sK0)),
% 1.89/1.03    inference(cnf_transformation,[],[f52])).
% 1.89/1.03  
% 1.89/1.03  fof(f25,axiom,(
% 1.89/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f43,plain,(
% 1.89/1.03    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.89/1.03    inference(ennf_transformation,[],[f25])).
% 1.89/1.03  
% 1.89/1.03  fof(f44,plain,(
% 1.89/1.03    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/1.03    inference(flattening,[],[f43])).
% 1.89/1.03  
% 1.89/1.03  fof(f78,plain,(
% 1.89/1.03    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f44])).
% 1.89/1.03  
% 1.89/1.03  fof(f15,axiom,(
% 1.89/1.03    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f68,plain,(
% 1.89/1.03    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.89/1.03    inference(cnf_transformation,[],[f15])).
% 1.89/1.03  
% 1.89/1.03  fof(f13,axiom,(
% 1.89/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f66,plain,(
% 1.89/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.89/1.03    inference(cnf_transformation,[],[f13])).
% 1.89/1.03  
% 1.89/1.03  fof(f6,axiom,(
% 1.89/1.03    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f29,plain,(
% 1.89/1.03    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.89/1.03    inference(ennf_transformation,[],[f6])).
% 1.89/1.03  
% 1.89/1.03  fof(f30,plain,(
% 1.89/1.03    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.89/1.03    inference(flattening,[],[f29])).
% 1.89/1.03  
% 1.89/1.03  fof(f59,plain,(
% 1.89/1.03    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f30])).
% 1.89/1.03  
% 1.89/1.03  fof(f5,axiom,(
% 1.89/1.03    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f28,plain,(
% 1.89/1.03    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.89/1.03    inference(ennf_transformation,[],[f5])).
% 1.89/1.03  
% 1.89/1.03  fof(f57,plain,(
% 1.89/1.03    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f28])).
% 1.89/1.03  
% 1.89/1.03  fof(f100,plain,(
% 1.89/1.03    ( ! [X0] : (sK2 != X0 | r1_xboole_0(X0,X0)) )),
% 1.89/1.03    inference(definition_unfolding,[],[f57,f88])).
% 1.89/1.03  
% 1.89/1.03  fof(f104,plain,(
% 1.89/1.03    r1_xboole_0(sK2,sK2)),
% 1.89/1.03    inference(equality_resolution,[],[f100])).
% 1.89/1.03  
% 1.89/1.03  fof(f23,axiom,(
% 1.89/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/1.03  
% 1.89/1.03  fof(f39,plain,(
% 1.89/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.89/1.03    inference(ennf_transformation,[],[f23])).
% 1.89/1.03  
% 1.89/1.03  fof(f40,plain,(
% 1.89/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.89/1.03    inference(flattening,[],[f39])).
% 1.89/1.03  
% 1.89/1.03  fof(f76,plain,(
% 1.89/1.03    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.89/1.03    inference(cnf_transformation,[],[f40])).
% 1.89/1.03  
% 1.89/1.03  fof(f79,plain,(
% 1.89/1.03    ~v2_struct_0(sK0)),
% 1.89/1.03    inference(cnf_transformation,[],[f52])).
% 1.89/1.03  
% 1.89/1.03  cnf(c_23,negated_conjecture,
% 1.89/1.03      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 1.89/1.03      inference(cnf_transformation,[],[f82]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_656,plain,
% 1.89/1.03      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 1.89/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_14,plain,
% 1.89/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f75]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_13,plain,
% 1.89/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_338,plain,
% 1.89/1.03      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.89/1.03      inference(resolution,[status(thm)],[c_14,c_13]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_24,negated_conjecture,
% 1.89/1.03      ( l1_pre_topc(sK0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f81]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_387,plain,
% 1.89/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.89/1.03      inference(resolution_lifted,[status(thm)],[c_338,c_24]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_388,plain,
% 1.89/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.89/1.03      inference(unflattening,[status(thm)],[c_387]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_674,plain,
% 1.89/1.03      ( m1_subset_1(sK1,k2_struct_0(sK0)) = iProver_top ),
% 1.89/1.03      inference(light_normalisation,[status(thm)],[c_656,c_388]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_9,negated_conjecture,
% 1.89/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
% 1.89/1.03      inference(cnf_transformation,[],[f102]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_660,plain,
% 1.89/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
% 1.89/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_7,plain,
% 1.89/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.89/1.03      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f101]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_662,plain,
% 1.89/1.03      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 1.89/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.89/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_1029,plain,
% 1.89/1.03      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))) = k3_subset_1(X0,sK2) ),
% 1.89/1.03      inference(superposition,[status(thm)],[c_660,c_662]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_0,negated_conjecture,
% 1.89/1.03      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = sK2 ),
% 1.89/1.03      inference(cnf_transformation,[],[f96]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_2,negated_conjecture,
% 1.89/1.03      ( k5_xboole_0(X0,sK2) = X0 ),
% 1.89/1.03      inference(cnf_transformation,[],[f98]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_1034,plain,
% 1.89/1.03      ( k3_subset_1(X0,sK2) = X0 ),
% 1.89/1.03      inference(light_normalisation,[status(thm)],[c_1029,c_0,c_2]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_10,negated_conjecture,
% 1.89/1.03      ( r2_hidden(X0,X1)
% 1.89/1.03      | r2_hidden(X0,k3_subset_1(X2,X1))
% 1.89/1.03      | ~ m1_subset_1(X0,X2)
% 1.89/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.89/1.03      | sK2 = X2 ),
% 1.89/1.03      inference(cnf_transformation,[],[f103]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_659,plain,
% 1.89/1.03      ( sK2 = X0
% 1.89/1.03      | r2_hidden(X1,X2) = iProver_top
% 1.89/1.03      | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top
% 1.89/1.03      | m1_subset_1(X1,X0) != iProver_top
% 1.89/1.03      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.89/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_1079,plain,
% 1.89/1.03      ( sK2 = X0
% 1.89/1.03      | r2_hidden(X1,X0) = iProver_top
% 1.89/1.03      | r2_hidden(X1,sK2) = iProver_top
% 1.89/1.03      | m1_subset_1(X1,X0) != iProver_top
% 1.89/1.03      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.89/1.03      inference(superposition,[status(thm)],[c_1034,c_659]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_47,plain,
% 1.89/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
% 1.89/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_1082,plain,
% 1.89/1.03      ( m1_subset_1(X1,X0) != iProver_top
% 1.89/1.03      | r2_hidden(X1,sK2) = iProver_top
% 1.89/1.03      | r2_hidden(X1,X0) = iProver_top
% 1.89/1.03      | sK2 = X0 ),
% 1.89/1.03      inference(global_propositional_subsumption,
% 1.89/1.03                [status(thm)],
% 1.89/1.03                [c_1079,c_47]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_1083,plain,
% 1.89/1.03      ( sK2 = X0
% 1.89/1.03      | r2_hidden(X1,X0) = iProver_top
% 1.89/1.03      | r2_hidden(X1,sK2) = iProver_top
% 1.89/1.03      | m1_subset_1(X1,X0) != iProver_top ),
% 1.89/1.03      inference(renaming,[status(thm)],[c_1082]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_1,negated_conjecture,
% 1.89/1.03      ( r1_tarski(sK2,X0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f97]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_12,plain,
% 1.89/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_294,plain,
% 1.89/1.03      ( ~ r2_hidden(X0,X1) | X0 != X2 | sK2 != X1 ),
% 1.89/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_12]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_295,plain,
% 1.89/1.03      ( ~ r2_hidden(X0,sK2) ),
% 1.89/1.03      inference(unflattening,[status(thm)],[c_294]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_655,plain,
% 1.89/1.03      ( r2_hidden(X0,sK2) != iProver_top ),
% 1.89/1.03      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_1090,plain,
% 1.89/1.03      ( sK2 = X0
% 1.89/1.03      | r2_hidden(X1,X0) = iProver_top
% 1.89/1.03      | m1_subset_1(X1,X0) != iProver_top ),
% 1.89/1.03      inference(forward_subsumption_resolution,
% 1.89/1.03                [status(thm)],
% 1.89/1.03                [c_1083,c_655]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_1093,plain,
% 1.89/1.03      ( k2_struct_0(sK0) = sK2
% 1.89/1.03      | r2_hidden(sK1,k2_struct_0(sK0)) = iProver_top ),
% 1.89/1.03      inference(superposition,[status(thm)],[c_674,c_1090]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_18,negated_conjecture,
% 1.89/1.03      ( ~ v3_pre_topc(X0,sK0)
% 1.89/1.03      | ~ v4_pre_topc(X0,sK0)
% 1.89/1.03      | r2_hidden(X0,sK2)
% 1.89/1.03      | ~ r2_hidden(sK1,X0)
% 1.89/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.89/1.03      inference(cnf_transformation,[],[f87]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_318,plain,
% 1.89/1.03      ( ~ v3_pre_topc(X0,sK0)
% 1.89/1.03      | ~ v4_pre_topc(X0,sK0)
% 1.89/1.03      | ~ r2_hidden(sK1,X0)
% 1.89/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.89/1.03      inference(backward_subsumption_resolution,
% 1.89/1.03                [status(thm)],
% 1.89/1.03                [c_295,c_18]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_16,plain,
% 1.89/1.03      ( v4_pre_topc(k2_struct_0(X0),X0)
% 1.89/1.03      | ~ v2_pre_topc(X0)
% 1.89/1.03      | ~ l1_pre_topc(X0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_25,negated_conjecture,
% 1.89/1.03      ( v2_pre_topc(sK0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f80]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_372,plain,
% 1.89/1.03      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 1.89/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_373,plain,
% 1.89/1.03      ( v4_pre_topc(k2_struct_0(sK0),sK0) | ~ l1_pre_topc(sK0) ),
% 1.89/1.03      inference(unflattening,[status(thm)],[c_372]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_375,plain,
% 1.89/1.03      ( v4_pre_topc(k2_struct_0(sK0),sK0) ),
% 1.89/1.03      inference(global_propositional_subsumption,
% 1.89/1.03                [status(thm)],
% 1.89/1.03                [c_373,c_24]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_393,plain,
% 1.89/1.03      ( ~ v3_pre_topc(X0,sK0)
% 1.89/1.03      | ~ r2_hidden(sK1,X0)
% 1.89/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.89/1.03      | k2_struct_0(sK0) != X0
% 1.89/1.03      | sK0 != sK0 ),
% 1.89/1.03      inference(resolution_lifted,[status(thm)],[c_318,c_375]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_394,plain,
% 1.89/1.03      ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
% 1.89/1.03      | ~ r2_hidden(sK1,k2_struct_0(sK0))
% 1.89/1.03      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.89/1.03      inference(unflattening,[status(thm)],[c_393]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_17,plain,
% 1.89/1.03      ( v3_pre_topc(k2_struct_0(X0),X0)
% 1.89/1.03      | ~ v2_pre_topc(X0)
% 1.89/1.03      | ~ l1_pre_topc(X0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_361,plain,
% 1.89/1.03      ( v3_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 1.89/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_362,plain,
% 1.89/1.03      ( v3_pre_topc(k2_struct_0(sK0),sK0) | ~ l1_pre_topc(sK0) ),
% 1.89/1.03      inference(unflattening,[status(thm)],[c_361]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_396,plain,
% 1.89/1.03      ( ~ r2_hidden(sK1,k2_struct_0(sK0))
% 1.89/1.03      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.89/1.03      inference(global_propositional_subsumption,
% 1.89/1.03                [status(thm)],
% 1.89/1.03                [c_394,c_24,c_362]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_654,plain,
% 1.89/1.03      ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
% 1.89/1.03      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.89/1.03      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_685,plain,
% 1.89/1.03      ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
% 1.89/1.03      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.89/1.03      inference(light_normalisation,[status(thm)],[c_654,c_388]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_8,plain,
% 1.89/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.89/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_661,plain,
% 1.89/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.89/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_6,plain,
% 1.89/1.03      ( k2_subset_1(X0) = X0 ),
% 1.89/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_679,plain,
% 1.89/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.89/1.03      inference(light_normalisation,[status(thm)],[c_661,c_6]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_688,plain,
% 1.89/1.03      ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top ),
% 1.89/1.03      inference(forward_subsumption_resolution,
% 1.89/1.03                [status(thm)],
% 1.89/1.03                [c_685,c_679]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_5,plain,
% 1.89/1.03      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_303,plain,
% 1.89/1.03      ( ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) | X1 != X2 | sK2 != X0 ),
% 1.89/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_5]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_304,plain,
% 1.89/1.03      ( ~ r1_xboole_0(sK2,X0) | v1_xboole_0(sK2) ),
% 1.89/1.03      inference(unflattening,[status(thm)],[c_303]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_4,negated_conjecture,
% 1.89/1.03      ( r1_xboole_0(sK2,sK2) ),
% 1.89/1.03      inference(cnf_transformation,[],[f104]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_56,plain,
% 1.89/1.03      ( r1_tarski(sK2,sK2) ),
% 1.89/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_88,plain,
% 1.89/1.03      ( ~ r1_xboole_0(sK2,sK2)
% 1.89/1.03      | ~ r1_tarski(sK2,sK2)
% 1.89/1.03      | v1_xboole_0(sK2) ),
% 1.89/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_308,plain,
% 1.89/1.03      ( v1_xboole_0(sK2) ),
% 1.89/1.03      inference(global_propositional_subsumption,
% 1.89/1.03                [status(thm)],
% 1.89/1.03                [c_304,c_4,c_56,c_88]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_15,plain,
% 1.89/1.03      ( v2_struct_0(X0)
% 1.89/1.03      | ~ l1_struct_0(X0)
% 1.89/1.03      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.89/1.03      inference(cnf_transformation,[],[f76]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_26,negated_conjecture,
% 1.89/1.03      ( ~ v2_struct_0(sK0) ),
% 1.89/1.03      inference(cnf_transformation,[],[f79]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_281,plain,
% 1.89/1.03      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK0 != X0 ),
% 1.89/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_282,plain,
% 1.89/1.03      ( ~ l1_struct_0(sK0) | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.89/1.03      inference(unflattening,[status(thm)],[c_281]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_326,plain,
% 1.89/1.03      ( ~ l1_struct_0(sK0) | u1_struct_0(sK0) != sK2 ),
% 1.89/1.03      inference(resolution_lifted,[status(thm)],[c_308,c_282]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_349,plain,
% 1.89/1.03      ( ~ l1_pre_topc(X0) | u1_struct_0(sK0) != sK2 | sK0 != X0 ),
% 1.89/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_326]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_350,plain,
% 1.89/1.03      ( ~ l1_pre_topc(sK0) | u1_struct_0(sK0) != sK2 ),
% 1.89/1.03      inference(unflattening,[status(thm)],[c_349]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_352,plain,
% 1.89/1.03      ( u1_struct_0(sK0) != sK2 ),
% 1.89/1.03      inference(global_propositional_subsumption,
% 1.89/1.03                [status(thm)],
% 1.89/1.03                [c_350,c_24]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(c_667,plain,
% 1.89/1.03      ( k2_struct_0(sK0) != sK2 ),
% 1.89/1.03      inference(light_normalisation,[status(thm)],[c_352,c_388]) ).
% 1.89/1.03  
% 1.89/1.03  cnf(contradiction,plain,
% 1.89/1.03      ( $false ),
% 1.89/1.03      inference(minisat,[status(thm)],[c_1093,c_688,c_667]) ).
% 1.89/1.03  
% 1.89/1.03  
% 1.89/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.89/1.03  
% 1.89/1.03  ------                               Statistics
% 1.89/1.03  
% 1.89/1.03  ------ General
% 1.89/1.03  
% 1.89/1.03  abstr_ref_over_cycles:                  0
% 1.89/1.03  abstr_ref_under_cycles:                 0
% 1.89/1.03  gc_basic_clause_elim:                   0
% 1.89/1.03  forced_gc_time:                         0
% 1.89/1.03  parsing_time:                           0.014
% 1.89/1.03  unif_index_cands_time:                  0.
% 1.89/1.03  unif_index_add_time:                    0.
% 1.89/1.03  orderings_time:                         0.
% 1.89/1.03  out_proof_time:                         0.011
% 1.89/1.03  total_time:                             0.08
% 1.89/1.03  num_of_symbols:                         53
% 1.89/1.03  num_of_terms:                           1111
% 1.89/1.03  
% 1.89/1.03  ------ Preprocessing
% 1.89/1.03  
% 1.89/1.03  num_of_splits:                          0
% 1.89/1.03  num_of_split_atoms:                     0
% 1.89/1.03  num_of_reused_defs:                     0
% 1.89/1.03  num_eq_ax_congr_red:                    36
% 1.89/1.03  num_of_sem_filtered_clauses:            1
% 1.89/1.03  num_of_subtypes:                        0
% 1.89/1.03  monotx_restored_types:                  0
% 1.89/1.03  sat_num_of_epr_types:                   0
% 1.89/1.03  sat_num_of_non_cyclic_types:            0
% 1.89/1.03  sat_guarded_non_collapsed_types:        0
% 1.89/1.03  num_pure_diseq_elim:                    0
% 1.89/1.03  simp_replaced_by:                       0
% 1.89/1.03  res_preprocessed:                       90
% 1.89/1.03  prep_upred:                             0
% 1.89/1.03  prep_unflattend:                        11
% 1.89/1.03  smt_new_axioms:                         0
% 1.89/1.03  pred_elim_cands:                        2
% 1.89/1.03  pred_elim:                              9
% 1.89/1.03  pred_elim_cl:                           13
% 1.89/1.03  pred_elim_cycles:                       11
% 1.89/1.03  merged_defs:                            0
% 1.89/1.03  merged_defs_ncl:                        0
% 1.89/1.03  bin_hyper_res:                          0
% 1.89/1.03  prep_cycles:                            4
% 1.89/1.03  pred_elim_time:                         0.002
% 1.89/1.03  splitting_time:                         0.
% 1.89/1.03  sem_filter_time:                        0.
% 1.89/1.03  monotx_time:                            0.
% 1.89/1.03  subtype_inf_time:                       0.
% 1.89/1.03  
% 1.89/1.03  ------ Problem properties
% 1.89/1.03  
% 1.89/1.03  clauses:                                14
% 1.89/1.03  conjectures:                            6
% 1.89/1.03  epr:                                    1
% 1.89/1.03  horn:                                   13
% 1.89/1.03  ground:                                 5
% 1.89/1.03  unary:                                  10
% 1.89/1.03  binary:                                 2
% 1.89/1.03  lits:                                   22
% 1.89/1.03  lits_eq:                                7
% 1.89/1.03  fd_pure:                                0
% 1.89/1.03  fd_pseudo:                              0
% 1.89/1.03  fd_cond:                                1
% 1.89/1.03  fd_pseudo_cond:                         0
% 1.89/1.03  ac_symbols:                             0
% 1.89/1.03  
% 1.89/1.03  ------ Propositional Solver
% 1.89/1.03  
% 1.89/1.03  prop_solver_calls:                      25
% 1.89/1.03  prop_fast_solver_calls:                 399
% 1.89/1.03  smt_solver_calls:                       0
% 1.89/1.03  smt_fast_solver_calls:                  0
% 1.89/1.03  prop_num_of_clauses:                    352
% 1.89/1.03  prop_preprocess_simplified:             2289
% 1.89/1.03  prop_fo_subsumed:                       6
% 1.89/1.03  prop_solver_time:                       0.
% 1.89/1.03  smt_solver_time:                        0.
% 1.89/1.03  smt_fast_solver_time:                   0.
% 1.89/1.03  prop_fast_solver_time:                  0.
% 1.89/1.03  prop_unsat_core_time:                   0.
% 1.89/1.03  
% 1.89/1.03  ------ QBF
% 1.89/1.03  
% 1.89/1.03  qbf_q_res:                              0
% 1.89/1.03  qbf_num_tautologies:                    0
% 1.89/1.03  qbf_prep_cycles:                        0
% 1.89/1.03  
% 1.89/1.03  ------ BMC1
% 1.89/1.03  
% 1.89/1.03  bmc1_current_bound:                     -1
% 1.89/1.03  bmc1_last_solved_bound:                 -1
% 1.89/1.03  bmc1_unsat_core_size:                   -1
% 1.89/1.03  bmc1_unsat_core_parents_size:           -1
% 1.89/1.03  bmc1_merge_next_fun:                    0
% 1.89/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.89/1.03  
% 1.89/1.03  ------ Instantiation
% 1.89/1.03  
% 1.89/1.03  inst_num_of_clauses:                    97
% 1.89/1.03  inst_num_in_passive:                    23
% 1.89/1.03  inst_num_in_active:                     63
% 1.89/1.03  inst_num_in_unprocessed:                11
% 1.89/1.03  inst_num_of_loops:                      70
% 1.89/1.03  inst_num_of_learning_restarts:          0
% 1.89/1.03  inst_num_moves_active_passive:          5
% 1.89/1.03  inst_lit_activity:                      0
% 1.89/1.03  inst_lit_activity_moves:                0
% 1.89/1.03  inst_num_tautologies:                   0
% 1.89/1.03  inst_num_prop_implied:                  0
% 1.89/1.03  inst_num_existing_simplified:           0
% 1.89/1.03  inst_num_eq_res_simplified:             0
% 1.89/1.03  inst_num_child_elim:                    0
% 1.89/1.03  inst_num_of_dismatching_blockings:      9
% 1.89/1.03  inst_num_of_non_proper_insts:           60
% 1.89/1.03  inst_num_of_duplicates:                 0
% 1.89/1.03  inst_inst_num_from_inst_to_res:         0
% 1.89/1.03  inst_dismatching_checking_time:         0.
% 1.89/1.03  
% 1.89/1.03  ------ Resolution
% 1.89/1.03  
% 1.89/1.03  res_num_of_clauses:                     0
% 1.89/1.03  res_num_in_passive:                     0
% 1.89/1.03  res_num_in_active:                      0
% 1.89/1.03  res_num_of_loops:                       94
% 1.89/1.03  res_forward_subset_subsumed:            3
% 1.89/1.03  res_backward_subset_subsumed:           1
% 1.89/1.03  res_forward_subsumed:                   0
% 1.89/1.03  res_backward_subsumed:                  2
% 1.89/1.03  res_forward_subsumption_resolution:     0
% 1.89/1.03  res_backward_subsumption_resolution:    1
% 1.89/1.03  res_clause_to_clause_subsumption:       35
% 1.89/1.03  res_orphan_elimination:                 0
% 1.89/1.03  res_tautology_del:                      5
% 1.89/1.03  res_num_eq_res_simplified:              0
% 1.89/1.03  res_num_sel_changes:                    0
% 1.89/1.03  res_moves_from_active_to_pass:          0
% 1.89/1.03  
% 1.89/1.03  ------ Superposition
% 1.89/1.03  
% 1.89/1.03  sup_time_total:                         0.
% 1.89/1.03  sup_time_generating:                    0.
% 1.89/1.03  sup_time_sim_full:                      0.
% 1.89/1.03  sup_time_sim_immed:                     0.
% 1.89/1.03  
% 1.89/1.03  sup_num_of_clauses:                     19
% 1.89/1.03  sup_num_in_active:                      14
% 1.89/1.03  sup_num_in_passive:                     5
% 1.89/1.03  sup_num_of_loops:                       13
% 1.89/1.03  sup_fw_superposition:                   6
% 1.89/1.03  sup_bw_superposition:                   2
% 1.89/1.03  sup_immediate_simplified:               2
% 1.89/1.03  sup_given_eliminated:                   0
% 1.89/1.03  comparisons_done:                       0
% 1.89/1.03  comparisons_avoided:                    0
% 1.89/1.03  
% 1.89/1.03  ------ Simplifications
% 1.89/1.03  
% 1.89/1.03  
% 1.89/1.03  sim_fw_subset_subsumed:                 1
% 1.89/1.03  sim_bw_subset_subsumed:                 0
% 1.89/1.03  sim_fw_subsumed:                        1
% 1.89/1.03  sim_bw_subsumed:                        0
% 1.89/1.03  sim_fw_subsumption_res:                 2
% 1.89/1.03  sim_bw_subsumption_res:                 0
% 1.89/1.03  sim_tautology_del:                      0
% 1.89/1.03  sim_eq_tautology_del:                   0
% 1.89/1.03  sim_eq_res_simp:                        0
% 1.89/1.03  sim_fw_demodulated:                     0
% 1.89/1.03  sim_bw_demodulated:                     0
% 1.89/1.03  sim_light_normalised:                   6
% 1.89/1.03  sim_joinable_taut:                      0
% 1.89/1.03  sim_joinable_simp:                      0
% 1.89/1.03  sim_ac_normalised:                      0
% 1.89/1.03  sim_smt_subsumption:                    0
% 1.89/1.03  
%------------------------------------------------------------------------------
