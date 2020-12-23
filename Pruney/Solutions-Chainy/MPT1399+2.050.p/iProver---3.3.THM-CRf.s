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
% DateTime   : Thu Dec  3 12:18:41 EST 2020

% Result     : Theorem 1.20s
% Output     : CNFRefutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 418 expanded)
%              Number of clauses        :   54 (  82 expanded)
%              Number of leaves         :   18 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  393 (4001 expanded)
%              Number of equality atoms :   82 ( 398 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).

fof(f57,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    ! [X0] : k1_subset_1(X0) = sK2 ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f65,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,sK2) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f68,plain,(
    ! [X0] : k3_subset_1(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(definition_unfolding,[],[f40,f63])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,(
    v1_xboole_0(sK2) ),
    inference(definition_unfolding,[],[f39,f63])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f43,f65])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_561,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_281,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_8])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_321,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_281,c_19])).

cnf(c_322,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_576,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_561,c_322])).

cnf(c_2,negated_conjecture,
    ( k3_subset_1(X0,sK2) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sK2 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_564,plain,
    ( sK2 = X0
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_769,plain,
    ( sK2 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_564])).

cnf(c_4,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_774,plain,
    ( m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | sK2 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_769,c_42])).

cnf(c_775,plain,
    ( sK2 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_774])).

cnf(c_943,plain,
    ( k2_struct_0(sK0) = sK2
    | r2_hidden(sK1,k2_struct_0(sK0)) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_576,c_775])).

cnf(c_1,negated_conjecture,
    ( r1_tarski(sK2,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_239,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_240,plain,
    ( ~ r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_911,plain,
    ( ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_912,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_0,negated_conjecture,
    ( v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_10,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_254,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_272,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != sK2
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_254,c_21])).

cnf(c_273,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) != sK2 ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_63,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_256,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) != sK2 ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_275,plain,
    ( u1_struct_0(sK0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_21,c_19,c_63,c_256])).

cnf(c_569,plain,
    ( k2_struct_0(sK0) != sK2 ),
    inference(light_normalisation,[status(thm)],[c_275,c_322])).

cnf(c_13,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | r2_hidden(X0,sK2)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_250,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_240,c_13])).

cnf(c_11,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_306,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_307,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_57,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_309,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_20,c_19,c_57])).

cnf(c_327,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_250,c_309])).

cnf(c_328,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_12,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_54,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_330,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_20,c_19,c_54])).

cnf(c_559,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_585,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_559,c_322])).

cnf(c_3,negated_conjecture,
    ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_566,plain,
    ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_582,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_566,c_2])).

cnf(c_588,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_585,c_582])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_943,c_912,c_569,c_588])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:36:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.20/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.20/0.98  
% 1.20/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.20/0.98  
% 1.20/0.98  ------  iProver source info
% 1.20/0.98  
% 1.20/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.20/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.20/0.98  git: non_committed_changes: false
% 1.20/0.98  git: last_make_outside_of_git: false
% 1.20/0.98  
% 1.20/0.98  ------ 
% 1.20/0.98  
% 1.20/0.98  ------ Input Options
% 1.20/0.98  
% 1.20/0.98  --out_options                           all
% 1.20/0.98  --tptp_safe_out                         true
% 1.20/0.98  --problem_path                          ""
% 1.20/0.98  --include_path                          ""
% 1.20/0.98  --clausifier                            res/vclausify_rel
% 1.20/0.98  --clausifier_options                    --mode clausify
% 1.20/0.98  --stdin                                 false
% 1.20/0.98  --stats_out                             all
% 1.20/0.98  
% 1.20/0.98  ------ General Options
% 1.20/0.98  
% 1.20/0.98  --fof                                   false
% 1.20/0.98  --time_out_real                         305.
% 1.20/0.98  --time_out_virtual                      -1.
% 1.20/0.98  --symbol_type_check                     false
% 1.20/0.98  --clausify_out                          false
% 1.20/0.98  --sig_cnt_out                           false
% 1.20/0.98  --trig_cnt_out                          false
% 1.20/0.98  --trig_cnt_out_tolerance                1.
% 1.20/0.98  --trig_cnt_out_sk_spl                   false
% 1.20/0.98  --abstr_cl_out                          false
% 1.20/0.98  
% 1.20/0.98  ------ Global Options
% 1.20/0.98  
% 1.20/0.98  --schedule                              default
% 1.20/0.98  --add_important_lit                     false
% 1.20/0.98  --prop_solver_per_cl                    1000
% 1.20/0.98  --min_unsat_core                        false
% 1.20/0.98  --soft_assumptions                      false
% 1.20/0.98  --soft_lemma_size                       3
% 1.20/0.98  --prop_impl_unit_size                   0
% 1.20/0.98  --prop_impl_unit                        []
% 1.20/0.98  --share_sel_clauses                     true
% 1.20/0.98  --reset_solvers                         false
% 1.20/0.98  --bc_imp_inh                            [conj_cone]
% 1.20/0.98  --conj_cone_tolerance                   3.
% 1.20/0.98  --extra_neg_conj                        none
% 1.20/0.98  --large_theory_mode                     true
% 1.20/0.98  --prolific_symb_bound                   200
% 1.20/0.98  --lt_threshold                          2000
% 1.20/0.98  --clause_weak_htbl                      true
% 1.20/0.98  --gc_record_bc_elim                     false
% 1.20/0.98  
% 1.20/0.98  ------ Preprocessing Options
% 1.20/0.98  
% 1.20/0.98  --preprocessing_flag                    true
% 1.20/0.98  --time_out_prep_mult                    0.1
% 1.20/0.98  --splitting_mode                        input
% 1.20/0.98  --splitting_grd                         true
% 1.20/0.98  --splitting_cvd                         false
% 1.20/0.98  --splitting_cvd_svl                     false
% 1.20/0.98  --splitting_nvd                         32
% 1.20/0.98  --sub_typing                            true
% 1.20/0.98  --prep_gs_sim                           true
% 1.20/0.98  --prep_unflatten                        true
% 1.20/0.98  --prep_res_sim                          true
% 1.20/0.98  --prep_upred                            true
% 1.20/0.98  --prep_sem_filter                       exhaustive
% 1.20/0.98  --prep_sem_filter_out                   false
% 1.20/0.98  --pred_elim                             true
% 1.20/0.98  --res_sim_input                         true
% 1.20/0.98  --eq_ax_congr_red                       true
% 1.20/0.98  --pure_diseq_elim                       true
% 1.20/0.98  --brand_transform                       false
% 1.20/0.98  --non_eq_to_eq                          false
% 1.20/0.98  --prep_def_merge                        true
% 1.20/0.98  --prep_def_merge_prop_impl              false
% 1.20/0.98  --prep_def_merge_mbd                    true
% 1.20/0.98  --prep_def_merge_tr_red                 false
% 1.20/0.98  --prep_def_merge_tr_cl                  false
% 1.20/0.98  --smt_preprocessing                     true
% 1.20/0.98  --smt_ac_axioms                         fast
% 1.20/0.98  --preprocessed_out                      false
% 1.20/0.98  --preprocessed_stats                    false
% 1.20/0.98  
% 1.20/0.98  ------ Abstraction refinement Options
% 1.20/0.98  
% 1.20/0.98  --abstr_ref                             []
% 1.20/0.98  --abstr_ref_prep                        false
% 1.20/0.98  --abstr_ref_until_sat                   false
% 1.20/0.98  --abstr_ref_sig_restrict                funpre
% 1.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.20/0.98  --abstr_ref_under                       []
% 1.20/0.98  
% 1.20/0.98  ------ SAT Options
% 1.20/0.98  
% 1.20/0.98  --sat_mode                              false
% 1.20/0.98  --sat_fm_restart_options                ""
% 1.20/0.98  --sat_gr_def                            false
% 1.20/0.98  --sat_epr_types                         true
% 1.20/0.98  --sat_non_cyclic_types                  false
% 1.20/0.98  --sat_finite_models                     false
% 1.20/0.98  --sat_fm_lemmas                         false
% 1.20/0.98  --sat_fm_prep                           false
% 1.20/0.98  --sat_fm_uc_incr                        true
% 1.20/0.98  --sat_out_model                         small
% 1.20/0.98  --sat_out_clauses                       false
% 1.20/0.98  
% 1.20/0.98  ------ QBF Options
% 1.20/0.98  
% 1.20/0.98  --qbf_mode                              false
% 1.20/0.98  --qbf_elim_univ                         false
% 1.20/0.98  --qbf_dom_inst                          none
% 1.20/0.98  --qbf_dom_pre_inst                      false
% 1.20/0.98  --qbf_sk_in                             false
% 1.20/0.98  --qbf_pred_elim                         true
% 1.20/0.98  --qbf_split                             512
% 1.20/0.98  
% 1.20/0.98  ------ BMC1 Options
% 1.20/0.98  
% 1.20/0.98  --bmc1_incremental                      false
% 1.20/0.98  --bmc1_axioms                           reachable_all
% 1.20/0.98  --bmc1_min_bound                        0
% 1.20/0.98  --bmc1_max_bound                        -1
% 1.20/0.98  --bmc1_max_bound_default                -1
% 1.20/0.98  --bmc1_symbol_reachability              true
% 1.20/0.98  --bmc1_property_lemmas                  false
% 1.20/0.98  --bmc1_k_induction                      false
% 1.20/0.98  --bmc1_non_equiv_states                 false
% 1.20/0.98  --bmc1_deadlock                         false
% 1.20/0.98  --bmc1_ucm                              false
% 1.20/0.98  --bmc1_add_unsat_core                   none
% 1.20/0.98  --bmc1_unsat_core_children              false
% 1.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.20/0.98  --bmc1_out_stat                         full
% 1.20/0.98  --bmc1_ground_init                      false
% 1.20/0.98  --bmc1_pre_inst_next_state              false
% 1.20/0.98  --bmc1_pre_inst_state                   false
% 1.20/0.98  --bmc1_pre_inst_reach_state             false
% 1.20/0.98  --bmc1_out_unsat_core                   false
% 1.20/0.98  --bmc1_aig_witness_out                  false
% 1.20/0.98  --bmc1_verbose                          false
% 1.20/0.98  --bmc1_dump_clauses_tptp                false
% 1.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.20/0.98  --bmc1_dump_file                        -
% 1.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.20/0.98  --bmc1_ucm_extend_mode                  1
% 1.20/0.98  --bmc1_ucm_init_mode                    2
% 1.20/0.98  --bmc1_ucm_cone_mode                    none
% 1.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.20/0.98  --bmc1_ucm_relax_model                  4
% 1.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.20/0.98  --bmc1_ucm_layered_model                none
% 1.20/0.98  --bmc1_ucm_max_lemma_size               10
% 1.20/0.98  
% 1.20/0.98  ------ AIG Options
% 1.20/0.98  
% 1.20/0.98  --aig_mode                              false
% 1.20/0.98  
% 1.20/0.98  ------ Instantiation Options
% 1.20/0.98  
% 1.20/0.98  --instantiation_flag                    true
% 1.20/0.98  --inst_sos_flag                         false
% 1.20/0.98  --inst_sos_phase                        true
% 1.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.20/0.98  --inst_lit_sel_side                     num_symb
% 1.20/0.98  --inst_solver_per_active                1400
% 1.20/0.98  --inst_solver_calls_frac                1.
% 1.20/0.98  --inst_passive_queue_type               priority_queues
% 1.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.20/0.98  --inst_passive_queues_freq              [25;2]
% 1.20/0.98  --inst_dismatching                      true
% 1.20/0.98  --inst_eager_unprocessed_to_passive     true
% 1.20/0.98  --inst_prop_sim_given                   true
% 1.20/0.98  --inst_prop_sim_new                     false
% 1.20/0.98  --inst_subs_new                         false
% 1.20/0.98  --inst_eq_res_simp                      false
% 1.20/0.98  --inst_subs_given                       false
% 1.20/0.98  --inst_orphan_elimination               true
% 1.20/0.98  --inst_learning_loop_flag               true
% 1.20/0.98  --inst_learning_start                   3000
% 1.20/0.98  --inst_learning_factor                  2
% 1.20/0.98  --inst_start_prop_sim_after_learn       3
% 1.20/0.98  --inst_sel_renew                        solver
% 1.20/0.98  --inst_lit_activity_flag                true
% 1.20/0.98  --inst_restr_to_given                   false
% 1.20/0.98  --inst_activity_threshold               500
% 1.20/0.98  --inst_out_proof                        true
% 1.20/0.98  
% 1.20/0.98  ------ Resolution Options
% 1.20/0.98  
% 1.20/0.98  --resolution_flag                       true
% 1.20/0.98  --res_lit_sel                           adaptive
% 1.20/0.98  --res_lit_sel_side                      none
% 1.20/0.98  --res_ordering                          kbo
% 1.20/0.98  --res_to_prop_solver                    active
% 1.20/0.98  --res_prop_simpl_new                    false
% 1.20/0.98  --res_prop_simpl_given                  true
% 1.20/0.98  --res_passive_queue_type                priority_queues
% 1.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.20/0.98  --res_passive_queues_freq               [15;5]
% 1.20/0.98  --res_forward_subs                      full
% 1.20/0.98  --res_backward_subs                     full
% 1.20/0.98  --res_forward_subs_resolution           true
% 1.20/0.98  --res_backward_subs_resolution          true
% 1.20/0.98  --res_orphan_elimination                true
% 1.20/0.98  --res_time_limit                        2.
% 1.20/0.98  --res_out_proof                         true
% 1.20/0.98  
% 1.20/0.98  ------ Superposition Options
% 1.20/0.98  
% 1.20/0.98  --superposition_flag                    true
% 1.20/0.98  --sup_passive_queue_type                priority_queues
% 1.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.20/0.98  --demod_completeness_check              fast
% 1.20/0.98  --demod_use_ground                      true
% 1.20/0.98  --sup_to_prop_solver                    passive
% 1.20/0.98  --sup_prop_simpl_new                    true
% 1.20/0.98  --sup_prop_simpl_given                  true
% 1.20/0.98  --sup_fun_splitting                     false
% 1.20/0.98  --sup_smt_interval                      50000
% 1.20/0.98  
% 1.20/0.98  ------ Superposition Simplification Setup
% 1.20/0.98  
% 1.20/0.98  --sup_indices_passive                   []
% 1.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.20/0.98  --sup_full_bw                           [BwDemod]
% 1.20/0.98  --sup_immed_triv                        [TrivRules]
% 1.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.20/0.98  --sup_immed_bw_main                     []
% 1.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.20/0.98  
% 1.20/0.98  ------ Combination Options
% 1.20/0.98  
% 1.20/0.98  --comb_res_mult                         3
% 1.20/0.98  --comb_sup_mult                         2
% 1.20/0.98  --comb_inst_mult                        10
% 1.20/0.98  
% 1.20/0.98  ------ Debug Options
% 1.20/0.98  
% 1.20/0.98  --dbg_backtrace                         false
% 1.20/0.98  --dbg_dump_prop_clauses                 false
% 1.20/0.98  --dbg_dump_prop_clauses_file            -
% 1.20/0.98  --dbg_out_stat                          false
% 1.20/0.98  ------ Parsing...
% 1.20/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.20/0.98  
% 1.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.20/0.98  
% 1.20/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.20/0.98  
% 1.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.20/0.98  ------ Proving...
% 1.20/0.98  ------ Problem Properties 
% 1.20/0.98  
% 1.20/0.98  
% 1.20/0.98  clauses                                 11
% 1.20/0.98  conjectures                             6
% 1.20/0.98  EPR                                     1
% 1.20/0.98  Horn                                    10
% 1.20/0.98  unary                                   8
% 1.20/0.98  binary                                  1
% 1.20/0.98  lits                                    18
% 1.20/0.98  lits eq                                 4
% 1.20/0.98  fd_pure                                 0
% 1.20/0.98  fd_pseudo                               0
% 1.20/0.98  fd_cond                                 1
% 1.20/0.98  fd_pseudo_cond                          0
% 1.20/0.98  AC symbols                              0
% 1.20/0.98  
% 1.20/0.98  ------ Schedule dynamic 5 is on 
% 1.20/0.98  
% 1.20/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.20/0.98  
% 1.20/0.98  
% 1.20/0.98  ------ 
% 1.20/0.98  Current options:
% 1.20/0.98  ------ 
% 1.20/0.98  
% 1.20/0.98  ------ Input Options
% 1.20/0.98  
% 1.20/0.98  --out_options                           all
% 1.20/0.98  --tptp_safe_out                         true
% 1.20/0.98  --problem_path                          ""
% 1.20/0.98  --include_path                          ""
% 1.20/0.98  --clausifier                            res/vclausify_rel
% 1.20/0.98  --clausifier_options                    --mode clausify
% 1.20/0.98  --stdin                                 false
% 1.20/0.98  --stats_out                             all
% 1.20/0.98  
% 1.20/0.98  ------ General Options
% 1.20/0.98  
% 1.20/0.98  --fof                                   false
% 1.20/0.98  --time_out_real                         305.
% 1.20/0.98  --time_out_virtual                      -1.
% 1.20/0.98  --symbol_type_check                     false
% 1.20/0.98  --clausify_out                          false
% 1.20/0.98  --sig_cnt_out                           false
% 1.20/0.98  --trig_cnt_out                          false
% 1.20/0.98  --trig_cnt_out_tolerance                1.
% 1.20/0.98  --trig_cnt_out_sk_spl                   false
% 1.20/0.98  --abstr_cl_out                          false
% 1.20/0.98  
% 1.20/0.98  ------ Global Options
% 1.20/0.98  
% 1.20/0.98  --schedule                              default
% 1.20/0.98  --add_important_lit                     false
% 1.20/0.98  --prop_solver_per_cl                    1000
% 1.20/0.98  --min_unsat_core                        false
% 1.20/0.98  --soft_assumptions                      false
% 1.20/0.98  --soft_lemma_size                       3
% 1.20/0.98  --prop_impl_unit_size                   0
% 1.20/0.98  --prop_impl_unit                        []
% 1.20/0.98  --share_sel_clauses                     true
% 1.20/0.98  --reset_solvers                         false
% 1.20/0.98  --bc_imp_inh                            [conj_cone]
% 1.20/0.98  --conj_cone_tolerance                   3.
% 1.20/0.98  --extra_neg_conj                        none
% 1.20/0.98  --large_theory_mode                     true
% 1.20/0.98  --prolific_symb_bound                   200
% 1.20/0.98  --lt_threshold                          2000
% 1.20/0.98  --clause_weak_htbl                      true
% 1.20/0.98  --gc_record_bc_elim                     false
% 1.20/0.98  
% 1.20/0.98  ------ Preprocessing Options
% 1.20/0.98  
% 1.20/0.98  --preprocessing_flag                    true
% 1.20/0.98  --time_out_prep_mult                    0.1
% 1.20/0.98  --splitting_mode                        input
% 1.20/0.98  --splitting_grd                         true
% 1.20/0.98  --splitting_cvd                         false
% 1.20/0.98  --splitting_cvd_svl                     false
% 1.20/0.98  --splitting_nvd                         32
% 1.20/0.98  --sub_typing                            true
% 1.20/0.98  --prep_gs_sim                           true
% 1.20/0.98  --prep_unflatten                        true
% 1.20/0.98  --prep_res_sim                          true
% 1.20/0.98  --prep_upred                            true
% 1.20/0.98  --prep_sem_filter                       exhaustive
% 1.20/0.98  --prep_sem_filter_out                   false
% 1.20/0.98  --pred_elim                             true
% 1.20/0.98  --res_sim_input                         true
% 1.20/0.98  --eq_ax_congr_red                       true
% 1.20/0.98  --pure_diseq_elim                       true
% 1.20/0.98  --brand_transform                       false
% 1.20/0.98  --non_eq_to_eq                          false
% 1.20/0.98  --prep_def_merge                        true
% 1.20/0.98  --prep_def_merge_prop_impl              false
% 1.20/0.98  --prep_def_merge_mbd                    true
% 1.20/0.98  --prep_def_merge_tr_red                 false
% 1.20/0.98  --prep_def_merge_tr_cl                  false
% 1.20/0.98  --smt_preprocessing                     true
% 1.20/0.98  --smt_ac_axioms                         fast
% 1.20/0.98  --preprocessed_out                      false
% 1.20/0.98  --preprocessed_stats                    false
% 1.20/0.98  
% 1.20/0.98  ------ Abstraction refinement Options
% 1.20/0.98  
% 1.20/0.98  --abstr_ref                             []
% 1.20/0.98  --abstr_ref_prep                        false
% 1.20/0.98  --abstr_ref_until_sat                   false
% 1.20/0.98  --abstr_ref_sig_restrict                funpre
% 1.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.20/0.98  --abstr_ref_under                       []
% 1.20/0.98  
% 1.20/0.98  ------ SAT Options
% 1.20/0.98  
% 1.20/0.98  --sat_mode                              false
% 1.20/0.98  --sat_fm_restart_options                ""
% 1.20/0.98  --sat_gr_def                            false
% 1.20/0.98  --sat_epr_types                         true
% 1.20/0.98  --sat_non_cyclic_types                  false
% 1.20/0.98  --sat_finite_models                     false
% 1.20/0.98  --sat_fm_lemmas                         false
% 1.20/0.98  --sat_fm_prep                           false
% 1.20/0.98  --sat_fm_uc_incr                        true
% 1.20/0.98  --sat_out_model                         small
% 1.20/0.98  --sat_out_clauses                       false
% 1.20/0.98  
% 1.20/0.98  ------ QBF Options
% 1.20/0.98  
% 1.20/0.98  --qbf_mode                              false
% 1.20/0.98  --qbf_elim_univ                         false
% 1.20/0.98  --qbf_dom_inst                          none
% 1.20/0.98  --qbf_dom_pre_inst                      false
% 1.20/0.98  --qbf_sk_in                             false
% 1.20/0.98  --qbf_pred_elim                         true
% 1.20/0.98  --qbf_split                             512
% 1.20/0.98  
% 1.20/0.98  ------ BMC1 Options
% 1.20/0.98  
% 1.20/0.98  --bmc1_incremental                      false
% 1.20/0.98  --bmc1_axioms                           reachable_all
% 1.20/0.98  --bmc1_min_bound                        0
% 1.20/0.98  --bmc1_max_bound                        -1
% 1.20/0.98  --bmc1_max_bound_default                -1
% 1.20/0.98  --bmc1_symbol_reachability              true
% 1.20/0.98  --bmc1_property_lemmas                  false
% 1.20/0.98  --bmc1_k_induction                      false
% 1.20/0.98  --bmc1_non_equiv_states                 false
% 1.20/0.98  --bmc1_deadlock                         false
% 1.20/0.98  --bmc1_ucm                              false
% 1.20/0.98  --bmc1_add_unsat_core                   none
% 1.20/0.98  --bmc1_unsat_core_children              false
% 1.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.20/0.98  --bmc1_out_stat                         full
% 1.20/0.98  --bmc1_ground_init                      false
% 1.20/0.98  --bmc1_pre_inst_next_state              false
% 1.20/0.98  --bmc1_pre_inst_state                   false
% 1.20/0.98  --bmc1_pre_inst_reach_state             false
% 1.20/0.98  --bmc1_out_unsat_core                   false
% 1.20/0.98  --bmc1_aig_witness_out                  false
% 1.20/0.98  --bmc1_verbose                          false
% 1.20/0.98  --bmc1_dump_clauses_tptp                false
% 1.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.20/0.98  --bmc1_dump_file                        -
% 1.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.20/0.98  --bmc1_ucm_extend_mode                  1
% 1.20/0.98  --bmc1_ucm_init_mode                    2
% 1.20/0.98  --bmc1_ucm_cone_mode                    none
% 1.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.20/0.98  --bmc1_ucm_relax_model                  4
% 1.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.20/0.98  --bmc1_ucm_layered_model                none
% 1.20/0.98  --bmc1_ucm_max_lemma_size               10
% 1.20/0.98  
% 1.20/0.98  ------ AIG Options
% 1.20/0.98  
% 1.20/0.98  --aig_mode                              false
% 1.20/0.98  
% 1.20/0.98  ------ Instantiation Options
% 1.20/0.98  
% 1.20/0.98  --instantiation_flag                    true
% 1.20/0.98  --inst_sos_flag                         false
% 1.20/0.98  --inst_sos_phase                        true
% 1.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.20/0.98  --inst_lit_sel_side                     none
% 1.20/0.98  --inst_solver_per_active                1400
% 1.20/0.98  --inst_solver_calls_frac                1.
% 1.20/0.98  --inst_passive_queue_type               priority_queues
% 1.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.20/0.98  --inst_passive_queues_freq              [25;2]
% 1.20/0.98  --inst_dismatching                      true
% 1.20/0.98  --inst_eager_unprocessed_to_passive     true
% 1.20/0.98  --inst_prop_sim_given                   true
% 1.20/0.98  --inst_prop_sim_new                     false
% 1.20/0.98  --inst_subs_new                         false
% 1.20/0.98  --inst_eq_res_simp                      false
% 1.20/0.98  --inst_subs_given                       false
% 1.20/0.98  --inst_orphan_elimination               true
% 1.20/0.98  --inst_learning_loop_flag               true
% 1.20/0.98  --inst_learning_start                   3000
% 1.20/0.98  --inst_learning_factor                  2
% 1.20/0.98  --inst_start_prop_sim_after_learn       3
% 1.20/0.98  --inst_sel_renew                        solver
% 1.20/0.98  --inst_lit_activity_flag                true
% 1.20/0.98  --inst_restr_to_given                   false
% 1.20/0.98  --inst_activity_threshold               500
% 1.20/0.98  --inst_out_proof                        true
% 1.20/0.98  
% 1.20/0.98  ------ Resolution Options
% 1.20/0.98  
% 1.20/0.98  --resolution_flag                       false
% 1.20/0.98  --res_lit_sel                           adaptive
% 1.20/0.98  --res_lit_sel_side                      none
% 1.20/0.98  --res_ordering                          kbo
% 1.20/0.98  --res_to_prop_solver                    active
% 1.20/0.98  --res_prop_simpl_new                    false
% 1.20/0.98  --res_prop_simpl_given                  true
% 1.20/0.98  --res_passive_queue_type                priority_queues
% 1.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.20/0.98  --res_passive_queues_freq               [15;5]
% 1.20/0.98  --res_forward_subs                      full
% 1.20/0.98  --res_backward_subs                     full
% 1.20/0.98  --res_forward_subs_resolution           true
% 1.20/0.98  --res_backward_subs_resolution          true
% 1.20/0.98  --res_orphan_elimination                true
% 1.20/0.98  --res_time_limit                        2.
% 1.20/0.98  --res_out_proof                         true
% 1.20/0.98  
% 1.20/0.98  ------ Superposition Options
% 1.20/0.98  
% 1.20/0.98  --superposition_flag                    true
% 1.20/0.98  --sup_passive_queue_type                priority_queues
% 1.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.20/0.98  --demod_completeness_check              fast
% 1.20/0.98  --demod_use_ground                      true
% 1.20/0.98  --sup_to_prop_solver                    passive
% 1.20/0.98  --sup_prop_simpl_new                    true
% 1.20/0.98  --sup_prop_simpl_given                  true
% 1.20/0.98  --sup_fun_splitting                     false
% 1.20/0.98  --sup_smt_interval                      50000
% 1.20/0.98  
% 1.20/0.98  ------ Superposition Simplification Setup
% 1.20/0.98  
% 1.20/0.98  --sup_indices_passive                   []
% 1.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.20/0.98  --sup_full_bw                           [BwDemod]
% 1.20/0.98  --sup_immed_triv                        [TrivRules]
% 1.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.20/0.98  --sup_immed_bw_main                     []
% 1.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.20/0.98  
% 1.20/0.98  ------ Combination Options
% 1.20/0.98  
% 1.20/0.98  --comb_res_mult                         3
% 1.20/0.98  --comb_sup_mult                         2
% 1.20/0.98  --comb_inst_mult                        10
% 1.20/0.98  
% 1.20/0.98  ------ Debug Options
% 1.20/0.98  
% 1.20/0.98  --dbg_backtrace                         false
% 1.20/0.98  --dbg_dump_prop_clauses                 false
% 1.20/0.98  --dbg_dump_prop_clauses_file            -
% 1.20/0.98  --dbg_out_stat                          false
% 1.20/0.98  
% 1.20/0.98  
% 1.20/0.98  
% 1.20/0.98  
% 1.20/0.98  ------ Proving...
% 1.20/0.98  
% 1.20/0.98  
% 1.20/0.98  % SZS status Theorem for theBenchmark.p
% 1.20/0.98  
% 1.20/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.20/0.98  
% 1.20/0.98  fof(f16,conjecture,(
% 1.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f17,negated_conjecture,(
% 1.20/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.20/0.98    inference(negated_conjecture,[],[f16])).
% 1.20/0.98  
% 1.20/0.98  fof(f31,plain,(
% 1.20/0.98    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.20/0.98    inference(ennf_transformation,[],[f17])).
% 1.20/0.98  
% 1.20/0.98  fof(f32,plain,(
% 1.20/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.20/0.98    inference(flattening,[],[f31])).
% 1.20/0.98  
% 1.20/0.98  fof(f33,plain,(
% 1.20/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.20/0.98    inference(nnf_transformation,[],[f32])).
% 1.20/0.98  
% 1.20/0.98  fof(f34,plain,(
% 1.20/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.20/0.98    inference(flattening,[],[f33])).
% 1.20/0.98  
% 1.20/0.98  fof(f37,plain,(
% 1.20/0.98    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.20/0.98    introduced(choice_axiom,[])).
% 1.20/0.98  
% 1.20/0.98  fof(f36,plain,(
% 1.20/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 1.20/0.98    introduced(choice_axiom,[])).
% 1.20/0.98  
% 1.20/0.98  fof(f35,plain,(
% 1.20/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.20/0.98    introduced(choice_axiom,[])).
% 1.20/0.98  
% 1.20/0.98  fof(f38,plain,(
% 1.20/0.98    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).
% 1.20/0.98  
% 1.20/0.98  fof(f57,plain,(
% 1.20/0.98    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.20/0.98    inference(cnf_transformation,[],[f38])).
% 1.20/0.98  
% 1.20/0.98  fof(f12,axiom,(
% 1.20/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f24,plain,(
% 1.20/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.20/0.98    inference(ennf_transformation,[],[f12])).
% 1.20/0.98  
% 1.20/0.98  fof(f50,plain,(
% 1.20/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.20/0.98    inference(cnf_transformation,[],[f24])).
% 1.20/0.98  
% 1.20/0.98  fof(f11,axiom,(
% 1.20/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f23,plain,(
% 1.20/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.20/0.98    inference(ennf_transformation,[],[f11])).
% 1.20/0.98  
% 1.20/0.98  fof(f49,plain,(
% 1.20/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.20/0.98    inference(cnf_transformation,[],[f23])).
% 1.20/0.98  
% 1.20/0.98  fof(f56,plain,(
% 1.20/0.98    l1_pre_topc(sK0)),
% 1.20/0.98    inference(cnf_transformation,[],[f38])).
% 1.20/0.98  
% 1.20/0.98  fof(f4,axiom,(
% 1.20/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f42,plain,(
% 1.20/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.20/0.98    inference(cnf_transformation,[],[f4])).
% 1.20/0.98  
% 1.20/0.98  fof(f6,axiom,(
% 1.20/0.98    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f44,plain,(
% 1.20/0.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.20/0.98    inference(cnf_transformation,[],[f6])).
% 1.20/0.98  
% 1.20/0.98  fof(f3,axiom,(
% 1.20/0.98    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f41,plain,(
% 1.20/0.98    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.20/0.98    inference(cnf_transformation,[],[f3])).
% 1.20/0.98  
% 1.20/0.98  fof(f63,plain,(
% 1.20/0.98    k1_xboole_0 = sK2),
% 1.20/0.98    inference(cnf_transformation,[],[f38])).
% 1.20/0.98  
% 1.20/0.98  fof(f64,plain,(
% 1.20/0.98    ( ! [X0] : (k1_subset_1(X0) = sK2) )),
% 1.20/0.98    inference(definition_unfolding,[],[f41,f63])).
% 1.20/0.98  
% 1.20/0.98  fof(f65,plain,(
% 1.20/0.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,sK2)) )),
% 1.20/0.98    inference(definition_unfolding,[],[f44,f64])).
% 1.20/0.98  
% 1.20/0.98  fof(f68,plain,(
% 1.20/0.98    ( ! [X0] : (k3_subset_1(X0,sK2) = X0) )),
% 1.20/0.98    inference(definition_unfolding,[],[f42,f65])).
% 1.20/0.98  
% 1.20/0.98  fof(f8,axiom,(
% 1.20/0.98    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f18,plain,(
% 1.20/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.20/0.98    inference(ennf_transformation,[],[f8])).
% 1.20/0.98  
% 1.20/0.98  fof(f19,plain,(
% 1.20/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.20/0.98    inference(flattening,[],[f18])).
% 1.20/0.98  
% 1.20/0.98  fof(f46,plain,(
% 1.20/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 1.20/0.98    inference(cnf_transformation,[],[f19])).
% 1.20/0.98  
% 1.20/0.98  fof(f71,plain,(
% 1.20/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK2 = X0) )),
% 1.20/0.98    inference(definition_unfolding,[],[f46,f63])).
% 1.20/0.98  
% 1.20/0.98  fof(f7,axiom,(
% 1.20/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f45,plain,(
% 1.20/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.20/0.98    inference(cnf_transformation,[],[f7])).
% 1.20/0.98  
% 1.20/0.98  fof(f70,plain,(
% 1.20/0.98    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 1.20/0.98    inference(definition_unfolding,[],[f45,f63])).
% 1.20/0.98  
% 1.20/0.98  fof(f2,axiom,(
% 1.20/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f40,plain,(
% 1.20/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.20/0.98    inference(cnf_transformation,[],[f2])).
% 1.20/0.98  
% 1.20/0.98  fof(f67,plain,(
% 1.20/0.98    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 1.20/0.98    inference(definition_unfolding,[],[f40,f63])).
% 1.20/0.98  
% 1.20/0.98  fof(f10,axiom,(
% 1.20/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f22,plain,(
% 1.20/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.20/0.98    inference(ennf_transformation,[],[f10])).
% 1.20/0.98  
% 1.20/0.98  fof(f48,plain,(
% 1.20/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.20/0.98    inference(cnf_transformation,[],[f22])).
% 1.20/0.98  
% 1.20/0.98  fof(f1,axiom,(
% 1.20/0.98    v1_xboole_0(k1_xboole_0)),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f39,plain,(
% 1.20/0.98    v1_xboole_0(k1_xboole_0)),
% 1.20/0.98    inference(cnf_transformation,[],[f1])).
% 1.20/0.98  
% 1.20/0.98  fof(f66,plain,(
% 1.20/0.98    v1_xboole_0(sK2)),
% 1.20/0.98    inference(definition_unfolding,[],[f39,f63])).
% 1.20/0.98  
% 1.20/0.98  fof(f13,axiom,(
% 1.20/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f25,plain,(
% 1.20/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.20/0.98    inference(ennf_transformation,[],[f13])).
% 1.20/0.98  
% 1.20/0.98  fof(f26,plain,(
% 1.20/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.20/0.98    inference(flattening,[],[f25])).
% 1.20/0.98  
% 1.20/0.98  fof(f51,plain,(
% 1.20/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.20/0.98    inference(cnf_transformation,[],[f26])).
% 1.20/0.98  
% 1.20/0.98  fof(f54,plain,(
% 1.20/0.98    ~v2_struct_0(sK0)),
% 1.20/0.98    inference(cnf_transformation,[],[f38])).
% 1.20/0.98  
% 1.20/0.98  fof(f62,plain,(
% 1.20/0.98    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.20/0.98    inference(cnf_transformation,[],[f38])).
% 1.20/0.98  
% 1.20/0.98  fof(f14,axiom,(
% 1.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f27,plain,(
% 1.20/0.98    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.20/0.98    inference(ennf_transformation,[],[f14])).
% 1.20/0.98  
% 1.20/0.98  fof(f28,plain,(
% 1.20/0.98    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.20/0.98    inference(flattening,[],[f27])).
% 1.20/0.98  
% 1.20/0.98  fof(f52,plain,(
% 1.20/0.98    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.20/0.98    inference(cnf_transformation,[],[f28])).
% 1.20/0.98  
% 1.20/0.98  fof(f55,plain,(
% 1.20/0.98    v2_pre_topc(sK0)),
% 1.20/0.98    inference(cnf_transformation,[],[f38])).
% 1.20/0.98  
% 1.20/0.98  fof(f15,axiom,(
% 1.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f29,plain,(
% 1.20/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.20/0.98    inference(ennf_transformation,[],[f15])).
% 1.20/0.98  
% 1.20/0.98  fof(f30,plain,(
% 1.20/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.20/0.98    inference(flattening,[],[f29])).
% 1.20/0.98  
% 1.20/0.98  fof(f53,plain,(
% 1.20/0.98    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.20/0.98    inference(cnf_transformation,[],[f30])).
% 1.20/0.98  
% 1.20/0.98  fof(f5,axiom,(
% 1.20/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.20/0.98  
% 1.20/0.98  fof(f43,plain,(
% 1.20/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.20/0.98    inference(cnf_transformation,[],[f5])).
% 1.20/0.98  
% 1.20/0.98  fof(f69,plain,(
% 1.20/0.98    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))) )),
% 1.20/0.98    inference(definition_unfolding,[],[f43,f65])).
% 1.20/0.98  
% 1.20/0.98  cnf(c_18,negated_conjecture,
% 1.20/0.98      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 1.20/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_561,plain,
% 1.20/0.98      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 1.20/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_9,plain,
% 1.20/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.20/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_8,plain,
% 1.20/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.20/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_281,plain,
% 1.20/0.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.20/0.98      inference(resolution,[status(thm)],[c_9,c_8]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_19,negated_conjecture,
% 1.20/0.98      ( l1_pre_topc(sK0) ),
% 1.20/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_321,plain,
% 1.20/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.20/0.98      inference(resolution_lifted,[status(thm)],[c_281,c_19]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_322,plain,
% 1.20/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.20/0.98      inference(unflattening,[status(thm)],[c_321]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_576,plain,
% 1.20/0.98      ( m1_subset_1(sK1,k2_struct_0(sK0)) = iProver_top ),
% 1.20/0.98      inference(light_normalisation,[status(thm)],[c_561,c_322]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_2,negated_conjecture,
% 1.20/0.98      ( k3_subset_1(X0,sK2) = X0 ),
% 1.20/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_5,negated_conjecture,
% 1.20/0.98      ( r2_hidden(X0,X1)
% 1.20/0.98      | r2_hidden(X0,k3_subset_1(X2,X1))
% 1.20/0.98      | ~ m1_subset_1(X0,X2)
% 1.20/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.20/0.98      | sK2 = X2 ),
% 1.20/0.98      inference(cnf_transformation,[],[f71]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_564,plain,
% 1.20/0.98      ( sK2 = X0
% 1.20/0.98      | r2_hidden(X1,X2) = iProver_top
% 1.20/0.98      | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top
% 1.20/0.98      | m1_subset_1(X1,X0) != iProver_top
% 1.20/0.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.20/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_769,plain,
% 1.20/0.98      ( sK2 = X0
% 1.20/0.98      | r2_hidden(X1,X0) = iProver_top
% 1.20/0.98      | r2_hidden(X1,sK2) = iProver_top
% 1.20/0.98      | m1_subset_1(X1,X0) != iProver_top
% 1.20/0.98      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.20/0.98      inference(superposition,[status(thm)],[c_2,c_564]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_4,negated_conjecture,
% 1.20/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
% 1.20/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_42,plain,
% 1.20/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
% 1.20/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_774,plain,
% 1.20/0.98      ( m1_subset_1(X1,X0) != iProver_top
% 1.20/0.98      | r2_hidden(X1,sK2) = iProver_top
% 1.20/0.98      | r2_hidden(X1,X0) = iProver_top
% 1.20/0.98      | sK2 = X0 ),
% 1.20/0.98      inference(global_propositional_subsumption,
% 1.20/0.98                [status(thm)],
% 1.20/0.98                [c_769,c_42]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_775,plain,
% 1.20/0.98      ( sK2 = X0
% 1.20/0.98      | r2_hidden(X1,X0) = iProver_top
% 1.20/0.98      | r2_hidden(X1,sK2) = iProver_top
% 1.20/0.98      | m1_subset_1(X1,X0) != iProver_top ),
% 1.20/0.98      inference(renaming,[status(thm)],[c_774]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_943,plain,
% 1.20/0.98      ( k2_struct_0(sK0) = sK2
% 1.20/0.98      | r2_hidden(sK1,k2_struct_0(sK0)) = iProver_top
% 1.20/0.98      | r2_hidden(sK1,sK2) = iProver_top ),
% 1.20/0.98      inference(superposition,[status(thm)],[c_576,c_775]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_1,negated_conjecture,
% 1.20/0.98      ( r1_tarski(sK2,X0) ),
% 1.20/0.98      inference(cnf_transformation,[],[f67]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_7,plain,
% 1.20/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.20/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_239,plain,
% 1.20/0.98      ( ~ r2_hidden(X0,X1) | X0 != X2 | sK2 != X1 ),
% 1.20/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_240,plain,
% 1.20/0.98      ( ~ r2_hidden(X0,sK2) ),
% 1.20/0.98      inference(unflattening,[status(thm)],[c_239]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_911,plain,
% 1.20/0.98      ( ~ r2_hidden(sK1,sK2) ),
% 1.20/0.98      inference(instantiation,[status(thm)],[c_240]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_912,plain,
% 1.20/0.98      ( r2_hidden(sK1,sK2) != iProver_top ),
% 1.20/0.98      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_0,negated_conjecture,
% 1.20/0.98      ( v1_xboole_0(sK2) ),
% 1.20/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_10,plain,
% 1.20/0.98      ( v2_struct_0(X0)
% 1.20/0.98      | ~ l1_struct_0(X0)
% 1.20/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.20/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_254,plain,
% 1.20/0.98      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != sK2 ),
% 1.20/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_21,negated_conjecture,
% 1.20/0.98      ( ~ v2_struct_0(sK0) ),
% 1.20/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_272,plain,
% 1.20/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != sK2 | sK0 != X0 ),
% 1.20/0.98      inference(resolution_lifted,[status(thm)],[c_254,c_21]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_273,plain,
% 1.20/0.98      ( ~ l1_struct_0(sK0) | u1_struct_0(sK0) != sK2 ),
% 1.20/0.98      inference(unflattening,[status(thm)],[c_272]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_63,plain,
% 1.20/0.98      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.20/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_256,plain,
% 1.20/0.98      ( v2_struct_0(sK0) | ~ l1_struct_0(sK0) | u1_struct_0(sK0) != sK2 ),
% 1.20/0.98      inference(instantiation,[status(thm)],[c_254]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_275,plain,
% 1.20/0.98      ( u1_struct_0(sK0) != sK2 ),
% 1.20/0.98      inference(global_propositional_subsumption,
% 1.20/0.98                [status(thm)],
% 1.20/0.98                [c_273,c_21,c_19,c_63,c_256]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_569,plain,
% 1.20/0.98      ( k2_struct_0(sK0) != sK2 ),
% 1.20/0.98      inference(light_normalisation,[status(thm)],[c_275,c_322]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_13,negated_conjecture,
% 1.20/0.98      ( ~ v3_pre_topc(X0,sK0)
% 1.20/0.98      | ~ v4_pre_topc(X0,sK0)
% 1.20/0.98      | r2_hidden(X0,sK2)
% 1.20/0.98      | ~ r2_hidden(sK1,X0)
% 1.20/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.20/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_250,plain,
% 1.20/0.98      ( ~ v3_pre_topc(X0,sK0)
% 1.20/0.98      | ~ v4_pre_topc(X0,sK0)
% 1.20/0.98      | ~ r2_hidden(sK1,X0)
% 1.20/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.20/0.98      inference(backward_subsumption_resolution,
% 1.20/0.98                [status(thm)],
% 1.20/0.98                [c_240,c_13]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_11,plain,
% 1.20/0.98      ( v4_pre_topc(k2_struct_0(X0),X0)
% 1.20/0.98      | ~ v2_pre_topc(X0)
% 1.20/0.98      | ~ l1_pre_topc(X0) ),
% 1.20/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_20,negated_conjecture,
% 1.20/0.98      ( v2_pre_topc(sK0) ),
% 1.20/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_306,plain,
% 1.20/0.98      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 1.20/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_307,plain,
% 1.20/0.98      ( v4_pre_topc(k2_struct_0(sK0),sK0) | ~ l1_pre_topc(sK0) ),
% 1.20/0.98      inference(unflattening,[status(thm)],[c_306]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_57,plain,
% 1.20/0.98      ( v4_pre_topc(k2_struct_0(sK0),sK0)
% 1.20/0.98      | ~ v2_pre_topc(sK0)
% 1.20/0.98      | ~ l1_pre_topc(sK0) ),
% 1.20/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_309,plain,
% 1.20/0.98      ( v4_pre_topc(k2_struct_0(sK0),sK0) ),
% 1.20/0.98      inference(global_propositional_subsumption,
% 1.20/0.98                [status(thm)],
% 1.20/0.98                [c_307,c_20,c_19,c_57]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_327,plain,
% 1.20/0.98      ( ~ v3_pre_topc(X0,sK0)
% 1.20/0.98      | ~ r2_hidden(sK1,X0)
% 1.20/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.20/0.98      | k2_struct_0(sK0) != X0
% 1.20/0.98      | sK0 != sK0 ),
% 1.20/0.98      inference(resolution_lifted,[status(thm)],[c_250,c_309]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_328,plain,
% 1.20/0.98      ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
% 1.20/0.98      | ~ r2_hidden(sK1,k2_struct_0(sK0))
% 1.20/0.98      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.20/0.98      inference(unflattening,[status(thm)],[c_327]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_12,plain,
% 1.20/0.98      ( v3_pre_topc(k2_struct_0(X0),X0)
% 1.20/0.98      | ~ v2_pre_topc(X0)
% 1.20/0.98      | ~ l1_pre_topc(X0) ),
% 1.20/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_54,plain,
% 1.20/0.98      ( v3_pre_topc(k2_struct_0(sK0),sK0)
% 1.20/0.98      | ~ v2_pre_topc(sK0)
% 1.20/0.98      | ~ l1_pre_topc(sK0) ),
% 1.20/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_330,plain,
% 1.20/0.98      ( ~ r2_hidden(sK1,k2_struct_0(sK0))
% 1.20/0.98      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.20/0.98      inference(global_propositional_subsumption,
% 1.20/0.98                [status(thm)],
% 1.20/0.98                [c_328,c_20,c_19,c_54]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_559,plain,
% 1.20/0.98      ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
% 1.20/0.98      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.20/0.98      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_585,plain,
% 1.20/0.98      ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
% 1.20/0.98      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.20/0.98      inference(light_normalisation,[status(thm)],[c_559,c_322]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_3,negated_conjecture,
% 1.20/0.98      ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
% 1.20/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_566,plain,
% 1.20/0.98      ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) = iProver_top ),
% 1.20/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_582,plain,
% 1.20/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.20/0.98      inference(light_normalisation,[status(thm)],[c_566,c_2]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(c_588,plain,
% 1.20/0.98      ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top ),
% 1.20/0.98      inference(forward_subsumption_resolution,
% 1.20/0.98                [status(thm)],
% 1.20/0.98                [c_585,c_582]) ).
% 1.20/0.98  
% 1.20/0.98  cnf(contradiction,plain,
% 1.20/0.98      ( $false ),
% 1.20/0.98      inference(minisat,[status(thm)],[c_943,c_912,c_569,c_588]) ).
% 1.20/0.98  
% 1.20/0.98  
% 1.20/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.20/0.98  
% 1.20/0.98  ------                               Statistics
% 1.20/0.98  
% 1.20/0.98  ------ General
% 1.20/0.98  
% 1.20/0.98  abstr_ref_over_cycles:                  0
% 1.20/0.98  abstr_ref_under_cycles:                 0
% 1.20/0.98  gc_basic_clause_elim:                   0
% 1.20/0.98  forced_gc_time:                         0
% 1.20/0.98  parsing_time:                           0.01
% 1.20/0.98  unif_index_cands_time:                  0.
% 1.20/0.98  unif_index_add_time:                    0.
% 1.20/0.98  orderings_time:                         0.
% 1.20/0.98  out_proof_time:                         0.012
% 1.20/0.98  total_time:                             0.066
% 1.20/0.98  num_of_symbols:                         48
% 1.20/0.98  num_of_terms:                           883
% 1.20/0.98  
% 1.20/0.98  ------ Preprocessing
% 1.20/0.98  
% 1.20/0.98  num_of_splits:                          0
% 1.20/0.98  num_of_split_atoms:                     0
% 1.20/0.98  num_of_reused_defs:                     0
% 1.20/0.98  num_eq_ax_congr_red:                    6
% 1.20/0.98  num_of_sem_filtered_clauses:            1
% 1.20/0.98  num_of_subtypes:                        0
% 1.20/0.98  monotx_restored_types:                  0
% 1.20/0.98  sat_num_of_epr_types:                   0
% 1.20/0.98  sat_num_of_non_cyclic_types:            0
% 1.20/0.98  sat_guarded_non_collapsed_types:        0
% 1.20/0.98  num_pure_diseq_elim:                    0
% 1.20/0.98  simp_replaced_by:                       0
% 1.20/0.98  res_preprocessed:                       72
% 1.20/0.98  prep_upred:                             0
% 1.20/0.98  prep_unflattend:                        7
% 1.20/0.98  smt_new_axioms:                         0
% 1.20/0.98  pred_elim_cands:                        2
% 1.20/0.98  pred_elim:                              8
% 1.20/0.98  pred_elim_cl:                           11
% 1.20/0.98  pred_elim_cycles:                       10
% 1.20/0.98  merged_defs:                            0
% 1.20/0.98  merged_defs_ncl:                        0
% 1.20/0.98  bin_hyper_res:                          0
% 1.20/0.98  prep_cycles:                            4
% 1.20/0.98  pred_elim_time:                         0.002
% 1.20/0.98  splitting_time:                         0.
% 1.20/0.98  sem_filter_time:                        0.
% 1.20/0.98  monotx_time:                            0.
% 1.20/0.98  subtype_inf_time:                       0.
% 1.20/0.98  
% 1.20/0.98  ------ Problem properties
% 1.20/0.98  
% 1.20/0.98  clauses:                                11
% 1.20/0.98  conjectures:                            6
% 1.20/0.98  epr:                                    1
% 1.20/0.98  horn:                                   10
% 1.20/0.98  ground:                                 5
% 1.20/0.98  unary:                                  8
% 1.20/0.98  binary:                                 1
% 1.20/0.98  lits:                                   18
% 1.20/0.98  lits_eq:                                4
% 1.20/0.98  fd_pure:                                0
% 1.20/0.98  fd_pseudo:                              0
% 1.20/0.98  fd_cond:                                1
% 1.20/0.98  fd_pseudo_cond:                         0
% 1.20/0.98  ac_symbols:                             0
% 1.20/0.98  
% 1.20/0.98  ------ Propositional Solver
% 1.20/0.98  
% 1.20/0.98  prop_solver_calls:                      24
% 1.20/0.98  prop_fast_solver_calls:                 329
% 1.20/0.98  smt_solver_calls:                       0
% 1.20/0.98  smt_fast_solver_calls:                  0
% 1.20/0.98  prop_num_of_clauses:                    310
% 1.20/0.98  prop_preprocess_simplified:             1799
% 1.20/0.98  prop_fo_subsumed:                       5
% 1.20/0.98  prop_solver_time:                       0.
% 1.20/0.98  smt_solver_time:                        0.
% 1.20/0.98  smt_fast_solver_time:                   0.
% 1.20/0.98  prop_fast_solver_time:                  0.
% 1.20/0.98  prop_unsat_core_time:                   0.
% 1.20/0.98  
% 1.20/0.98  ------ QBF
% 1.20/0.98  
% 1.20/0.98  qbf_q_res:                              0
% 1.20/0.98  qbf_num_tautologies:                    0
% 1.20/0.98  qbf_prep_cycles:                        0
% 1.20/0.98  
% 1.20/0.98  ------ BMC1
% 1.20/0.98  
% 1.20/0.98  bmc1_current_bound:                     -1
% 1.20/0.98  bmc1_last_solved_bound:                 -1
% 1.20/0.98  bmc1_unsat_core_size:                   -1
% 1.20/0.98  bmc1_unsat_core_parents_size:           -1
% 1.20/0.98  bmc1_merge_next_fun:                    0
% 1.20/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.20/0.98  
% 1.20/0.98  ------ Instantiation
% 1.20/0.98  
% 1.20/0.98  inst_num_of_clauses:                    75
% 1.20/0.98  inst_num_in_passive:                    19
% 1.20/0.98  inst_num_in_active:                     47
% 1.20/0.98  inst_num_in_unprocessed:                10
% 1.20/0.98  inst_num_of_loops:                      50
% 1.20/0.98  inst_num_of_learning_restarts:          0
% 1.20/0.98  inst_num_moves_active_passive:          1
% 1.20/0.98  inst_lit_activity:                      0
% 1.20/0.98  inst_lit_activity_moves:                0
% 1.20/0.98  inst_num_tautologies:                   0
% 1.20/0.98  inst_num_prop_implied:                  0
% 1.20/0.98  inst_num_existing_simplified:           0
% 1.20/0.98  inst_num_eq_res_simplified:             0
% 1.20/0.98  inst_num_child_elim:                    0
% 1.20/0.98  inst_num_of_dismatching_blockings:      11
% 1.20/0.98  inst_num_of_non_proper_insts:           53
% 1.20/0.98  inst_num_of_duplicates:                 0
% 1.20/0.98  inst_inst_num_from_inst_to_res:         0
% 1.20/0.98  inst_dismatching_checking_time:         0.
% 1.20/0.98  
% 1.20/0.98  ------ Resolution
% 1.20/0.98  
% 1.20/0.98  res_num_of_clauses:                     0
% 1.20/0.98  res_num_in_passive:                     0
% 1.20/0.98  res_num_in_active:                      0
% 1.20/0.98  res_num_of_loops:                       76
% 1.20/0.98  res_forward_subset_subsumed:            4
% 1.20/0.98  res_backward_subset_subsumed:           3
% 1.20/0.98  res_forward_subsumed:                   0
% 1.20/0.98  res_backward_subsumed:                  2
% 1.20/0.98  res_forward_subsumption_resolution:     0
% 1.20/0.98  res_backward_subsumption_resolution:    1
% 1.20/0.98  res_clause_to_clause_subsumption:       28
% 1.20/0.98  res_orphan_elimination:                 0
% 1.20/0.98  res_tautology_del:                      4
% 1.20/0.98  res_num_eq_res_simplified:              0
% 1.20/0.98  res_num_sel_changes:                    0
% 1.20/0.98  res_moves_from_active_to_pass:          0
% 1.20/0.98  
% 1.20/0.98  ------ Superposition
% 1.20/0.98  
% 1.20/0.98  sup_time_total:                         0.
% 1.20/0.98  sup_time_generating:                    0.
% 1.20/0.98  sup_time_sim_full:                      0.
% 1.20/0.98  sup_time_sim_immed:                     0.
% 1.20/0.98  
% 1.20/0.98  sup_num_of_clauses:                     15
% 1.20/0.98  sup_num_in_active:                      10
% 1.20/0.98  sup_num_in_passive:                     5
% 1.20/0.98  sup_num_of_loops:                       9
% 1.20/0.98  sup_fw_superposition:                   5
% 1.20/0.98  sup_bw_superposition:                   1
% 1.20/0.98  sup_immediate_simplified:               1
% 1.20/0.98  sup_given_eliminated:                   0
% 1.20/0.98  comparisons_done:                       0
% 1.20/0.98  comparisons_avoided:                    0
% 1.20/0.98  
% 1.20/0.98  ------ Simplifications
% 1.20/0.98  
% 1.20/0.98  
% 1.20/0.98  sim_fw_subset_subsumed:                 1
% 1.20/0.98  sim_bw_subset_subsumed:                 0
% 1.20/0.98  sim_fw_subsumed:                        1
% 1.20/0.98  sim_bw_subsumed:                        0
% 1.20/0.98  sim_fw_subsumption_res:                 1
% 1.20/0.98  sim_bw_subsumption_res:                 0
% 1.20/0.98  sim_tautology_del:                      0
% 1.20/0.98  sim_eq_tautology_del:                   0
% 1.20/0.98  sim_eq_res_simp:                        0
% 1.20/0.98  sim_fw_demodulated:                     0
% 1.20/0.98  sim_bw_demodulated:                     0
% 1.20/0.98  sim_light_normalised:                   5
% 1.20/0.98  sim_joinable_taut:                      0
% 1.20/0.98  sim_joinable_simp:                      0
% 1.20/0.98  sim_ac_normalised:                      0
% 1.20/0.98  sim_smt_subsumption:                    0
% 1.20/0.98  
%------------------------------------------------------------------------------
