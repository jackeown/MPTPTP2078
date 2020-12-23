%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:42 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 433 expanded)
%              Number of clauses        :   61 (  89 expanded)
%              Number of leaves         :   21 ( 121 expanded)
%              Depth                    :   19
%              Number of atoms          :  414 (4178 expanded)
%              Number of equality atoms :  100 ( 416 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).

fof(f64,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f73,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,sK2)) = sK2 ),
    inference(definition_unfolding,[],[f45,f70,f53,f70])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f10,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(definition_unfolding,[],[f46,f70])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f72,plain,(
    v1_xboole_0(sK2) ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_608,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_299,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_12,c_11])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_339,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_299,c_22])).

cnf(c_340,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_626,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_608,c_340])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_612,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_614,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1066,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2))) = k3_subset_1(X0,sK2) ),
    inference(superposition,[status(thm)],[c_612,c_614])).

cnf(c_1,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X0,sK2)) = sK2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3,negated_conjecture,
    ( k5_xboole_0(X0,sK2) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1071,plain,
    ( k3_subset_1(X0,sK2) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1066,c_1,c_3])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sK2 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_611,plain,
    ( sK2 = X0
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1198,plain,
    ( sK2 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_611])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1203,plain,
    ( m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | sK2 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1198,c_45])).

cnf(c_1204,plain,
    ( sK2 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1203])).

cnf(c_2,negated_conjecture,
    ( r1_tarski(sK2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_257,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_258,plain,
    ( ~ r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_607,plain,
    ( r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_1213,plain,
    ( sK2 = X0
    | r2_hidden(X1,X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1204,c_607])).

cnf(c_1218,plain,
    ( k2_struct_0(sK0) = sK2
    | r2_hidden(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_626,c_1213])).

cnf(c_16,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | r2_hidden(X0,sK2)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_268,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_258,c_16])).

cnf(c_14,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_324,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_325,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_58,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_327,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_23,c_22,c_58])).

cnf(c_345,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_268,c_327])).

cnf(c_346,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_15,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_55,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_348,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_23,c_22,c_55])).

cnf(c_606,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_637,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_606,c_340])).

cnf(c_6,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_613,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_613,c_4])).

cnf(c_640,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_637,c_633])).

cnf(c_0,negated_conjecture,
    ( v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_272,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_290,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != sK2
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_272,c_24])).

cnf(c_291,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) != sK2 ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_64,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_274,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) != sK2 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_293,plain,
    ( u1_struct_0(sK0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_24,c_22,c_64,c_274])).

cnf(c_619,plain,
    ( k2_struct_0(sK0) != sK2 ),
    inference(light_normalisation,[status(thm)],[c_293,c_340])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1218,c_640,c_619])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.90/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/0.99  
% 1.90/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.90/0.99  
% 1.90/0.99  ------  iProver source info
% 1.90/0.99  
% 1.90/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.90/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.90/0.99  git: non_committed_changes: false
% 1.90/0.99  git: last_make_outside_of_git: false
% 1.90/0.99  
% 1.90/0.99  ------ 
% 1.90/0.99  
% 1.90/0.99  ------ Input Options
% 1.90/0.99  
% 1.90/0.99  --out_options                           all
% 1.90/0.99  --tptp_safe_out                         true
% 1.90/0.99  --problem_path                          ""
% 1.90/0.99  --include_path                          ""
% 1.90/0.99  --clausifier                            res/vclausify_rel
% 1.90/0.99  --clausifier_options                    --mode clausify
% 1.90/0.99  --stdin                                 false
% 1.90/0.99  --stats_out                             all
% 1.90/0.99  
% 1.90/0.99  ------ General Options
% 1.90/0.99  
% 1.90/0.99  --fof                                   false
% 1.90/0.99  --time_out_real                         305.
% 1.90/0.99  --time_out_virtual                      -1.
% 1.90/0.99  --symbol_type_check                     false
% 1.90/0.99  --clausify_out                          false
% 1.90/0.99  --sig_cnt_out                           false
% 1.90/0.99  --trig_cnt_out                          false
% 1.90/0.99  --trig_cnt_out_tolerance                1.
% 1.90/0.99  --trig_cnt_out_sk_spl                   false
% 1.90/0.99  --abstr_cl_out                          false
% 1.90/0.99  
% 1.90/0.99  ------ Global Options
% 1.90/0.99  
% 1.90/0.99  --schedule                              default
% 1.90/0.99  --add_important_lit                     false
% 1.90/0.99  --prop_solver_per_cl                    1000
% 1.90/0.99  --min_unsat_core                        false
% 1.90/0.99  --soft_assumptions                      false
% 1.90/0.99  --soft_lemma_size                       3
% 1.90/0.99  --prop_impl_unit_size                   0
% 1.90/0.99  --prop_impl_unit                        []
% 1.90/0.99  --share_sel_clauses                     true
% 1.90/0.99  --reset_solvers                         false
% 1.90/0.99  --bc_imp_inh                            [conj_cone]
% 1.90/0.99  --conj_cone_tolerance                   3.
% 1.90/0.99  --extra_neg_conj                        none
% 1.90/0.99  --large_theory_mode                     true
% 1.90/0.99  --prolific_symb_bound                   200
% 1.90/0.99  --lt_threshold                          2000
% 1.90/0.99  --clause_weak_htbl                      true
% 1.90/0.99  --gc_record_bc_elim                     false
% 1.90/0.99  
% 1.90/0.99  ------ Preprocessing Options
% 1.90/0.99  
% 1.90/0.99  --preprocessing_flag                    true
% 1.90/0.99  --time_out_prep_mult                    0.1
% 1.90/0.99  --splitting_mode                        input
% 1.90/0.99  --splitting_grd                         true
% 1.90/0.99  --splitting_cvd                         false
% 1.90/0.99  --splitting_cvd_svl                     false
% 1.90/0.99  --splitting_nvd                         32
% 1.90/0.99  --sub_typing                            true
% 1.90/0.99  --prep_gs_sim                           true
% 1.90/0.99  --prep_unflatten                        true
% 1.90/0.99  --prep_res_sim                          true
% 1.90/0.99  --prep_upred                            true
% 1.90/0.99  --prep_sem_filter                       exhaustive
% 1.90/0.99  --prep_sem_filter_out                   false
% 1.90/0.99  --pred_elim                             true
% 1.90/0.99  --res_sim_input                         true
% 1.90/0.99  --eq_ax_congr_red                       true
% 1.90/0.99  --pure_diseq_elim                       true
% 1.90/0.99  --brand_transform                       false
% 1.90/0.99  --non_eq_to_eq                          false
% 1.90/0.99  --prep_def_merge                        true
% 1.90/0.99  --prep_def_merge_prop_impl              false
% 1.90/0.99  --prep_def_merge_mbd                    true
% 1.90/0.99  --prep_def_merge_tr_red                 false
% 1.90/0.99  --prep_def_merge_tr_cl                  false
% 1.90/0.99  --smt_preprocessing                     true
% 1.90/0.99  --smt_ac_axioms                         fast
% 1.90/0.99  --preprocessed_out                      false
% 1.90/0.99  --preprocessed_stats                    false
% 1.90/0.99  
% 1.90/0.99  ------ Abstraction refinement Options
% 1.90/0.99  
% 1.90/0.99  --abstr_ref                             []
% 1.90/0.99  --abstr_ref_prep                        false
% 1.90/0.99  --abstr_ref_until_sat                   false
% 1.90/0.99  --abstr_ref_sig_restrict                funpre
% 1.90/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/0.99  --abstr_ref_under                       []
% 1.90/0.99  
% 1.90/0.99  ------ SAT Options
% 1.90/0.99  
% 1.90/0.99  --sat_mode                              false
% 1.90/0.99  --sat_fm_restart_options                ""
% 1.90/0.99  --sat_gr_def                            false
% 1.90/0.99  --sat_epr_types                         true
% 1.90/0.99  --sat_non_cyclic_types                  false
% 1.90/0.99  --sat_finite_models                     false
% 1.90/0.99  --sat_fm_lemmas                         false
% 1.90/0.99  --sat_fm_prep                           false
% 1.90/0.99  --sat_fm_uc_incr                        true
% 1.90/0.99  --sat_out_model                         small
% 1.90/0.99  --sat_out_clauses                       false
% 1.90/0.99  
% 1.90/0.99  ------ QBF Options
% 1.90/0.99  
% 1.90/0.99  --qbf_mode                              false
% 1.90/0.99  --qbf_elim_univ                         false
% 1.90/0.99  --qbf_dom_inst                          none
% 1.90/0.99  --qbf_dom_pre_inst                      false
% 1.90/0.99  --qbf_sk_in                             false
% 1.90/0.99  --qbf_pred_elim                         true
% 1.90/0.99  --qbf_split                             512
% 1.90/0.99  
% 1.90/0.99  ------ BMC1 Options
% 1.90/0.99  
% 1.90/0.99  --bmc1_incremental                      false
% 1.90/0.99  --bmc1_axioms                           reachable_all
% 1.90/0.99  --bmc1_min_bound                        0
% 1.90/0.99  --bmc1_max_bound                        -1
% 1.90/0.99  --bmc1_max_bound_default                -1
% 1.90/0.99  --bmc1_symbol_reachability              true
% 1.90/0.99  --bmc1_property_lemmas                  false
% 1.90/0.99  --bmc1_k_induction                      false
% 1.90/0.99  --bmc1_non_equiv_states                 false
% 1.90/0.99  --bmc1_deadlock                         false
% 1.90/0.99  --bmc1_ucm                              false
% 1.90/0.99  --bmc1_add_unsat_core                   none
% 1.90/0.99  --bmc1_unsat_core_children              false
% 1.90/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/0.99  --bmc1_out_stat                         full
% 1.90/0.99  --bmc1_ground_init                      false
% 1.90/0.99  --bmc1_pre_inst_next_state              false
% 1.90/0.99  --bmc1_pre_inst_state                   false
% 1.90/0.99  --bmc1_pre_inst_reach_state             false
% 1.90/0.99  --bmc1_out_unsat_core                   false
% 1.90/0.99  --bmc1_aig_witness_out                  false
% 1.90/0.99  --bmc1_verbose                          false
% 1.90/0.99  --bmc1_dump_clauses_tptp                false
% 1.90/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.90/0.99  --bmc1_dump_file                        -
% 1.90/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.90/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.90/0.99  --bmc1_ucm_extend_mode                  1
% 1.90/0.99  --bmc1_ucm_init_mode                    2
% 1.90/0.99  --bmc1_ucm_cone_mode                    none
% 1.90/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.90/0.99  --bmc1_ucm_relax_model                  4
% 1.90/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.90/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/0.99  --bmc1_ucm_layered_model                none
% 1.90/0.99  --bmc1_ucm_max_lemma_size               10
% 1.90/0.99  
% 1.90/0.99  ------ AIG Options
% 1.90/0.99  
% 1.90/0.99  --aig_mode                              false
% 1.90/0.99  
% 1.90/0.99  ------ Instantiation Options
% 1.90/0.99  
% 1.90/0.99  --instantiation_flag                    true
% 1.90/0.99  --inst_sos_flag                         false
% 1.90/0.99  --inst_sos_phase                        true
% 1.90/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/0.99  --inst_lit_sel_side                     num_symb
% 1.90/0.99  --inst_solver_per_active                1400
% 1.90/0.99  --inst_solver_calls_frac                1.
% 1.90/0.99  --inst_passive_queue_type               priority_queues
% 1.90/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/0.99  --inst_passive_queues_freq              [25;2]
% 1.90/0.99  --inst_dismatching                      true
% 1.90/0.99  --inst_eager_unprocessed_to_passive     true
% 1.90/0.99  --inst_prop_sim_given                   true
% 1.90/0.99  --inst_prop_sim_new                     false
% 1.90/0.99  --inst_subs_new                         false
% 1.90/0.99  --inst_eq_res_simp                      false
% 1.90/0.99  --inst_subs_given                       false
% 1.90/0.99  --inst_orphan_elimination               true
% 1.90/0.99  --inst_learning_loop_flag               true
% 1.90/0.99  --inst_learning_start                   3000
% 1.90/0.99  --inst_learning_factor                  2
% 1.90/0.99  --inst_start_prop_sim_after_learn       3
% 1.90/0.99  --inst_sel_renew                        solver
% 1.90/0.99  --inst_lit_activity_flag                true
% 1.90/0.99  --inst_restr_to_given                   false
% 1.90/0.99  --inst_activity_threshold               500
% 1.90/0.99  --inst_out_proof                        true
% 1.90/0.99  
% 1.90/0.99  ------ Resolution Options
% 1.90/0.99  
% 1.90/0.99  --resolution_flag                       true
% 1.90/0.99  --res_lit_sel                           adaptive
% 1.90/0.99  --res_lit_sel_side                      none
% 1.90/0.99  --res_ordering                          kbo
% 1.90/0.99  --res_to_prop_solver                    active
% 1.90/0.99  --res_prop_simpl_new                    false
% 1.90/0.99  --res_prop_simpl_given                  true
% 1.90/0.99  --res_passive_queue_type                priority_queues
% 1.90/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/0.99  --res_passive_queues_freq               [15;5]
% 1.90/0.99  --res_forward_subs                      full
% 1.90/0.99  --res_backward_subs                     full
% 1.90/0.99  --res_forward_subs_resolution           true
% 1.90/0.99  --res_backward_subs_resolution          true
% 1.90/0.99  --res_orphan_elimination                true
% 1.90/0.99  --res_time_limit                        2.
% 1.90/0.99  --res_out_proof                         true
% 1.90/0.99  
% 1.90/0.99  ------ Superposition Options
% 1.90/0.99  
% 1.90/0.99  --superposition_flag                    true
% 1.90/0.99  --sup_passive_queue_type                priority_queues
% 1.90/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.90/0.99  --demod_completeness_check              fast
% 1.90/0.99  --demod_use_ground                      true
% 1.90/0.99  --sup_to_prop_solver                    passive
% 1.90/0.99  --sup_prop_simpl_new                    true
% 1.90/0.99  --sup_prop_simpl_given                  true
% 1.90/0.99  --sup_fun_splitting                     false
% 1.90/0.99  --sup_smt_interval                      50000
% 1.90/0.99  
% 1.90/0.99  ------ Superposition Simplification Setup
% 1.90/0.99  
% 1.90/0.99  --sup_indices_passive                   []
% 1.90/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.99  --sup_full_bw                           [BwDemod]
% 1.90/0.99  --sup_immed_triv                        [TrivRules]
% 1.90/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.99  --sup_immed_bw_main                     []
% 1.90/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.99  
% 1.90/0.99  ------ Combination Options
% 1.90/0.99  
% 1.90/0.99  --comb_res_mult                         3
% 1.90/0.99  --comb_sup_mult                         2
% 1.90/0.99  --comb_inst_mult                        10
% 1.90/0.99  
% 1.90/0.99  ------ Debug Options
% 1.90/0.99  
% 1.90/0.99  --dbg_backtrace                         false
% 1.90/0.99  --dbg_dump_prop_clauses                 false
% 1.90/0.99  --dbg_dump_prop_clauses_file            -
% 1.90/0.99  --dbg_out_stat                          false
% 1.90/0.99  ------ Parsing...
% 1.90/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.90/0.99  
% 1.90/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.90/0.99  
% 1.90/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.90/0.99  
% 1.90/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.90/0.99  ------ Proving...
% 1.90/0.99  ------ Problem Properties 
% 1.90/0.99  
% 1.90/0.99  
% 1.90/0.99  clauses                                 14
% 1.90/0.99  conjectures                             6
% 1.90/0.99  EPR                                     1
% 1.90/0.99  Horn                                    13
% 1.90/0.99  unary                                   10
% 1.90/0.99  binary                                  2
% 1.90/0.99  lits                                    22
% 1.90/0.99  lits eq                                 7
% 1.90/0.99  fd_pure                                 0
% 1.90/0.99  fd_pseudo                               0
% 1.90/0.99  fd_cond                                 1
% 1.90/0.99  fd_pseudo_cond                          0
% 1.90/0.99  AC symbols                              0
% 1.90/0.99  
% 1.90/0.99  ------ Schedule dynamic 5 is on 
% 1.90/0.99  
% 1.90/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.90/0.99  
% 1.90/0.99  
% 1.90/0.99  ------ 
% 1.90/0.99  Current options:
% 1.90/0.99  ------ 
% 1.90/0.99  
% 1.90/0.99  ------ Input Options
% 1.90/0.99  
% 1.90/0.99  --out_options                           all
% 1.90/0.99  --tptp_safe_out                         true
% 1.90/0.99  --problem_path                          ""
% 1.90/0.99  --include_path                          ""
% 1.90/0.99  --clausifier                            res/vclausify_rel
% 1.90/0.99  --clausifier_options                    --mode clausify
% 1.90/0.99  --stdin                                 false
% 1.90/0.99  --stats_out                             all
% 1.90/0.99  
% 1.90/0.99  ------ General Options
% 1.90/0.99  
% 1.90/0.99  --fof                                   false
% 1.90/0.99  --time_out_real                         305.
% 1.90/0.99  --time_out_virtual                      -1.
% 1.90/0.99  --symbol_type_check                     false
% 1.90/0.99  --clausify_out                          false
% 1.90/0.99  --sig_cnt_out                           false
% 1.90/0.99  --trig_cnt_out                          false
% 1.90/0.99  --trig_cnt_out_tolerance                1.
% 1.90/0.99  --trig_cnt_out_sk_spl                   false
% 1.90/0.99  --abstr_cl_out                          false
% 1.90/0.99  
% 1.90/0.99  ------ Global Options
% 1.90/0.99  
% 1.90/0.99  --schedule                              default
% 1.90/0.99  --add_important_lit                     false
% 1.90/0.99  --prop_solver_per_cl                    1000
% 1.90/0.99  --min_unsat_core                        false
% 1.90/0.99  --soft_assumptions                      false
% 1.90/0.99  --soft_lemma_size                       3
% 1.90/0.99  --prop_impl_unit_size                   0
% 1.90/0.99  --prop_impl_unit                        []
% 1.90/0.99  --share_sel_clauses                     true
% 1.90/0.99  --reset_solvers                         false
% 1.90/0.99  --bc_imp_inh                            [conj_cone]
% 1.90/0.99  --conj_cone_tolerance                   3.
% 1.90/0.99  --extra_neg_conj                        none
% 1.90/0.99  --large_theory_mode                     true
% 1.90/0.99  --prolific_symb_bound                   200
% 1.90/0.99  --lt_threshold                          2000
% 1.90/0.99  --clause_weak_htbl                      true
% 1.90/0.99  --gc_record_bc_elim                     false
% 1.90/0.99  
% 1.90/0.99  ------ Preprocessing Options
% 1.90/0.99  
% 1.90/0.99  --preprocessing_flag                    true
% 1.90/0.99  --time_out_prep_mult                    0.1
% 1.90/0.99  --splitting_mode                        input
% 1.90/0.99  --splitting_grd                         true
% 1.90/0.99  --splitting_cvd                         false
% 1.90/0.99  --splitting_cvd_svl                     false
% 1.90/0.99  --splitting_nvd                         32
% 1.90/0.99  --sub_typing                            true
% 1.90/0.99  --prep_gs_sim                           true
% 1.90/0.99  --prep_unflatten                        true
% 1.90/0.99  --prep_res_sim                          true
% 1.90/0.99  --prep_upred                            true
% 1.90/0.99  --prep_sem_filter                       exhaustive
% 1.90/0.99  --prep_sem_filter_out                   false
% 1.90/0.99  --pred_elim                             true
% 1.90/0.99  --res_sim_input                         true
% 1.90/0.99  --eq_ax_congr_red                       true
% 1.90/0.99  --pure_diseq_elim                       true
% 1.90/0.99  --brand_transform                       false
% 1.90/0.99  --non_eq_to_eq                          false
% 1.90/0.99  --prep_def_merge                        true
% 1.90/0.99  --prep_def_merge_prop_impl              false
% 1.90/0.99  --prep_def_merge_mbd                    true
% 1.90/0.99  --prep_def_merge_tr_red                 false
% 1.90/0.99  --prep_def_merge_tr_cl                  false
% 1.90/0.99  --smt_preprocessing                     true
% 1.90/0.99  --smt_ac_axioms                         fast
% 1.90/0.99  --preprocessed_out                      false
% 1.90/0.99  --preprocessed_stats                    false
% 1.90/0.99  
% 1.90/0.99  ------ Abstraction refinement Options
% 1.90/0.99  
% 1.90/0.99  --abstr_ref                             []
% 1.90/0.99  --abstr_ref_prep                        false
% 1.90/0.99  --abstr_ref_until_sat                   false
% 1.90/0.99  --abstr_ref_sig_restrict                funpre
% 1.90/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/0.99  --abstr_ref_under                       []
% 1.90/0.99  
% 1.90/0.99  ------ SAT Options
% 1.90/0.99  
% 1.90/0.99  --sat_mode                              false
% 1.90/0.99  --sat_fm_restart_options                ""
% 1.90/0.99  --sat_gr_def                            false
% 1.90/0.99  --sat_epr_types                         true
% 1.90/0.99  --sat_non_cyclic_types                  false
% 1.90/0.99  --sat_finite_models                     false
% 1.90/0.99  --sat_fm_lemmas                         false
% 1.90/0.99  --sat_fm_prep                           false
% 1.90/0.99  --sat_fm_uc_incr                        true
% 1.90/0.99  --sat_out_model                         small
% 1.90/0.99  --sat_out_clauses                       false
% 1.90/0.99  
% 1.90/0.99  ------ QBF Options
% 1.90/0.99  
% 1.90/0.99  --qbf_mode                              false
% 1.90/0.99  --qbf_elim_univ                         false
% 1.90/0.99  --qbf_dom_inst                          none
% 1.90/0.99  --qbf_dom_pre_inst                      false
% 1.90/0.99  --qbf_sk_in                             false
% 1.90/0.99  --qbf_pred_elim                         true
% 1.90/0.99  --qbf_split                             512
% 1.90/0.99  
% 1.90/0.99  ------ BMC1 Options
% 1.90/0.99  
% 1.90/0.99  --bmc1_incremental                      false
% 1.90/0.99  --bmc1_axioms                           reachable_all
% 1.90/0.99  --bmc1_min_bound                        0
% 1.90/0.99  --bmc1_max_bound                        -1
% 1.90/0.99  --bmc1_max_bound_default                -1
% 1.90/0.99  --bmc1_symbol_reachability              true
% 1.90/0.99  --bmc1_property_lemmas                  false
% 1.90/0.99  --bmc1_k_induction                      false
% 1.90/0.99  --bmc1_non_equiv_states                 false
% 1.90/0.99  --bmc1_deadlock                         false
% 1.90/0.99  --bmc1_ucm                              false
% 1.90/0.99  --bmc1_add_unsat_core                   none
% 1.90/0.99  --bmc1_unsat_core_children              false
% 1.90/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/0.99  --bmc1_out_stat                         full
% 1.90/0.99  --bmc1_ground_init                      false
% 1.90/0.99  --bmc1_pre_inst_next_state              false
% 1.90/0.99  --bmc1_pre_inst_state                   false
% 1.90/0.99  --bmc1_pre_inst_reach_state             false
% 1.90/0.99  --bmc1_out_unsat_core                   false
% 1.90/0.99  --bmc1_aig_witness_out                  false
% 1.90/0.99  --bmc1_verbose                          false
% 1.90/0.99  --bmc1_dump_clauses_tptp                false
% 1.90/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.90/0.99  --bmc1_dump_file                        -
% 1.90/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.90/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.90/0.99  --bmc1_ucm_extend_mode                  1
% 1.90/0.99  --bmc1_ucm_init_mode                    2
% 1.90/0.99  --bmc1_ucm_cone_mode                    none
% 1.90/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.90/0.99  --bmc1_ucm_relax_model                  4
% 1.90/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.90/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/0.99  --bmc1_ucm_layered_model                none
% 1.90/0.99  --bmc1_ucm_max_lemma_size               10
% 1.90/0.99  
% 1.90/0.99  ------ AIG Options
% 1.90/0.99  
% 1.90/0.99  --aig_mode                              false
% 1.90/0.99  
% 1.90/0.99  ------ Instantiation Options
% 1.90/0.99  
% 1.90/0.99  --instantiation_flag                    true
% 1.90/0.99  --inst_sos_flag                         false
% 1.90/0.99  --inst_sos_phase                        true
% 1.90/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/0.99  --inst_lit_sel_side                     none
% 1.90/0.99  --inst_solver_per_active                1400
% 1.90/0.99  --inst_solver_calls_frac                1.
% 1.90/0.99  --inst_passive_queue_type               priority_queues
% 1.90/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/0.99  --inst_passive_queues_freq              [25;2]
% 1.90/0.99  --inst_dismatching                      true
% 1.90/0.99  --inst_eager_unprocessed_to_passive     true
% 1.90/0.99  --inst_prop_sim_given                   true
% 1.90/0.99  --inst_prop_sim_new                     false
% 1.90/0.99  --inst_subs_new                         false
% 1.90/0.99  --inst_eq_res_simp                      false
% 1.90/0.99  --inst_subs_given                       false
% 1.90/0.99  --inst_orphan_elimination               true
% 1.90/0.99  --inst_learning_loop_flag               true
% 1.90/0.99  --inst_learning_start                   3000
% 1.90/0.99  --inst_learning_factor                  2
% 1.90/0.99  --inst_start_prop_sim_after_learn       3
% 1.90/0.99  --inst_sel_renew                        solver
% 1.90/0.99  --inst_lit_activity_flag                true
% 1.90/0.99  --inst_restr_to_given                   false
% 1.90/0.99  --inst_activity_threshold               500
% 1.90/0.99  --inst_out_proof                        true
% 1.90/0.99  
% 1.90/0.99  ------ Resolution Options
% 1.90/0.99  
% 1.90/0.99  --resolution_flag                       false
% 1.90/0.99  --res_lit_sel                           adaptive
% 1.90/0.99  --res_lit_sel_side                      none
% 1.90/0.99  --res_ordering                          kbo
% 1.90/0.99  --res_to_prop_solver                    active
% 1.90/0.99  --res_prop_simpl_new                    false
% 1.90/0.99  --res_prop_simpl_given                  true
% 1.90/0.99  --res_passive_queue_type                priority_queues
% 1.90/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/0.99  --res_passive_queues_freq               [15;5]
% 1.90/0.99  --res_forward_subs                      full
% 1.90/0.99  --res_backward_subs                     full
% 1.90/0.99  --res_forward_subs_resolution           true
% 1.90/0.99  --res_backward_subs_resolution          true
% 1.90/0.99  --res_orphan_elimination                true
% 1.90/0.99  --res_time_limit                        2.
% 1.90/0.99  --res_out_proof                         true
% 1.90/0.99  
% 1.90/0.99  ------ Superposition Options
% 1.90/0.99  
% 1.90/0.99  --superposition_flag                    true
% 1.90/0.99  --sup_passive_queue_type                priority_queues
% 1.90/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.90/0.99  --demod_completeness_check              fast
% 1.90/0.99  --demod_use_ground                      true
% 1.90/0.99  --sup_to_prop_solver                    passive
% 1.90/0.99  --sup_prop_simpl_new                    true
% 1.90/0.99  --sup_prop_simpl_given                  true
% 1.90/0.99  --sup_fun_splitting                     false
% 1.90/0.99  --sup_smt_interval                      50000
% 1.90/0.99  
% 1.90/0.99  ------ Superposition Simplification Setup
% 1.90/0.99  
% 1.90/0.99  --sup_indices_passive                   []
% 1.90/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.99  --sup_full_bw                           [BwDemod]
% 1.90/0.99  --sup_immed_triv                        [TrivRules]
% 1.90/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.99  --sup_immed_bw_main                     []
% 1.90/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.99  
% 1.90/0.99  ------ Combination Options
% 1.90/0.99  
% 1.90/0.99  --comb_res_mult                         3
% 1.90/0.99  --comb_sup_mult                         2
% 1.90/0.99  --comb_inst_mult                        10
% 1.90/0.99  
% 1.90/0.99  ------ Debug Options
% 1.90/0.99  
% 1.90/0.99  --dbg_backtrace                         false
% 1.90/0.99  --dbg_dump_prop_clauses                 false
% 1.90/0.99  --dbg_dump_prop_clauses_file            -
% 1.90/0.99  --dbg_out_stat                          false
% 1.90/0.99  
% 1.90/0.99  
% 1.90/0.99  
% 1.90/0.99  
% 1.90/0.99  ------ Proving...
% 1.90/0.99  
% 1.90/0.99  
% 1.90/0.99  % SZS status Theorem for theBenchmark.p
% 1.90/0.99  
% 1.90/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.90/0.99  
% 1.90/0.99  fof(f19,conjecture,(
% 1.90/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f20,negated_conjecture,(
% 1.90/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.90/0.99    inference(negated_conjecture,[],[f19])).
% 1.90/0.99  
% 1.90/0.99  fof(f35,plain,(
% 1.90/0.99    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.90/0.99    inference(ennf_transformation,[],[f20])).
% 1.90/0.99  
% 1.90/0.99  fof(f36,plain,(
% 1.90/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.90/0.99    inference(flattening,[],[f35])).
% 1.90/0.99  
% 1.90/0.99  fof(f37,plain,(
% 1.90/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.90/0.99    inference(nnf_transformation,[],[f36])).
% 1.90/0.99  
% 1.90/0.99  fof(f38,plain,(
% 1.90/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.90/0.99    inference(flattening,[],[f37])).
% 1.90/0.99  
% 1.90/0.99  fof(f41,plain,(
% 1.90/0.99    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.90/0.99    introduced(choice_axiom,[])).
% 1.90/0.99  
% 1.90/0.99  fof(f40,plain,(
% 1.90/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 1.90/0.99    introduced(choice_axiom,[])).
% 1.90/0.99  
% 1.90/0.99  fof(f39,plain,(
% 1.90/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.90/0.99    introduced(choice_axiom,[])).
% 1.90/0.99  
% 1.90/0.99  fof(f42,plain,(
% 1.90/0.99    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.90/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).
% 1.90/0.99  
% 1.90/0.99  fof(f64,plain,(
% 1.90/0.99    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.90/0.99    inference(cnf_transformation,[],[f42])).
% 1.90/0.99  
% 1.90/0.99  fof(f15,axiom,(
% 1.90/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f28,plain,(
% 1.90/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.90/0.99    inference(ennf_transformation,[],[f15])).
% 1.90/0.99  
% 1.90/0.99  fof(f57,plain,(
% 1.90/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.90/0.99    inference(cnf_transformation,[],[f28])).
% 1.90/0.99  
% 1.90/0.99  fof(f14,axiom,(
% 1.90/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f27,plain,(
% 1.90/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.90/0.99    inference(ennf_transformation,[],[f14])).
% 1.90/0.99  
% 1.90/0.99  fof(f56,plain,(
% 1.90/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.90/0.99    inference(cnf_transformation,[],[f27])).
% 1.90/0.99  
% 1.90/0.99  fof(f63,plain,(
% 1.90/0.99    l1_pre_topc(sK0)),
% 1.90/0.99    inference(cnf_transformation,[],[f42])).
% 1.90/0.99  
% 1.90/0.99  fof(f9,axiom,(
% 1.90/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f51,plain,(
% 1.90/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.90/0.99    inference(cnf_transformation,[],[f9])).
% 1.90/0.99  
% 1.90/0.99  fof(f70,plain,(
% 1.90/0.99    k1_xboole_0 = sK2),
% 1.90/0.99    inference(cnf_transformation,[],[f42])).
% 1.90/0.99  
% 1.90/0.99  fof(f77,plain,(
% 1.90/0.99    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 1.90/0.99    inference(definition_unfolding,[],[f51,f70])).
% 1.90/0.99  
% 1.90/0.99  fof(f7,axiom,(
% 1.90/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f21,plain,(
% 1.90/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.90/0.99    inference(ennf_transformation,[],[f7])).
% 1.90/0.99  
% 1.90/0.99  fof(f49,plain,(
% 1.90/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.90/0.99    inference(cnf_transformation,[],[f21])).
% 1.90/0.99  
% 1.90/0.99  fof(f2,axiom,(
% 1.90/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f44,plain,(
% 1.90/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.90/0.99    inference(cnf_transformation,[],[f2])).
% 1.90/0.99  
% 1.90/0.99  fof(f11,axiom,(
% 1.90/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f53,plain,(
% 1.90/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.90/0.99    inference(cnf_transformation,[],[f11])).
% 1.90/0.99  
% 1.90/0.99  fof(f71,plain,(
% 1.90/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.90/0.99    inference(definition_unfolding,[],[f44,f53])).
% 1.90/0.99  
% 1.90/0.99  fof(f76,plain,(
% 1.90/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.90/0.99    inference(definition_unfolding,[],[f49,f71])).
% 1.90/0.99  
% 1.90/0.99  fof(f3,axiom,(
% 1.90/0.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f45,plain,(
% 1.90/0.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.90/0.99    inference(cnf_transformation,[],[f3])).
% 1.90/0.99  
% 1.90/0.99  fof(f73,plain,(
% 1.90/0.99    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,sK2)) = sK2) )),
% 1.90/0.99    inference(definition_unfolding,[],[f45,f70,f53,f70])).
% 1.90/0.99  
% 1.90/0.99  fof(f5,axiom,(
% 1.90/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f47,plain,(
% 1.90/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.90/0.99    inference(cnf_transformation,[],[f5])).
% 1.90/0.99  
% 1.90/0.99  fof(f75,plain,(
% 1.90/0.99    ( ! [X0] : (k5_xboole_0(X0,sK2) = X0) )),
% 1.90/0.99    inference(definition_unfolding,[],[f47,f70])).
% 1.90/0.99  
% 1.90/0.99  fof(f10,axiom,(
% 1.90/0.99    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f22,plain,(
% 1.90/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.90/0.99    inference(ennf_transformation,[],[f10])).
% 1.90/0.99  
% 1.90/0.99  fof(f23,plain,(
% 1.90/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.90/0.99    inference(flattening,[],[f22])).
% 1.90/0.99  
% 1.90/0.99  fof(f52,plain,(
% 1.90/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 1.90/0.99    inference(cnf_transformation,[],[f23])).
% 1.90/0.99  
% 1.90/0.99  fof(f78,plain,(
% 1.90/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK2 = X0) )),
% 1.90/0.99    inference(definition_unfolding,[],[f52,f70])).
% 1.90/0.99  
% 1.90/0.99  fof(f4,axiom,(
% 1.90/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f46,plain,(
% 1.90/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.90/0.99    inference(cnf_transformation,[],[f4])).
% 1.90/0.99  
% 1.90/0.99  fof(f74,plain,(
% 1.90/0.99    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 1.90/0.99    inference(definition_unfolding,[],[f46,f70])).
% 1.90/0.99  
% 1.90/0.99  fof(f13,axiom,(
% 1.90/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f26,plain,(
% 1.90/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.90/0.99    inference(ennf_transformation,[],[f13])).
% 1.90/0.99  
% 1.90/0.99  fof(f55,plain,(
% 1.90/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.90/0.99    inference(cnf_transformation,[],[f26])).
% 1.90/0.99  
% 1.90/0.99  fof(f69,plain,(
% 1.90/0.99    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.90/0.99    inference(cnf_transformation,[],[f42])).
% 1.90/0.99  
% 1.90/0.99  fof(f17,axiom,(
% 1.90/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f31,plain,(
% 1.90/0.99    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.90/0.99    inference(ennf_transformation,[],[f17])).
% 1.90/0.99  
% 1.90/0.99  fof(f32,plain,(
% 1.90/0.99    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.90/0.99    inference(flattening,[],[f31])).
% 1.90/0.99  
% 1.90/0.99  fof(f59,plain,(
% 1.90/0.99    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.90/0.99    inference(cnf_transformation,[],[f32])).
% 1.90/0.99  
% 1.90/0.99  fof(f62,plain,(
% 1.90/0.99    v2_pre_topc(sK0)),
% 1.90/0.99    inference(cnf_transformation,[],[f42])).
% 1.90/0.99  
% 1.90/0.99  fof(f18,axiom,(
% 1.90/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f33,plain,(
% 1.90/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.90/0.99    inference(ennf_transformation,[],[f18])).
% 1.90/0.99  
% 1.90/0.99  fof(f34,plain,(
% 1.90/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.90/0.99    inference(flattening,[],[f33])).
% 1.90/0.99  
% 1.90/0.99  fof(f60,plain,(
% 1.90/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.90/0.99    inference(cnf_transformation,[],[f34])).
% 1.90/0.99  
% 1.90/0.99  fof(f8,axiom,(
% 1.90/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f50,plain,(
% 1.90/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.90/0.99    inference(cnf_transformation,[],[f8])).
% 1.90/0.99  
% 1.90/0.99  fof(f6,axiom,(
% 1.90/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f48,plain,(
% 1.90/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.90/0.99    inference(cnf_transformation,[],[f6])).
% 1.90/0.99  
% 1.90/0.99  fof(f1,axiom,(
% 1.90/0.99    v1_xboole_0(k1_xboole_0)),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f43,plain,(
% 1.90/0.99    v1_xboole_0(k1_xboole_0)),
% 1.90/0.99    inference(cnf_transformation,[],[f1])).
% 1.90/0.99  
% 1.90/0.99  fof(f72,plain,(
% 1.90/0.99    v1_xboole_0(sK2)),
% 1.90/0.99    inference(definition_unfolding,[],[f43,f70])).
% 1.90/0.99  
% 1.90/0.99  fof(f16,axiom,(
% 1.90/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.99  
% 1.90/0.99  fof(f29,plain,(
% 1.90/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.90/0.99    inference(ennf_transformation,[],[f16])).
% 1.90/0.99  
% 1.90/0.99  fof(f30,plain,(
% 1.90/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.90/0.99    inference(flattening,[],[f29])).
% 1.90/0.99  
% 1.90/0.99  fof(f58,plain,(
% 1.90/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.90/0.99    inference(cnf_transformation,[],[f30])).
% 1.90/0.99  
% 1.90/0.99  fof(f61,plain,(
% 1.90/0.99    ~v2_struct_0(sK0)),
% 1.90/0.99    inference(cnf_transformation,[],[f42])).
% 1.90/0.99  
% 1.90/0.99  cnf(c_21,negated_conjecture,
% 1.90/0.99      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 1.90/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_608,plain,
% 1.90/0.99      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 1.90/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_12,plain,
% 1.90/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.90/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_11,plain,
% 1.90/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.90/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_299,plain,
% 1.90/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.90/0.99      inference(resolution,[status(thm)],[c_12,c_11]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_22,negated_conjecture,
% 1.90/0.99      ( l1_pre_topc(sK0) ),
% 1.90/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_339,plain,
% 1.90/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.90/0.99      inference(resolution_lifted,[status(thm)],[c_299,c_22]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_340,plain,
% 1.90/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.90/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_626,plain,
% 1.90/0.99      ( m1_subset_1(sK1,k2_struct_0(sK0)) = iProver_top ),
% 1.90/0.99      inference(light_normalisation,[status(thm)],[c_608,c_340]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_7,negated_conjecture,
% 1.90/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
% 1.90/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_612,plain,
% 1.90/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
% 1.90/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.90/0.99  
% 1.90/0.99  cnf(c_5,plain,
% 1.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.90/1.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 1.90/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_614,plain,
% 1.90/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 1.90/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1066,plain,
% 1.90/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2))) = k3_subset_1(X0,sK2) ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_612,c_614]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1,negated_conjecture,
% 1.90/1.00      ( k1_setfam_1(k2_tarski(X0,sK2)) = sK2 ),
% 1.90/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_3,negated_conjecture,
% 1.90/1.00      ( k5_xboole_0(X0,sK2) = X0 ),
% 1.90/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1071,plain,
% 1.90/1.00      ( k3_subset_1(X0,sK2) = X0 ),
% 1.90/1.00      inference(light_normalisation,[status(thm)],[c_1066,c_1,c_3]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_8,negated_conjecture,
% 1.90/1.00      ( r2_hidden(X0,X1)
% 1.90/1.00      | r2_hidden(X0,k3_subset_1(X2,X1))
% 1.90/1.00      | ~ m1_subset_1(X0,X2)
% 1.90/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.90/1.00      | sK2 = X2 ),
% 1.90/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_611,plain,
% 1.90/1.00      ( sK2 = X0
% 1.90/1.00      | r2_hidden(X1,X2) = iProver_top
% 1.90/1.00      | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top
% 1.90/1.00      | m1_subset_1(X1,X0) != iProver_top
% 1.90/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1198,plain,
% 1.90/1.00      ( sK2 = X0
% 1.90/1.00      | r2_hidden(X1,X0) = iProver_top
% 1.90/1.00      | r2_hidden(X1,sK2) = iProver_top
% 1.90/1.00      | m1_subset_1(X1,X0) != iProver_top
% 1.90/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_1071,c_611]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_45,plain,
% 1.90/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1203,plain,
% 1.90/1.00      ( m1_subset_1(X1,X0) != iProver_top
% 1.90/1.00      | r2_hidden(X1,sK2) = iProver_top
% 1.90/1.00      | r2_hidden(X1,X0) = iProver_top
% 1.90/1.00      | sK2 = X0 ),
% 1.90/1.00      inference(global_propositional_subsumption,
% 1.90/1.00                [status(thm)],
% 1.90/1.00                [c_1198,c_45]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1204,plain,
% 1.90/1.00      ( sK2 = X0
% 1.90/1.00      | r2_hidden(X1,X0) = iProver_top
% 1.90/1.00      | r2_hidden(X1,sK2) = iProver_top
% 1.90/1.00      | m1_subset_1(X1,X0) != iProver_top ),
% 1.90/1.00      inference(renaming,[status(thm)],[c_1203]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2,negated_conjecture,
% 1.90/1.00      ( r1_tarski(sK2,X0) ),
% 1.90/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_10,plain,
% 1.90/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.90/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_257,plain,
% 1.90/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | sK2 != X1 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_258,plain,
% 1.90/1.00      ( ~ r2_hidden(X0,sK2) ),
% 1.90/1.00      inference(unflattening,[status(thm)],[c_257]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_607,plain,
% 1.90/1.00      ( r2_hidden(X0,sK2) != iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1213,plain,
% 1.90/1.00      ( sK2 = X0
% 1.90/1.00      | r2_hidden(X1,X0) = iProver_top
% 1.90/1.00      | m1_subset_1(X1,X0) != iProver_top ),
% 1.90/1.00      inference(forward_subsumption_resolution,
% 1.90/1.00                [status(thm)],
% 1.90/1.00                [c_1204,c_607]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1218,plain,
% 1.90/1.00      ( k2_struct_0(sK0) = sK2
% 1.90/1.00      | r2_hidden(sK1,k2_struct_0(sK0)) = iProver_top ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_626,c_1213]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_16,negated_conjecture,
% 1.90/1.00      ( ~ v3_pre_topc(X0,sK0)
% 1.90/1.00      | ~ v4_pre_topc(X0,sK0)
% 1.90/1.00      | r2_hidden(X0,sK2)
% 1.90/1.00      | ~ r2_hidden(sK1,X0)
% 1.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.90/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_268,plain,
% 1.90/1.00      ( ~ v3_pre_topc(X0,sK0)
% 1.90/1.00      | ~ v4_pre_topc(X0,sK0)
% 1.90/1.00      | ~ r2_hidden(sK1,X0)
% 1.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.90/1.00      inference(backward_subsumption_resolution,
% 1.90/1.00                [status(thm)],
% 1.90/1.00                [c_258,c_16]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_14,plain,
% 1.90/1.00      ( v4_pre_topc(k2_struct_0(X0),X0)
% 1.90/1.00      | ~ v2_pre_topc(X0)
% 1.90/1.00      | ~ l1_pre_topc(X0) ),
% 1.90/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_23,negated_conjecture,
% 1.90/1.00      ( v2_pre_topc(sK0) ),
% 1.90/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_324,plain,
% 1.90/1.00      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_325,plain,
% 1.90/1.00      ( v4_pre_topc(k2_struct_0(sK0),sK0) | ~ l1_pre_topc(sK0) ),
% 1.90/1.00      inference(unflattening,[status(thm)],[c_324]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_58,plain,
% 1.90/1.00      ( v4_pre_topc(k2_struct_0(sK0),sK0)
% 1.90/1.00      | ~ v2_pre_topc(sK0)
% 1.90/1.00      | ~ l1_pre_topc(sK0) ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_327,plain,
% 1.90/1.00      ( v4_pre_topc(k2_struct_0(sK0),sK0) ),
% 1.90/1.00      inference(global_propositional_subsumption,
% 1.90/1.00                [status(thm)],
% 1.90/1.00                [c_325,c_23,c_22,c_58]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_345,plain,
% 1.90/1.00      ( ~ v3_pre_topc(X0,sK0)
% 1.90/1.00      | ~ r2_hidden(sK1,X0)
% 1.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.90/1.00      | k2_struct_0(sK0) != X0
% 1.90/1.00      | sK0 != sK0 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_268,c_327]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_346,plain,
% 1.90/1.00      ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
% 1.90/1.00      | ~ r2_hidden(sK1,k2_struct_0(sK0))
% 1.90/1.00      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.90/1.00      inference(unflattening,[status(thm)],[c_345]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_15,plain,
% 1.90/1.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 1.90/1.00      | ~ v2_pre_topc(X0)
% 1.90/1.00      | ~ l1_pre_topc(X0) ),
% 1.90/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_55,plain,
% 1.90/1.00      ( v3_pre_topc(k2_struct_0(sK0),sK0)
% 1.90/1.00      | ~ v2_pre_topc(sK0)
% 1.90/1.00      | ~ l1_pre_topc(sK0) ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_348,plain,
% 1.90/1.00      ( ~ r2_hidden(sK1,k2_struct_0(sK0))
% 1.90/1.00      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.90/1.00      inference(global_propositional_subsumption,
% 1.90/1.00                [status(thm)],
% 1.90/1.00                [c_346,c_23,c_22,c_55]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_606,plain,
% 1.90/1.00      ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
% 1.90/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_637,plain,
% 1.90/1.00      ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top
% 1.90/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.90/1.00      inference(light_normalisation,[status(thm)],[c_606,c_340]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_6,plain,
% 1.90/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.90/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_613,plain,
% 1.90/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_4,plain,
% 1.90/1.00      ( k2_subset_1(X0) = X0 ),
% 1.90/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_633,plain,
% 1.90/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.90/1.00      inference(light_normalisation,[status(thm)],[c_613,c_4]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_640,plain,
% 1.90/1.00      ( r2_hidden(sK1,k2_struct_0(sK0)) != iProver_top ),
% 1.90/1.00      inference(forward_subsumption_resolution,
% 1.90/1.00                [status(thm)],
% 1.90/1.00                [c_637,c_633]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_0,negated_conjecture,
% 1.90/1.00      ( v1_xboole_0(sK2) ),
% 1.90/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_13,plain,
% 1.90/1.00      ( v2_struct_0(X0)
% 1.90/1.00      | ~ l1_struct_0(X0)
% 1.90/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.90/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_272,plain,
% 1.90/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != sK2 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_13]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_24,negated_conjecture,
% 1.90/1.00      ( ~ v2_struct_0(sK0) ),
% 1.90/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_290,plain,
% 1.90/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != sK2 | sK0 != X0 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_272,c_24]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_291,plain,
% 1.90/1.00      ( ~ l1_struct_0(sK0) | u1_struct_0(sK0) != sK2 ),
% 1.90/1.00      inference(unflattening,[status(thm)],[c_290]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_64,plain,
% 1.90/1.00      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_274,plain,
% 1.90/1.00      ( v2_struct_0(sK0) | ~ l1_struct_0(sK0) | u1_struct_0(sK0) != sK2 ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_272]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_293,plain,
% 1.90/1.00      ( u1_struct_0(sK0) != sK2 ),
% 1.90/1.00      inference(global_propositional_subsumption,
% 1.90/1.00                [status(thm)],
% 1.90/1.00                [c_291,c_24,c_22,c_64,c_274]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_619,plain,
% 1.90/1.00      ( k2_struct_0(sK0) != sK2 ),
% 1.90/1.00      inference(light_normalisation,[status(thm)],[c_293,c_340]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(contradiction,plain,
% 1.90/1.00      ( $false ),
% 1.90/1.00      inference(minisat,[status(thm)],[c_1218,c_640,c_619]) ).
% 1.90/1.00  
% 1.90/1.00  
% 1.90/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.90/1.00  
% 1.90/1.00  ------                               Statistics
% 1.90/1.00  
% 1.90/1.00  ------ General
% 1.90/1.00  
% 1.90/1.00  abstr_ref_over_cycles:                  0
% 1.90/1.00  abstr_ref_under_cycles:                 0
% 1.90/1.00  gc_basic_clause_elim:                   0
% 1.90/1.00  forced_gc_time:                         0
% 1.90/1.00  parsing_time:                           0.009
% 1.90/1.00  unif_index_cands_time:                  0.
% 1.90/1.00  unif_index_add_time:                    0.
% 1.90/1.00  orderings_time:                         0.
% 1.90/1.00  out_proof_time:                         0.011
% 1.90/1.00  total_time:                             0.075
% 1.90/1.00  num_of_symbols:                         52
% 1.90/1.00  num_of_terms:                           1325
% 1.90/1.00  
% 1.90/1.00  ------ Preprocessing
% 1.90/1.00  
% 1.90/1.00  num_of_splits:                          0
% 1.90/1.00  num_of_split_atoms:                     0
% 1.90/1.00  num_of_reused_defs:                     0
% 1.90/1.00  num_eq_ax_congr_red:                    18
% 1.90/1.00  num_of_sem_filtered_clauses:            1
% 1.90/1.00  num_of_subtypes:                        0
% 1.90/1.00  monotx_restored_types:                  0
% 1.90/1.00  sat_num_of_epr_types:                   0
% 1.90/1.00  sat_num_of_non_cyclic_types:            0
% 1.90/1.00  sat_guarded_non_collapsed_types:        0
% 1.90/1.00  num_pure_diseq_elim:                    0
% 1.90/1.00  simp_replaced_by:                       0
% 1.90/1.00  res_preprocessed:                       88
% 1.90/1.00  prep_upred:                             0
% 1.90/1.00  prep_unflattend:                        7
% 1.90/1.00  smt_new_axioms:                         0
% 1.90/1.00  pred_elim_cands:                        2
% 1.90/1.00  pred_elim:                              8
% 1.90/1.00  pred_elim_cl:                           11
% 1.90/1.00  pred_elim_cycles:                       10
% 1.90/1.00  merged_defs:                            0
% 1.90/1.00  merged_defs_ncl:                        0
% 1.90/1.00  bin_hyper_res:                          0
% 1.90/1.00  prep_cycles:                            4
% 1.90/1.00  pred_elim_time:                         0.002
% 1.90/1.00  splitting_time:                         0.
% 1.90/1.00  sem_filter_time:                        0.
% 1.90/1.00  monotx_time:                            0.
% 1.90/1.00  subtype_inf_time:                       0.
% 1.90/1.00  
% 1.90/1.00  ------ Problem properties
% 1.90/1.00  
% 1.90/1.00  clauses:                                14
% 1.90/1.00  conjectures:                            6
% 1.90/1.00  epr:                                    1
% 1.90/1.00  horn:                                   13
% 1.90/1.00  ground:                                 5
% 1.90/1.00  unary:                                  10
% 1.90/1.00  binary:                                 2
% 1.90/1.00  lits:                                   22
% 1.90/1.00  lits_eq:                                7
% 1.90/1.00  fd_pure:                                0
% 1.90/1.00  fd_pseudo:                              0
% 1.90/1.00  fd_cond:                                1
% 1.90/1.00  fd_pseudo_cond:                         0
% 1.90/1.00  ac_symbols:                             0
% 1.90/1.00  
% 1.90/1.00  ------ Propositional Solver
% 1.90/1.00  
% 1.90/1.00  prop_solver_calls:                      25
% 1.90/1.00  prop_fast_solver_calls:                 385
% 1.90/1.00  smt_solver_calls:                       0
% 1.90/1.00  smt_fast_solver_calls:                  0
% 1.90/1.00  prop_num_of_clauses:                    446
% 1.90/1.00  prop_preprocess_simplified:             2321
% 1.90/1.00  prop_fo_subsumed:                       5
% 1.90/1.00  prop_solver_time:                       0.
% 1.90/1.00  smt_solver_time:                        0.
% 1.90/1.00  smt_fast_solver_time:                   0.
% 1.90/1.00  prop_fast_solver_time:                  0.
% 1.90/1.00  prop_unsat_core_time:                   0.
% 1.90/1.00  
% 1.90/1.00  ------ QBF
% 1.90/1.00  
% 1.90/1.00  qbf_q_res:                              0
% 1.90/1.00  qbf_num_tautologies:                    0
% 1.90/1.00  qbf_prep_cycles:                        0
% 1.90/1.00  
% 1.90/1.00  ------ BMC1
% 1.90/1.00  
% 1.90/1.00  bmc1_current_bound:                     -1
% 1.90/1.00  bmc1_last_solved_bound:                 -1
% 1.90/1.00  bmc1_unsat_core_size:                   -1
% 1.90/1.00  bmc1_unsat_core_parents_size:           -1
% 1.90/1.00  bmc1_merge_next_fun:                    0
% 1.90/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.90/1.00  
% 1.90/1.00  ------ Instantiation
% 1.90/1.00  
% 1.90/1.00  inst_num_of_clauses:                    122
% 1.90/1.00  inst_num_in_passive:                    36
% 1.90/1.00  inst_num_in_active:                     67
% 1.90/1.00  inst_num_in_unprocessed:                20
% 1.90/1.00  inst_num_of_loops:                      70
% 1.90/1.00  inst_num_of_learning_restarts:          0
% 1.90/1.00  inst_num_moves_active_passive:          1
% 1.90/1.00  inst_lit_activity:                      0
% 1.90/1.00  inst_lit_activity_moves:                0
% 1.90/1.00  inst_num_tautologies:                   0
% 1.90/1.00  inst_num_prop_implied:                  0
% 1.90/1.00  inst_num_existing_simplified:           0
% 1.90/1.00  inst_num_eq_res_simplified:             0
% 1.90/1.00  inst_num_child_elim:                    0
% 1.90/1.00  inst_num_of_dismatching_blockings:      11
% 1.90/1.00  inst_num_of_non_proper_insts:           80
% 1.90/1.00  inst_num_of_duplicates:                 0
% 1.90/1.00  inst_inst_num_from_inst_to_res:         0
% 1.90/1.00  inst_dismatching_checking_time:         0.
% 1.90/1.00  
% 1.90/1.00  ------ Resolution
% 1.90/1.00  
% 1.90/1.00  res_num_of_clauses:                     0
% 1.90/1.00  res_num_in_passive:                     0
% 1.90/1.00  res_num_in_active:                      0
% 1.90/1.00  res_num_of_loops:                       92
% 1.90/1.00  res_forward_subset_subsumed:            5
% 1.90/1.00  res_backward_subset_subsumed:           3
% 1.90/1.00  res_forward_subsumed:                   0
% 1.90/1.00  res_backward_subsumed:                  2
% 1.90/1.00  res_forward_subsumption_resolution:     0
% 1.90/1.00  res_backward_subsumption_resolution:    1
% 1.90/1.00  res_clause_to_clause_subsumption:       35
% 1.90/1.00  res_orphan_elimination:                 0
% 1.90/1.00  res_tautology_del:                      4
% 1.90/1.00  res_num_eq_res_simplified:              0
% 1.90/1.00  res_num_sel_changes:                    0
% 1.90/1.00  res_moves_from_active_to_pass:          0
% 1.90/1.00  
% 1.90/1.00  ------ Superposition
% 1.90/1.00  
% 1.90/1.00  sup_time_total:                         0.
% 1.90/1.00  sup_time_generating:                    0.
% 1.90/1.00  sup_time_sim_full:                      0.
% 1.90/1.00  sup_time_sim_immed:                     0.
% 1.90/1.00  
% 1.90/1.00  sup_num_of_clauses:                     19
% 1.90/1.00  sup_num_in_active:                      14
% 1.90/1.00  sup_num_in_passive:                     5
% 1.90/1.00  sup_num_of_loops:                       13
% 1.90/1.00  sup_fw_superposition:                   6
% 1.90/1.00  sup_bw_superposition:                   2
% 1.90/1.00  sup_immediate_simplified:               2
% 1.90/1.00  sup_given_eliminated:                   0
% 1.90/1.00  comparisons_done:                       0
% 1.90/1.00  comparisons_avoided:                    0
% 1.90/1.00  
% 1.90/1.00  ------ Simplifications
% 1.90/1.00  
% 1.90/1.00  
% 1.90/1.00  sim_fw_subset_subsumed:                 1
% 1.90/1.00  sim_bw_subset_subsumed:                 0
% 1.90/1.00  sim_fw_subsumed:                        1
% 1.90/1.00  sim_bw_subsumed:                        0
% 1.90/1.00  sim_fw_subsumption_res:                 2
% 1.90/1.00  sim_bw_subsumption_res:                 0
% 1.90/1.00  sim_tautology_del:                      0
% 1.90/1.00  sim_eq_tautology_del:                   0
% 1.90/1.00  sim_eq_res_simp:                        0
% 1.90/1.00  sim_fw_demodulated:                     0
% 1.90/1.00  sim_bw_demodulated:                     0
% 1.90/1.00  sim_light_normalised:                   6
% 1.90/1.00  sim_joinable_taut:                      0
% 1.90/1.00  sim_joinable_simp:                      0
% 1.90/1.00  sim_ac_normalised:                      0
% 1.90/1.00  sim_smt_subsumption:                    0
% 1.90/1.00  
%------------------------------------------------------------------------------
