%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:30 EST 2020

% Result     : Theorem 19.96s
% Output     : CNFRefutation 19.96s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 448 expanded)
%              Number of clauses        :   57 ( 135 expanded)
%              Number of leaves         :   19 ( 108 expanded)
%              Depth                    :   17
%              Number of atoms          :  271 (1103 expanded)
%              Number of equality atoms :   83 ( 289 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0)
        & v2_tops_2(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0)
            & v2_tops_2(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v2_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f35,f34,f33])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v2_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_747,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_125,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_126,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_125])).

cnf(c_154,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_126])).

cnf(c_739,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_2485,plain,
    ( k9_subset_1(X0,X0,X1) = k9_subset_1(X0,X1,X0) ),
    inference(superposition,[status(thm)],[c_747,c_739])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_155,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_126])).

cnf(c_738,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_744,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2296,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_744])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_740,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_10,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_241,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_224,c_10])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_246,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_241,c_16])).

cnf(c_247,plain,
    ( ~ v2_tops_2(X0,sK0)
    | v2_tops_2(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_736,plain,
    ( v2_tops_2(X0,sK0) != iProver_top
    | v2_tops_2(X1,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_1115,plain,
    ( v2_tops_2(X0,sK0) = iProver_top
    | v2_tops_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_740,c_736])).

cnf(c_13,negated_conjecture,
    ( v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,plain,
    ( v2_tops_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1551,plain,
    ( v2_tops_2(X0,sK0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1115,c_20])).

cnf(c_2455,plain,
    ( v2_tops_2(k9_subset_1(sK1,X0,X1),sK0) = iProver_top
    | r1_tarski(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_1551])).

cnf(c_2617,plain,
    ( v2_tops_2(k9_subset_1(sK1,sK1,X0),sK0) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_2455])).

cnf(c_1427,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1428,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1427])).

cnf(c_3952,plain,
    ( v2_tops_2(k9_subset_1(sK1,sK1,X0),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2617,c_1428])).

cnf(c_3958,plain,
    ( v2_tops_2(k9_subset_1(sK1,X0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_3952])).

cnf(c_1269,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_740,c_744])).

cnf(c_2488,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) ),
    inference(superposition,[status(thm)],[c_1269,c_739])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_156,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_126])).

cnf(c_737,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_1182,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_747,c_737])).

cnf(c_1481,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) ),
    inference(superposition,[status(thm)],[c_1269,c_737])).

cnf(c_2291,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k9_subset_1(sK1,X0,sK1) ),
    inference(demodulation,[status(thm)],[c_1182,c_1481])).

cnf(c_2491,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k9_subset_1(sK1,X0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2488,c_2291])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_741,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1268,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_744])).

cnf(c_1401,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) ),
    inference(superposition,[status(thm)],[c_1268,c_737])).

cnf(c_2290,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
    inference(demodulation,[status(thm)],[c_1182,c_1401])).

cnf(c_3732,plain,
    ( k9_subset_1(sK1,sK2,sK1) = k9_subset_1(sK2,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2491,c_2290])).

cnf(c_12,negated_conjecture,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_743,plain,
    ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2879,plain,
    ( v2_tops_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2290,c_743])).

cnf(c_70959,plain,
    ( v2_tops_2(k9_subset_1(sK1,sK2,sK1),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3732,c_2879])).

cnf(c_72271,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3958,c_70959])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:48:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.96/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.96/3.00  
% 19.96/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.96/3.00  
% 19.96/3.00  ------  iProver source info
% 19.96/3.00  
% 19.96/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.96/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.96/3.00  git: non_committed_changes: false
% 19.96/3.00  git: last_make_outside_of_git: false
% 19.96/3.00  
% 19.96/3.00  ------ 
% 19.96/3.00  
% 19.96/3.00  ------ Input Options
% 19.96/3.00  
% 19.96/3.00  --out_options                           all
% 19.96/3.00  --tptp_safe_out                         true
% 19.96/3.00  --problem_path                          ""
% 19.96/3.00  --include_path                          ""
% 19.96/3.00  --clausifier                            res/vclausify_rel
% 19.96/3.00  --clausifier_options                    ""
% 19.96/3.00  --stdin                                 false
% 19.96/3.00  --stats_out                             all
% 19.96/3.00  
% 19.96/3.00  ------ General Options
% 19.96/3.00  
% 19.96/3.00  --fof                                   false
% 19.96/3.00  --time_out_real                         305.
% 19.96/3.00  --time_out_virtual                      -1.
% 19.96/3.00  --symbol_type_check                     false
% 19.96/3.00  --clausify_out                          false
% 19.96/3.00  --sig_cnt_out                           false
% 19.96/3.00  --trig_cnt_out                          false
% 19.96/3.00  --trig_cnt_out_tolerance                1.
% 19.96/3.00  --trig_cnt_out_sk_spl                   false
% 19.96/3.00  --abstr_cl_out                          false
% 19.96/3.00  
% 19.96/3.00  ------ Global Options
% 19.96/3.00  
% 19.96/3.00  --schedule                              default
% 19.96/3.00  --add_important_lit                     false
% 19.96/3.00  --prop_solver_per_cl                    1000
% 19.96/3.00  --min_unsat_core                        false
% 19.96/3.00  --soft_assumptions                      false
% 19.96/3.00  --soft_lemma_size                       3
% 19.96/3.00  --prop_impl_unit_size                   0
% 19.96/3.00  --prop_impl_unit                        []
% 19.96/3.00  --share_sel_clauses                     true
% 19.96/3.00  --reset_solvers                         false
% 19.96/3.00  --bc_imp_inh                            [conj_cone]
% 19.96/3.00  --conj_cone_tolerance                   3.
% 19.96/3.00  --extra_neg_conj                        none
% 19.96/3.00  --large_theory_mode                     true
% 19.96/3.00  --prolific_symb_bound                   200
% 19.96/3.00  --lt_threshold                          2000
% 19.96/3.00  --clause_weak_htbl                      true
% 19.96/3.00  --gc_record_bc_elim                     false
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing Options
% 19.96/3.00  
% 19.96/3.00  --preprocessing_flag                    true
% 19.96/3.00  --time_out_prep_mult                    0.1
% 19.96/3.00  --splitting_mode                        input
% 19.96/3.00  --splitting_grd                         true
% 19.96/3.00  --splitting_cvd                         false
% 19.96/3.00  --splitting_cvd_svl                     false
% 19.96/3.00  --splitting_nvd                         32
% 19.96/3.00  --sub_typing                            true
% 19.96/3.00  --prep_gs_sim                           true
% 19.96/3.00  --prep_unflatten                        true
% 19.96/3.00  --prep_res_sim                          true
% 19.96/3.00  --prep_upred                            true
% 19.96/3.00  --prep_sem_filter                       exhaustive
% 19.96/3.00  --prep_sem_filter_out                   false
% 19.96/3.00  --pred_elim                             true
% 19.96/3.00  --res_sim_input                         true
% 19.96/3.00  --eq_ax_congr_red                       true
% 19.96/3.00  --pure_diseq_elim                       true
% 19.96/3.00  --brand_transform                       false
% 19.96/3.00  --non_eq_to_eq                          false
% 19.96/3.00  --prep_def_merge                        true
% 19.96/3.00  --prep_def_merge_prop_impl              false
% 19.96/3.00  --prep_def_merge_mbd                    true
% 19.96/3.00  --prep_def_merge_tr_red                 false
% 19.96/3.00  --prep_def_merge_tr_cl                  false
% 19.96/3.00  --smt_preprocessing                     true
% 19.96/3.00  --smt_ac_axioms                         fast
% 19.96/3.00  --preprocessed_out                      false
% 19.96/3.00  --preprocessed_stats                    false
% 19.96/3.00  
% 19.96/3.00  ------ Abstraction refinement Options
% 19.96/3.00  
% 19.96/3.00  --abstr_ref                             []
% 19.96/3.00  --abstr_ref_prep                        false
% 19.96/3.00  --abstr_ref_until_sat                   false
% 19.96/3.00  --abstr_ref_sig_restrict                funpre
% 19.96/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.96/3.00  --abstr_ref_under                       []
% 19.96/3.00  
% 19.96/3.00  ------ SAT Options
% 19.96/3.00  
% 19.96/3.00  --sat_mode                              false
% 19.96/3.00  --sat_fm_restart_options                ""
% 19.96/3.00  --sat_gr_def                            false
% 19.96/3.00  --sat_epr_types                         true
% 19.96/3.00  --sat_non_cyclic_types                  false
% 19.96/3.00  --sat_finite_models                     false
% 19.96/3.00  --sat_fm_lemmas                         false
% 19.96/3.00  --sat_fm_prep                           false
% 19.96/3.00  --sat_fm_uc_incr                        true
% 19.96/3.00  --sat_out_model                         small
% 19.96/3.00  --sat_out_clauses                       false
% 19.96/3.00  
% 19.96/3.00  ------ QBF Options
% 19.96/3.00  
% 19.96/3.00  --qbf_mode                              false
% 19.96/3.00  --qbf_elim_univ                         false
% 19.96/3.00  --qbf_dom_inst                          none
% 19.96/3.00  --qbf_dom_pre_inst                      false
% 19.96/3.00  --qbf_sk_in                             false
% 19.96/3.00  --qbf_pred_elim                         true
% 19.96/3.00  --qbf_split                             512
% 19.96/3.00  
% 19.96/3.00  ------ BMC1 Options
% 19.96/3.00  
% 19.96/3.00  --bmc1_incremental                      false
% 19.96/3.00  --bmc1_axioms                           reachable_all
% 19.96/3.00  --bmc1_min_bound                        0
% 19.96/3.00  --bmc1_max_bound                        -1
% 19.96/3.00  --bmc1_max_bound_default                -1
% 19.96/3.00  --bmc1_symbol_reachability              true
% 19.96/3.00  --bmc1_property_lemmas                  false
% 19.96/3.00  --bmc1_k_induction                      false
% 19.96/3.00  --bmc1_non_equiv_states                 false
% 19.96/3.00  --bmc1_deadlock                         false
% 19.96/3.00  --bmc1_ucm                              false
% 19.96/3.00  --bmc1_add_unsat_core                   none
% 19.96/3.00  --bmc1_unsat_core_children              false
% 19.96/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.96/3.00  --bmc1_out_stat                         full
% 19.96/3.00  --bmc1_ground_init                      false
% 19.96/3.00  --bmc1_pre_inst_next_state              false
% 19.96/3.00  --bmc1_pre_inst_state                   false
% 19.96/3.00  --bmc1_pre_inst_reach_state             false
% 19.96/3.00  --bmc1_out_unsat_core                   false
% 19.96/3.00  --bmc1_aig_witness_out                  false
% 19.96/3.00  --bmc1_verbose                          false
% 19.96/3.00  --bmc1_dump_clauses_tptp                false
% 19.96/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.96/3.00  --bmc1_dump_file                        -
% 19.96/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.96/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.96/3.00  --bmc1_ucm_extend_mode                  1
% 19.96/3.00  --bmc1_ucm_init_mode                    2
% 19.96/3.00  --bmc1_ucm_cone_mode                    none
% 19.96/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.96/3.00  --bmc1_ucm_relax_model                  4
% 19.96/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.96/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.96/3.00  --bmc1_ucm_layered_model                none
% 19.96/3.00  --bmc1_ucm_max_lemma_size               10
% 19.96/3.00  
% 19.96/3.00  ------ AIG Options
% 19.96/3.00  
% 19.96/3.00  --aig_mode                              false
% 19.96/3.00  
% 19.96/3.00  ------ Instantiation Options
% 19.96/3.00  
% 19.96/3.00  --instantiation_flag                    true
% 19.96/3.00  --inst_sos_flag                         true
% 19.96/3.00  --inst_sos_phase                        true
% 19.96/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.96/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.96/3.00  --inst_lit_sel_side                     num_symb
% 19.96/3.00  --inst_solver_per_active                1400
% 19.96/3.00  --inst_solver_calls_frac                1.
% 19.96/3.00  --inst_passive_queue_type               priority_queues
% 19.96/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.96/3.00  --inst_passive_queues_freq              [25;2]
% 19.96/3.00  --inst_dismatching                      true
% 19.96/3.00  --inst_eager_unprocessed_to_passive     true
% 19.96/3.00  --inst_prop_sim_given                   true
% 19.96/3.00  --inst_prop_sim_new                     false
% 19.96/3.00  --inst_subs_new                         false
% 19.96/3.00  --inst_eq_res_simp                      false
% 19.96/3.00  --inst_subs_given                       false
% 19.96/3.00  --inst_orphan_elimination               true
% 19.96/3.00  --inst_learning_loop_flag               true
% 19.96/3.00  --inst_learning_start                   3000
% 19.96/3.00  --inst_learning_factor                  2
% 19.96/3.00  --inst_start_prop_sim_after_learn       3
% 19.96/3.00  --inst_sel_renew                        solver
% 19.96/3.00  --inst_lit_activity_flag                true
% 19.96/3.00  --inst_restr_to_given                   false
% 19.96/3.00  --inst_activity_threshold               500
% 19.96/3.00  --inst_out_proof                        true
% 19.96/3.00  
% 19.96/3.00  ------ Resolution Options
% 19.96/3.00  
% 19.96/3.00  --resolution_flag                       true
% 19.96/3.00  --res_lit_sel                           adaptive
% 19.96/3.00  --res_lit_sel_side                      none
% 19.96/3.00  --res_ordering                          kbo
% 19.96/3.00  --res_to_prop_solver                    active
% 19.96/3.00  --res_prop_simpl_new                    false
% 19.96/3.00  --res_prop_simpl_given                  true
% 19.96/3.00  --res_passive_queue_type                priority_queues
% 19.96/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.96/3.00  --res_passive_queues_freq               [15;5]
% 19.96/3.00  --res_forward_subs                      full
% 19.96/3.00  --res_backward_subs                     full
% 19.96/3.00  --res_forward_subs_resolution           true
% 19.96/3.00  --res_backward_subs_resolution          true
% 19.96/3.00  --res_orphan_elimination                true
% 19.96/3.00  --res_time_limit                        2.
% 19.96/3.00  --res_out_proof                         true
% 19.96/3.00  
% 19.96/3.00  ------ Superposition Options
% 19.96/3.00  
% 19.96/3.00  --superposition_flag                    true
% 19.96/3.00  --sup_passive_queue_type                priority_queues
% 19.96/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.96/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.96/3.00  --demod_completeness_check              fast
% 19.96/3.00  --demod_use_ground                      true
% 19.96/3.00  --sup_to_prop_solver                    passive
% 19.96/3.00  --sup_prop_simpl_new                    true
% 19.96/3.00  --sup_prop_simpl_given                  true
% 19.96/3.00  --sup_fun_splitting                     true
% 19.96/3.00  --sup_smt_interval                      50000
% 19.96/3.00  
% 19.96/3.00  ------ Superposition Simplification Setup
% 19.96/3.00  
% 19.96/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.96/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.96/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.96/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.96/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.96/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.96/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.96/3.00  --sup_immed_triv                        [TrivRules]
% 19.96/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.96/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.96/3.00  --sup_immed_bw_main                     []
% 19.96/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.96/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.96/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.96/3.00  --sup_input_bw                          []
% 19.96/3.00  
% 19.96/3.00  ------ Combination Options
% 19.96/3.00  
% 19.96/3.00  --comb_res_mult                         3
% 19.96/3.00  --comb_sup_mult                         2
% 19.96/3.00  --comb_inst_mult                        10
% 19.96/3.00  
% 19.96/3.00  ------ Debug Options
% 19.96/3.00  
% 19.96/3.00  --dbg_backtrace                         false
% 19.96/3.00  --dbg_dump_prop_clauses                 false
% 19.96/3.00  --dbg_dump_prop_clauses_file            -
% 19.96/3.00  --dbg_out_stat                          false
% 19.96/3.00  ------ Parsing...
% 19.96/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.96/3.00  ------ Proving...
% 19.96/3.00  ------ Problem Properties 
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  clauses                                 14
% 19.96/3.00  conjectures                             4
% 19.96/3.00  EPR                                     4
% 19.96/3.00  Horn                                    14
% 19.96/3.00  unary                                   5
% 19.96/3.00  binary                                  5
% 19.96/3.00  lits                                    28
% 19.96/3.00  lits eq                                 3
% 19.96/3.00  fd_pure                                 0
% 19.96/3.00  fd_pseudo                               0
% 19.96/3.00  fd_cond                                 0
% 19.96/3.00  fd_pseudo_cond                          1
% 19.96/3.00  AC symbols                              0
% 19.96/3.00  
% 19.96/3.00  ------ Schedule dynamic 5 is on 
% 19.96/3.00  
% 19.96/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ 
% 19.96/3.00  Current options:
% 19.96/3.00  ------ 
% 19.96/3.00  
% 19.96/3.00  ------ Input Options
% 19.96/3.00  
% 19.96/3.00  --out_options                           all
% 19.96/3.00  --tptp_safe_out                         true
% 19.96/3.00  --problem_path                          ""
% 19.96/3.00  --include_path                          ""
% 19.96/3.00  --clausifier                            res/vclausify_rel
% 19.96/3.00  --clausifier_options                    ""
% 19.96/3.00  --stdin                                 false
% 19.96/3.00  --stats_out                             all
% 19.96/3.00  
% 19.96/3.00  ------ General Options
% 19.96/3.00  
% 19.96/3.00  --fof                                   false
% 19.96/3.00  --time_out_real                         305.
% 19.96/3.00  --time_out_virtual                      -1.
% 19.96/3.00  --symbol_type_check                     false
% 19.96/3.00  --clausify_out                          false
% 19.96/3.00  --sig_cnt_out                           false
% 19.96/3.00  --trig_cnt_out                          false
% 19.96/3.00  --trig_cnt_out_tolerance                1.
% 19.96/3.00  --trig_cnt_out_sk_spl                   false
% 19.96/3.00  --abstr_cl_out                          false
% 19.96/3.00  
% 19.96/3.00  ------ Global Options
% 19.96/3.00  
% 19.96/3.00  --schedule                              default
% 19.96/3.00  --add_important_lit                     false
% 19.96/3.00  --prop_solver_per_cl                    1000
% 19.96/3.00  --min_unsat_core                        false
% 19.96/3.00  --soft_assumptions                      false
% 19.96/3.00  --soft_lemma_size                       3
% 19.96/3.00  --prop_impl_unit_size                   0
% 19.96/3.00  --prop_impl_unit                        []
% 19.96/3.00  --share_sel_clauses                     true
% 19.96/3.00  --reset_solvers                         false
% 19.96/3.00  --bc_imp_inh                            [conj_cone]
% 19.96/3.00  --conj_cone_tolerance                   3.
% 19.96/3.00  --extra_neg_conj                        none
% 19.96/3.00  --large_theory_mode                     true
% 19.96/3.00  --prolific_symb_bound                   200
% 19.96/3.00  --lt_threshold                          2000
% 19.96/3.00  --clause_weak_htbl                      true
% 19.96/3.00  --gc_record_bc_elim                     false
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing Options
% 19.96/3.00  
% 19.96/3.00  --preprocessing_flag                    true
% 19.96/3.00  --time_out_prep_mult                    0.1
% 19.96/3.00  --splitting_mode                        input
% 19.96/3.00  --splitting_grd                         true
% 19.96/3.00  --splitting_cvd                         false
% 19.96/3.00  --splitting_cvd_svl                     false
% 19.96/3.00  --splitting_nvd                         32
% 19.96/3.00  --sub_typing                            true
% 19.96/3.00  --prep_gs_sim                           true
% 19.96/3.00  --prep_unflatten                        true
% 19.96/3.00  --prep_res_sim                          true
% 19.96/3.00  --prep_upred                            true
% 19.96/3.00  --prep_sem_filter                       exhaustive
% 19.96/3.00  --prep_sem_filter_out                   false
% 19.96/3.00  --pred_elim                             true
% 19.96/3.00  --res_sim_input                         true
% 19.96/3.00  --eq_ax_congr_red                       true
% 19.96/3.00  --pure_diseq_elim                       true
% 19.96/3.00  --brand_transform                       false
% 19.96/3.00  --non_eq_to_eq                          false
% 19.96/3.00  --prep_def_merge                        true
% 19.96/3.00  --prep_def_merge_prop_impl              false
% 19.96/3.00  --prep_def_merge_mbd                    true
% 19.96/3.00  --prep_def_merge_tr_red                 false
% 19.96/3.00  --prep_def_merge_tr_cl                  false
% 19.96/3.00  --smt_preprocessing                     true
% 19.96/3.00  --smt_ac_axioms                         fast
% 19.96/3.00  --preprocessed_out                      false
% 19.96/3.00  --preprocessed_stats                    false
% 19.96/3.00  
% 19.96/3.00  ------ Abstraction refinement Options
% 19.96/3.00  
% 19.96/3.00  --abstr_ref                             []
% 19.96/3.00  --abstr_ref_prep                        false
% 19.96/3.00  --abstr_ref_until_sat                   false
% 19.96/3.00  --abstr_ref_sig_restrict                funpre
% 19.96/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.96/3.00  --abstr_ref_under                       []
% 19.96/3.00  
% 19.96/3.00  ------ SAT Options
% 19.96/3.00  
% 19.96/3.00  --sat_mode                              false
% 19.96/3.00  --sat_fm_restart_options                ""
% 19.96/3.00  --sat_gr_def                            false
% 19.96/3.00  --sat_epr_types                         true
% 19.96/3.00  --sat_non_cyclic_types                  false
% 19.96/3.00  --sat_finite_models                     false
% 19.96/3.00  --sat_fm_lemmas                         false
% 19.96/3.00  --sat_fm_prep                           false
% 19.96/3.00  --sat_fm_uc_incr                        true
% 19.96/3.00  --sat_out_model                         small
% 19.96/3.00  --sat_out_clauses                       false
% 19.96/3.00  
% 19.96/3.00  ------ QBF Options
% 19.96/3.00  
% 19.96/3.00  --qbf_mode                              false
% 19.96/3.00  --qbf_elim_univ                         false
% 19.96/3.00  --qbf_dom_inst                          none
% 19.96/3.00  --qbf_dom_pre_inst                      false
% 19.96/3.00  --qbf_sk_in                             false
% 19.96/3.00  --qbf_pred_elim                         true
% 19.96/3.00  --qbf_split                             512
% 19.96/3.00  
% 19.96/3.00  ------ BMC1 Options
% 19.96/3.00  
% 19.96/3.00  --bmc1_incremental                      false
% 19.96/3.00  --bmc1_axioms                           reachable_all
% 19.96/3.00  --bmc1_min_bound                        0
% 19.96/3.00  --bmc1_max_bound                        -1
% 19.96/3.00  --bmc1_max_bound_default                -1
% 19.96/3.00  --bmc1_symbol_reachability              true
% 19.96/3.00  --bmc1_property_lemmas                  false
% 19.96/3.00  --bmc1_k_induction                      false
% 19.96/3.00  --bmc1_non_equiv_states                 false
% 19.96/3.00  --bmc1_deadlock                         false
% 19.96/3.00  --bmc1_ucm                              false
% 19.96/3.00  --bmc1_add_unsat_core                   none
% 19.96/3.00  --bmc1_unsat_core_children              false
% 19.96/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.96/3.00  --bmc1_out_stat                         full
% 19.96/3.00  --bmc1_ground_init                      false
% 19.96/3.00  --bmc1_pre_inst_next_state              false
% 19.96/3.00  --bmc1_pre_inst_state                   false
% 19.96/3.00  --bmc1_pre_inst_reach_state             false
% 19.96/3.00  --bmc1_out_unsat_core                   false
% 19.96/3.00  --bmc1_aig_witness_out                  false
% 19.96/3.00  --bmc1_verbose                          false
% 19.96/3.00  --bmc1_dump_clauses_tptp                false
% 19.96/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.96/3.00  --bmc1_dump_file                        -
% 19.96/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.96/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.96/3.00  --bmc1_ucm_extend_mode                  1
% 19.96/3.00  --bmc1_ucm_init_mode                    2
% 19.96/3.00  --bmc1_ucm_cone_mode                    none
% 19.96/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.96/3.00  --bmc1_ucm_relax_model                  4
% 19.96/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.96/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.96/3.00  --bmc1_ucm_layered_model                none
% 19.96/3.00  --bmc1_ucm_max_lemma_size               10
% 19.96/3.00  
% 19.96/3.00  ------ AIG Options
% 19.96/3.00  
% 19.96/3.00  --aig_mode                              false
% 19.96/3.00  
% 19.96/3.00  ------ Instantiation Options
% 19.96/3.00  
% 19.96/3.00  --instantiation_flag                    true
% 19.96/3.00  --inst_sos_flag                         true
% 19.96/3.00  --inst_sos_phase                        true
% 19.96/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.96/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.96/3.00  --inst_lit_sel_side                     none
% 19.96/3.00  --inst_solver_per_active                1400
% 19.96/3.00  --inst_solver_calls_frac                1.
% 19.96/3.00  --inst_passive_queue_type               priority_queues
% 19.96/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.96/3.00  --inst_passive_queues_freq              [25;2]
% 19.96/3.00  --inst_dismatching                      true
% 19.96/3.00  --inst_eager_unprocessed_to_passive     true
% 19.96/3.00  --inst_prop_sim_given                   true
% 19.96/3.00  --inst_prop_sim_new                     false
% 19.96/3.00  --inst_subs_new                         false
% 19.96/3.00  --inst_eq_res_simp                      false
% 19.96/3.00  --inst_subs_given                       false
% 19.96/3.00  --inst_orphan_elimination               true
% 19.96/3.00  --inst_learning_loop_flag               true
% 19.96/3.00  --inst_learning_start                   3000
% 19.96/3.00  --inst_learning_factor                  2
% 19.96/3.00  --inst_start_prop_sim_after_learn       3
% 19.96/3.00  --inst_sel_renew                        solver
% 19.96/3.00  --inst_lit_activity_flag                true
% 19.96/3.00  --inst_restr_to_given                   false
% 19.96/3.00  --inst_activity_threshold               500
% 19.96/3.00  --inst_out_proof                        true
% 19.96/3.00  
% 19.96/3.00  ------ Resolution Options
% 19.96/3.00  
% 19.96/3.00  --resolution_flag                       false
% 19.96/3.00  --res_lit_sel                           adaptive
% 19.96/3.00  --res_lit_sel_side                      none
% 19.96/3.00  --res_ordering                          kbo
% 19.96/3.00  --res_to_prop_solver                    active
% 19.96/3.00  --res_prop_simpl_new                    false
% 19.96/3.00  --res_prop_simpl_given                  true
% 19.96/3.00  --res_passive_queue_type                priority_queues
% 19.96/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.96/3.00  --res_passive_queues_freq               [15;5]
% 19.96/3.00  --res_forward_subs                      full
% 19.96/3.00  --res_backward_subs                     full
% 19.96/3.00  --res_forward_subs_resolution           true
% 19.96/3.00  --res_backward_subs_resolution          true
% 19.96/3.00  --res_orphan_elimination                true
% 19.96/3.00  --res_time_limit                        2.
% 19.96/3.00  --res_out_proof                         true
% 19.96/3.00  
% 19.96/3.00  ------ Superposition Options
% 19.96/3.00  
% 19.96/3.00  --superposition_flag                    true
% 19.96/3.00  --sup_passive_queue_type                priority_queues
% 19.96/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.96/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.96/3.00  --demod_completeness_check              fast
% 19.96/3.00  --demod_use_ground                      true
% 19.96/3.00  --sup_to_prop_solver                    passive
% 19.96/3.00  --sup_prop_simpl_new                    true
% 19.96/3.00  --sup_prop_simpl_given                  true
% 19.96/3.00  --sup_fun_splitting                     true
% 19.96/3.00  --sup_smt_interval                      50000
% 19.96/3.00  
% 19.96/3.00  ------ Superposition Simplification Setup
% 19.96/3.00  
% 19.96/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.96/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.96/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.96/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.96/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.96/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.96/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.96/3.00  --sup_immed_triv                        [TrivRules]
% 19.96/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.96/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.96/3.00  --sup_immed_bw_main                     []
% 19.96/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.96/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.96/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.96/3.00  --sup_input_bw                          []
% 19.96/3.00  
% 19.96/3.00  ------ Combination Options
% 19.96/3.00  
% 19.96/3.00  --comb_res_mult                         3
% 19.96/3.00  --comb_sup_mult                         2
% 19.96/3.00  --comb_inst_mult                        10
% 19.96/3.00  
% 19.96/3.00  ------ Debug Options
% 19.96/3.00  
% 19.96/3.00  --dbg_backtrace                         false
% 19.96/3.00  --dbg_dump_prop_clauses                 false
% 19.96/3.00  --dbg_dump_prop_clauses_file            -
% 19.96/3.00  --dbg_out_stat                          false
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  ------ Proving...
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  % SZS status Theorem for theBenchmark.p
% 19.96/3.00  
% 19.96/3.00   Resolution empty clause
% 19.96/3.00  
% 19.96/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.96/3.00  
% 19.96/3.00  fof(f1,axiom,(
% 19.96/3.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f30,plain,(
% 19.96/3.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.96/3.00    inference(nnf_transformation,[],[f1])).
% 19.96/3.00  
% 19.96/3.00  fof(f31,plain,(
% 19.96/3.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.96/3.00    inference(flattening,[],[f30])).
% 19.96/3.00  
% 19.96/3.00  fof(f38,plain,(
% 19.96/3.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 19.96/3.00    inference(cnf_transformation,[],[f31])).
% 19.96/3.00  
% 19.96/3.00  fof(f68,plain,(
% 19.96/3.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.96/3.00    inference(equality_resolution,[],[f38])).
% 19.96/3.00  
% 19.96/3.00  fof(f9,axiom,(
% 19.96/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f21,plain,(
% 19.96/3.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.96/3.00    inference(ennf_transformation,[],[f9])).
% 19.96/3.00  
% 19.96/3.00  fof(f47,plain,(
% 19.96/3.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.96/3.00    inference(cnf_transformation,[],[f21])).
% 19.96/3.00  
% 19.96/3.00  fof(f13,axiom,(
% 19.96/3.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f32,plain,(
% 19.96/3.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.96/3.00    inference(nnf_transformation,[],[f13])).
% 19.96/3.00  
% 19.96/3.00  fof(f52,plain,(
% 19.96/3.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f32])).
% 19.96/3.00  
% 19.96/3.00  fof(f10,axiom,(
% 19.96/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f22,plain,(
% 19.96/3.00    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.96/3.00    inference(ennf_transformation,[],[f10])).
% 19.96/3.00  
% 19.96/3.00  fof(f48,plain,(
% 19.96/3.00    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.96/3.00    inference(cnf_transformation,[],[f22])).
% 19.96/3.00  
% 19.96/3.00  fof(f51,plain,(
% 19.96/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.96/3.00    inference(cnf_transformation,[],[f32])).
% 19.96/3.00  
% 19.96/3.00  fof(f17,conjecture,(
% 19.96/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f18,negated_conjecture,(
% 19.96/3.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 19.96/3.00    inference(negated_conjecture,[],[f17])).
% 19.96/3.00  
% 19.96/3.00  fof(f28,plain,(
% 19.96/3.00    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 19.96/3.00    inference(ennf_transformation,[],[f18])).
% 19.96/3.00  
% 19.96/3.00  fof(f29,plain,(
% 19.96/3.00    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 19.96/3.00    inference(flattening,[],[f28])).
% 19.96/3.00  
% 19.96/3.00  fof(f35,plain,(
% 19.96/3.00    ( ! [X0,X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0) & v2_tops_2(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 19.96/3.00    introduced(choice_axiom,[])).
% 19.96/3.00  
% 19.96/3.00  fof(f34,plain,(
% 19.96/3.00    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0) & v2_tops_2(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 19.96/3.00    introduced(choice_axiom,[])).
% 19.96/3.00  
% 19.96/3.00  fof(f33,plain,(
% 19.96/3.00    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 19.96/3.00    introduced(choice_axiom,[])).
% 19.96/3.00  
% 19.96/3.00  fof(f36,plain,(
% 19.96/3.00    ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 19.96/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f35,f34,f33])).
% 19.96/3.00  
% 19.96/3.00  fof(f57,plain,(
% 19.96/3.00    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 19.96/3.00    inference(cnf_transformation,[],[f36])).
% 19.96/3.00  
% 19.96/3.00  fof(f14,axiom,(
% 19.96/3.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f24,plain,(
% 19.96/3.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 19.96/3.00    inference(ennf_transformation,[],[f14])).
% 19.96/3.00  
% 19.96/3.00  fof(f53,plain,(
% 19.96/3.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f24])).
% 19.96/3.00  
% 19.96/3.00  fof(f16,axiom,(
% 19.96/3.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f27,plain,(
% 19.96/3.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 19.96/3.00    inference(ennf_transformation,[],[f16])).
% 19.96/3.00  
% 19.96/3.00  fof(f55,plain,(
% 19.96/3.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f27])).
% 19.96/3.00  
% 19.96/3.00  fof(f15,axiom,(
% 19.96/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f25,plain,(
% 19.96/3.00    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 19.96/3.00    inference(ennf_transformation,[],[f15])).
% 19.96/3.00  
% 19.96/3.00  fof(f26,plain,(
% 19.96/3.00    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 19.96/3.00    inference(flattening,[],[f25])).
% 19.96/3.00  
% 19.96/3.00  fof(f54,plain,(
% 19.96/3.00    ( ! [X2,X0,X1] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f26])).
% 19.96/3.00  
% 19.96/3.00  fof(f56,plain,(
% 19.96/3.00    l1_pre_topc(sK0)),
% 19.96/3.00    inference(cnf_transformation,[],[f36])).
% 19.96/3.00  
% 19.96/3.00  fof(f59,plain,(
% 19.96/3.00    v2_tops_2(sK1,sK0)),
% 19.96/3.00    inference(cnf_transformation,[],[f36])).
% 19.96/3.00  
% 19.96/3.00  fof(f11,axiom,(
% 19.96/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f23,plain,(
% 19.96/3.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.96/3.00    inference(ennf_transformation,[],[f11])).
% 19.96/3.00  
% 19.96/3.00  fof(f49,plain,(
% 19.96/3.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.96/3.00    inference(cnf_transformation,[],[f23])).
% 19.96/3.00  
% 19.96/3.00  fof(f12,axiom,(
% 19.96/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f50,plain,(
% 19.96/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.96/3.00    inference(cnf_transformation,[],[f12])).
% 19.96/3.00  
% 19.96/3.00  fof(f3,axiom,(
% 19.96/3.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f41,plain,(
% 19.96/3.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f3])).
% 19.96/3.00  
% 19.96/3.00  fof(f4,axiom,(
% 19.96/3.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f42,plain,(
% 19.96/3.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f4])).
% 19.96/3.00  
% 19.96/3.00  fof(f5,axiom,(
% 19.96/3.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f43,plain,(
% 19.96/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f5])).
% 19.96/3.00  
% 19.96/3.00  fof(f6,axiom,(
% 19.96/3.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f44,plain,(
% 19.96/3.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f6])).
% 19.96/3.00  
% 19.96/3.00  fof(f7,axiom,(
% 19.96/3.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f45,plain,(
% 19.96/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f7])).
% 19.96/3.00  
% 19.96/3.00  fof(f8,axiom,(
% 19.96/3.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 19.96/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.96/3.00  
% 19.96/3.00  fof(f46,plain,(
% 19.96/3.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 19.96/3.00    inference(cnf_transformation,[],[f8])).
% 19.96/3.00  
% 19.96/3.00  fof(f61,plain,(
% 19.96/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 19.96/3.00    inference(definition_unfolding,[],[f45,f46])).
% 19.96/3.00  
% 19.96/3.00  fof(f62,plain,(
% 19.96/3.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 19.96/3.00    inference(definition_unfolding,[],[f44,f61])).
% 19.96/3.00  
% 19.96/3.00  fof(f63,plain,(
% 19.96/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 19.96/3.00    inference(definition_unfolding,[],[f43,f62])).
% 19.96/3.00  
% 19.96/3.00  fof(f64,plain,(
% 19.96/3.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 19.96/3.00    inference(definition_unfolding,[],[f42,f63])).
% 19.96/3.00  
% 19.96/3.00  fof(f65,plain,(
% 19.96/3.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 19.96/3.00    inference(definition_unfolding,[],[f41,f64])).
% 19.96/3.00  
% 19.96/3.00  fof(f66,plain,(
% 19.96/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 19.96/3.00    inference(definition_unfolding,[],[f50,f65])).
% 19.96/3.00  
% 19.96/3.00  fof(f67,plain,(
% 19.96/3.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.96/3.00    inference(definition_unfolding,[],[f49,f66])).
% 19.96/3.00  
% 19.96/3.00  fof(f58,plain,(
% 19.96/3.00    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 19.96/3.00    inference(cnf_transformation,[],[f36])).
% 19.96/3.00  
% 19.96/3.00  fof(f60,plain,(
% 19.96/3.00    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 19.96/3.00    inference(cnf_transformation,[],[f36])).
% 19.96/3.00  
% 19.96/3.00  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f68]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_747,plain,
% 19.96/3.00      ( r1_tarski(X0,X0) = iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_4,plain,
% 19.96/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.96/3.00      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 19.96/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_7,plain,
% 19.96/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.96/3.00      inference(cnf_transformation,[],[f52]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_125,plain,
% 19.96/3.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.96/3.00      inference(prop_impl,[status(thm)],[c_7]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_126,plain,
% 19.96/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.96/3.00      inference(renaming,[status(thm)],[c_125]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_154,plain,
% 19.96/3.00      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 19.96/3.00      inference(bin_hyper_res,[status(thm)],[c_4,c_126]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_739,plain,
% 19.96/3.00      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 19.96/3.00      | r1_tarski(X1,X0) != iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_154]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_2485,plain,
% 19.96/3.00      ( k9_subset_1(X0,X0,X1) = k9_subset_1(X0,X1,X0) ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_747,c_739]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_5,plain,
% 19.96/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.96/3.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 19.96/3.00      inference(cnf_transformation,[],[f48]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_155,plain,
% 19.96/3.00      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 19.96/3.00      | ~ r1_tarski(X2,X0) ),
% 19.96/3.00      inference(bin_hyper_res,[status(thm)],[c_5,c_126]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_738,plain,
% 19.96/3.00      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 19.96/3.00      | r1_tarski(X2,X0) != iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_8,plain,
% 19.96/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.96/3.00      inference(cnf_transformation,[],[f51]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_744,plain,
% 19.96/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.96/3.00      | r1_tarski(X0,X1) = iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_2296,plain,
% 19.96/3.00      ( r1_tarski(X0,X1) != iProver_top
% 19.96/3.00      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_738,c_744]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_15,negated_conjecture,
% 19.96/3.00      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 19.96/3.00      inference(cnf_transformation,[],[f57]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_740,plain,
% 19.96/3.00      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_9,plain,
% 19.96/3.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 19.96/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_11,plain,
% 19.96/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 19.96/3.00      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 19.96/3.00      | ~ r1_tarski(X2,X0)
% 19.96/3.00      | ~ l1_struct_0(X1) ),
% 19.96/3.00      inference(cnf_transformation,[],[f55]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_223,plain,
% 19.96/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 19.96/3.00      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 19.96/3.00      | ~ r1_tarski(X2,X0)
% 19.96/3.00      | ~ l1_pre_topc(X3)
% 19.96/3.00      | X1 != X3 ),
% 19.96/3.00      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_224,plain,
% 19.96/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 19.96/3.00      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 19.96/3.00      | ~ r1_tarski(X2,X0)
% 19.96/3.00      | ~ l1_pre_topc(X1) ),
% 19.96/3.00      inference(unflattening,[status(thm)],[c_223]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_10,plain,
% 19.96/3.00      ( ~ v2_tops_2(X0,X1)
% 19.96/3.00      | v2_tops_2(X2,X1)
% 19.96/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 19.96/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 19.96/3.00      | ~ r1_tarski(X2,X0)
% 19.96/3.00      | ~ l1_pre_topc(X1) ),
% 19.96/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_241,plain,
% 19.96/3.00      ( ~ v2_tops_2(X0,X1)
% 19.96/3.00      | v2_tops_2(X2,X1)
% 19.96/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 19.96/3.00      | ~ r1_tarski(X2,X0)
% 19.96/3.00      | ~ l1_pre_topc(X1) ),
% 19.96/3.00      inference(backward_subsumption_resolution,[status(thm)],[c_224,c_10]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_16,negated_conjecture,
% 19.96/3.00      ( l1_pre_topc(sK0) ),
% 19.96/3.00      inference(cnf_transformation,[],[f56]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_246,plain,
% 19.96/3.00      ( ~ v2_tops_2(X0,X1)
% 19.96/3.00      | v2_tops_2(X2,X1)
% 19.96/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 19.96/3.00      | ~ r1_tarski(X2,X0)
% 19.96/3.00      | sK0 != X1 ),
% 19.96/3.00      inference(resolution_lifted,[status(thm)],[c_241,c_16]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_247,plain,
% 19.96/3.00      ( ~ v2_tops_2(X0,sK0)
% 19.96/3.00      | v2_tops_2(X1,sK0)
% 19.96/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 19.96/3.00      | ~ r1_tarski(X1,X0) ),
% 19.96/3.00      inference(unflattening,[status(thm)],[c_246]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_736,plain,
% 19.96/3.00      ( v2_tops_2(X0,sK0) != iProver_top
% 19.96/3.00      | v2_tops_2(X1,sK0) = iProver_top
% 19.96/3.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 19.96/3.00      | r1_tarski(X1,X0) != iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_1115,plain,
% 19.96/3.00      ( v2_tops_2(X0,sK0) = iProver_top
% 19.96/3.00      | v2_tops_2(sK1,sK0) != iProver_top
% 19.96/3.00      | r1_tarski(X0,sK1) != iProver_top ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_740,c_736]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_13,negated_conjecture,
% 19.96/3.00      ( v2_tops_2(sK1,sK0) ),
% 19.96/3.00      inference(cnf_transformation,[],[f59]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_20,plain,
% 19.96/3.00      ( v2_tops_2(sK1,sK0) = iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_1551,plain,
% 19.96/3.00      ( v2_tops_2(X0,sK0) = iProver_top | r1_tarski(X0,sK1) != iProver_top ),
% 19.96/3.00      inference(global_propositional_subsumption,[status(thm)],[c_1115,c_20]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_2455,plain,
% 19.96/3.00      ( v2_tops_2(k9_subset_1(sK1,X0,X1),sK0) = iProver_top
% 19.96/3.00      | r1_tarski(X1,sK1) != iProver_top ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_2296,c_1551]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_2617,plain,
% 19.96/3.00      ( v2_tops_2(k9_subset_1(sK1,sK1,X0),sK0) = iProver_top
% 19.96/3.00      | r1_tarski(sK1,sK1) != iProver_top ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_2485,c_2455]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_1427,plain,
% 19.96/3.00      ( r1_tarski(sK1,sK1) ),
% 19.96/3.00      inference(instantiation,[status(thm)],[c_1]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_1428,plain,
% 19.96/3.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_1427]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_3952,plain,
% 19.96/3.00      ( v2_tops_2(k9_subset_1(sK1,sK1,X0),sK0) = iProver_top ),
% 19.96/3.00      inference(global_propositional_subsumption,[status(thm)],[c_2617,c_1428]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_3958,plain,
% 19.96/3.00      ( v2_tops_2(k9_subset_1(sK1,X0,sK1),sK0) = iProver_top ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_2485,c_3952]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_1269,plain,
% 19.96/3.00      ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_740,c_744]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_2488,plain,
% 19.96/3.00      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_1269,c_739]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_6,plain,
% 19.96/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.96/3.00      | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 19.96/3.00      inference(cnf_transformation,[],[f67]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_156,plain,
% 19.96/3.00      ( ~ r1_tarski(X0,X1)
% 19.96/3.00      | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 19.96/3.00      inference(bin_hyper_res,[status(thm)],[c_6,c_126]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_737,plain,
% 19.96/3.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 19.96/3.00      | r1_tarski(X1,X2) != iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_1182,plain,
% 19.96/3.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_747,c_737]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_1481,plain,
% 19.96/3.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_1269,c_737]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_2291,plain,
% 19.96/3.00      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k9_subset_1(sK1,X0,sK1) ),
% 19.96/3.00      inference(demodulation,[status(thm)],[c_1182,c_1481]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_2491,plain,
% 19.96/3.00      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k9_subset_1(sK1,X0,sK1) ),
% 19.96/3.00      inference(light_normalisation,[status(thm)],[c_2488,c_2291]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_14,negated_conjecture,
% 19.96/3.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 19.96/3.00      inference(cnf_transformation,[],[f58]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_741,plain,
% 19.96/3.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_1268,plain,
% 19.96/3.00      ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_741,c_744]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_1401,plain,
% 19.96/3.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_1268,c_737]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_2290,plain,
% 19.96/3.00      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
% 19.96/3.00      inference(demodulation,[status(thm)],[c_1182,c_1401]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_3732,plain,
% 19.96/3.00      ( k9_subset_1(sK1,sK2,sK1) = k9_subset_1(sK2,sK1,sK2) ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_2491,c_2290]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_12,negated_conjecture,
% 19.96/3.00      ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 19.96/3.00      inference(cnf_transformation,[],[f60]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_743,plain,
% 19.96/3.00      ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
% 19.96/3.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_2879,plain,
% 19.96/3.00      ( v2_tops_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
% 19.96/3.00      inference(demodulation,[status(thm)],[c_2290,c_743]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_70959,plain,
% 19.96/3.00      ( v2_tops_2(k9_subset_1(sK1,sK2,sK1),sK0) != iProver_top ),
% 19.96/3.00      inference(demodulation,[status(thm)],[c_3732,c_2879]) ).
% 19.96/3.00  
% 19.96/3.00  cnf(c_72271,plain,
% 19.96/3.00      ( $false ),
% 19.96/3.00      inference(superposition,[status(thm)],[c_3958,c_70959]) ).
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.96/3.00  
% 19.96/3.00  ------                               Statistics
% 19.96/3.00  
% 19.96/3.00  ------ General
% 19.96/3.00  
% 19.96/3.00  abstr_ref_over_cycles:                  0
% 19.96/3.00  abstr_ref_under_cycles:                 0
% 19.96/3.00  gc_basic_clause_elim:                   0
% 19.96/3.00  forced_gc_time:                         0
% 19.96/3.00  parsing_time:                           0.01
% 19.96/3.00  unif_index_cands_time:                  0.
% 19.96/3.00  unif_index_add_time:                    0.
% 19.96/3.00  orderings_time:                         0.
% 19.96/3.00  out_proof_time:                         0.01
% 19.96/3.00  total_time:                             2.507
% 19.96/3.00  num_of_symbols:                         41
% 19.96/3.00  num_of_terms:                           62527
% 19.96/3.00  
% 19.96/3.00  ------ Preprocessing
% 19.96/3.00  
% 19.96/3.00  num_of_splits:                          0
% 19.96/3.00  num_of_split_atoms:                     0
% 19.96/3.00  num_of_reused_defs:                     0
% 19.96/3.00  num_eq_ax_congr_red:                    31
% 19.96/3.00  num_of_sem_filtered_clauses:            1
% 19.96/3.00  num_of_subtypes:                        0
% 19.96/3.00  monotx_restored_types:                  0
% 19.96/3.00  sat_num_of_epr_types:                   0
% 19.96/3.00  sat_num_of_non_cyclic_types:            0
% 19.96/3.00  sat_guarded_non_collapsed_types:        0
% 19.96/3.00  num_pure_diseq_elim:                    0
% 19.96/3.00  simp_replaced_by:                       0
% 19.96/3.00  res_preprocessed:                       75
% 19.96/3.00  prep_upred:                             0
% 19.96/3.00  prep_unflattend:                        3
% 19.96/3.00  smt_new_axioms:                         0
% 19.96/3.00  pred_elim_cands:                        3
% 19.96/3.00  pred_elim:                              2
% 19.96/3.00  pred_elim_cl:                           2
% 19.96/3.00  pred_elim_cycles:                       4
% 19.96/3.00  merged_defs:                            8
% 19.96/3.00  merged_defs_ncl:                        0
% 19.96/3.00  bin_hyper_res:                          11
% 19.96/3.00  prep_cycles:                            4
% 19.96/3.00  pred_elim_time:                         0.001
% 19.96/3.00  splitting_time:                         0.
% 19.96/3.00  sem_filter_time:                        0.
% 19.96/3.00  monotx_time:                            0.004
% 19.96/3.00  subtype_inf_time:                       0.
% 19.96/3.00  
% 19.96/3.00  ------ Problem properties
% 19.96/3.00  
% 19.96/3.00  clauses:                                14
% 19.96/3.00  conjectures:                            4
% 19.96/3.00  epr:                                    4
% 19.96/3.00  horn:                                   14
% 19.96/3.00  ground:                                 4
% 19.96/3.00  unary:                                  5
% 19.96/3.00  binary:                                 5
% 19.96/3.00  lits:                                   28
% 19.96/3.00  lits_eq:                                3
% 19.96/3.00  fd_pure:                                0
% 19.96/3.00  fd_pseudo:                              0
% 19.96/3.00  fd_cond:                                0
% 19.96/3.00  fd_pseudo_cond:                         1
% 19.96/3.00  ac_symbols:                             0
% 19.96/3.00  
% 19.96/3.00  ------ Propositional Solver
% 19.96/3.00  
% 19.96/3.00  prop_solver_calls:                      36
% 19.96/3.00  prop_fast_solver_calls:                 1899
% 19.96/3.00  smt_solver_calls:                       0
% 19.96/3.00  smt_fast_solver_calls:                  0
% 19.96/3.00  prop_num_of_clauses:                    29964
% 19.96/3.00  prop_preprocess_simplified:             35926
% 19.96/3.00  prop_fo_subsumed:                       62
% 19.96/3.00  prop_solver_time:                       0.
% 19.96/3.00  smt_solver_time:                        0.
% 19.96/3.00  smt_fast_solver_time:                   0.
% 19.96/3.00  prop_fast_solver_time:                  0.
% 19.96/3.00  prop_unsat_core_time:                   0.
% 19.96/3.00  
% 19.96/3.00  ------ QBF
% 19.96/3.00  
% 19.96/3.00  qbf_q_res:                              0
% 19.96/3.00  qbf_num_tautologies:                    0
% 19.96/3.00  qbf_prep_cycles:                        0
% 19.96/3.00  
% 19.96/3.00  ------ BMC1
% 19.96/3.00  
% 19.96/3.00  bmc1_current_bound:                     -1
% 19.96/3.00  bmc1_last_solved_bound:                 -1
% 19.96/3.00  bmc1_unsat_core_size:                   -1
% 19.96/3.00  bmc1_unsat_core_parents_size:           -1
% 19.96/3.00  bmc1_merge_next_fun:                    0
% 19.96/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.96/3.00  
% 19.96/3.00  ------ Instantiation
% 19.96/3.00  
% 19.96/3.00  inst_num_of_clauses:                    5515
% 19.96/3.00  inst_num_in_passive:                    2095
% 19.96/3.00  inst_num_in_active:                     2281
% 19.96/3.00  inst_num_in_unprocessed:                1139
% 19.96/3.00  inst_num_of_loops:                      2410
% 19.96/3.00  inst_num_of_learning_restarts:          0
% 19.96/3.00  inst_num_moves_active_passive:          125
% 19.96/3.00  inst_lit_activity:                      0
% 19.96/3.00  inst_lit_activity_moves:                1
% 19.96/3.00  inst_num_tautologies:                   0
% 19.96/3.00  inst_num_prop_implied:                  0
% 19.96/3.00  inst_num_existing_simplified:           0
% 19.96/3.00  inst_num_eq_res_simplified:             0
% 19.96/3.00  inst_num_child_elim:                    0
% 19.96/3.00  inst_num_of_dismatching_blockings:      11218
% 19.96/3.00  inst_num_of_non_proper_insts:           10586
% 19.96/3.00  inst_num_of_duplicates:                 0
% 19.96/3.00  inst_inst_num_from_inst_to_res:         0
% 19.96/3.00  inst_dismatching_checking_time:         0.
% 19.96/3.00  
% 19.96/3.00  ------ Resolution
% 19.96/3.00  
% 19.96/3.00  res_num_of_clauses:                     0
% 19.96/3.00  res_num_in_passive:                     0
% 19.96/3.00  res_num_in_active:                      0
% 19.96/3.00  res_num_of_loops:                       79
% 19.96/3.00  res_forward_subset_subsumed:            796
% 19.96/3.00  res_backward_subset_subsumed:           12
% 19.96/3.00  res_forward_subsumed:                   0
% 19.96/3.00  res_backward_subsumed:                  0
% 19.96/3.00  res_forward_subsumption_resolution:     0
% 19.96/3.00  res_backward_subsumption_resolution:    1
% 19.96/3.00  res_clause_to_clause_subsumption:       65736
% 19.96/3.00  res_orphan_elimination:                 0
% 19.96/3.00  res_tautology_del:                      2774
% 19.96/3.00  res_num_eq_res_simplified:              0
% 19.96/3.00  res_num_sel_changes:                    0
% 19.96/3.00  res_moves_from_active_to_pass:          0
% 19.96/3.00  
% 19.96/3.00  ------ Superposition
% 19.96/3.00  
% 19.96/3.00  sup_time_total:                         0.
% 19.96/3.00  sup_time_generating:                    0.
% 19.96/3.00  sup_time_sim_full:                      0.
% 19.96/3.00  sup_time_sim_immed:                     0.
% 19.96/3.00  
% 19.96/3.00  sup_num_of_clauses:                     4224
% 19.96/3.00  sup_num_in_active:                      438
% 19.96/3.00  sup_num_in_passive:                     3786
% 19.96/3.00  sup_num_of_loops:                       480
% 19.96/3.00  sup_fw_superposition:                   6500
% 19.96/3.00  sup_bw_superposition:                   2959
% 19.96/3.00  sup_immediate_simplified:               3823
% 19.96/3.00  sup_given_eliminated:                   4
% 19.96/3.00  comparisons_done:                       0
% 19.96/3.00  comparisons_avoided:                    0
% 19.96/3.00  
% 19.96/3.00  ------ Simplifications
% 19.96/3.00  
% 19.96/3.00  
% 19.96/3.00  sim_fw_subset_subsumed:                 2440
% 19.96/3.00  sim_bw_subset_subsumed:                 354
% 19.96/3.00  sim_fw_subsumed:                        650
% 19.96/3.00  sim_bw_subsumed:                        137
% 19.96/3.00  sim_fw_subsumption_res:                 0
% 19.96/3.00  sim_bw_subsumption_res:                 0
% 19.96/3.00  sim_tautology_del:                      28
% 19.96/3.00  sim_eq_tautology_del:                   38
% 19.96/3.00  sim_eq_res_simp:                        0
% 19.96/3.00  sim_fw_demodulated:                     477
% 19.96/3.00  sim_bw_demodulated:                     25
% 19.96/3.00  sim_light_normalised:                   204
% 19.96/3.00  sim_joinable_taut:                      0
% 19.96/3.00  sim_joinable_simp:                      0
% 19.96/3.00  sim_ac_normalised:                      0
% 19.96/3.00  sim_smt_subsumption:                    0
% 19.96/3.00  
%------------------------------------------------------------------------------
