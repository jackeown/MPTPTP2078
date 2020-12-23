%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:42 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 581 expanded)
%              Number of clauses        :   74 ( 171 expanded)
%              Number of leaves         :   19 ( 141 expanded)
%              Depth                    :   21
%              Number of atoms          :  308 (1691 expanded)
%              Number of equality atoms :  119 ( 251 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f38,f37])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f65])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
          | ~ v5_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
          | ~ v5_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_699,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_242,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_696,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_701,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_701])).

cnf(c_1153,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_701])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_116,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_117,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_116])).

cnf(c_142,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_117])).

cnf(c_305,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_306,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_305])).

cnf(c_329,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_142,c_306])).

cnf(c_694,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_1273,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) = k4_subset_1(u1_struct_0(sK0),X0,sK1)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_694])).

cnf(c_1822,plain,
    ( k3_tarski(k6_enumset1(k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_1273])).

cnf(c_5531,plain,
    ( k3_tarski(k6_enumset1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_699,c_1822])).

cnf(c_1,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_704,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_705,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1996,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_705])).

cnf(c_2136,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1996,c_705])).

cnf(c_3557,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_2136])).

cnf(c_6231,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5531,c_3557])).

cnf(c_17,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_788,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_789,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_1031,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1518,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_1519,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_6490,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6231,c_17,c_789,c_1519])).

cnf(c_10,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_13,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_209,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_211,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_209,c_15,c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_697,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_880,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_211,c_697])).

cnf(c_785,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_786,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_1001,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_880,c_17,c_786])).

cnf(c_1157,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_701])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_141,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k4_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_117])).

cnf(c_328,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_141,c_306])).

cnf(c_695,plain,
    ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1849,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_695])).

cnf(c_9792,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_6490,c_1849])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_698,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_887,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_698])).

cnf(c_2503,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_699,c_887])).

cnf(c_2521,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_2503,c_211])).

cnf(c_9794,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_9792,c_2521])).

cnf(c_1612,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_tops_1(sK0,X1))) = k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_694])).

cnf(c_4527,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK1))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_1612])).

cnf(c_4750,plain,
    ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1157,c_4527])).

cnf(c_4870,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4750,c_704])).

cnf(c_10209,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9794,c_4870])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10209,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.47/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/0.98  
% 3.47/0.98  ------  iProver source info
% 3.47/0.98  
% 3.47/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.47/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/0.98  git: non_committed_changes: false
% 3.47/0.98  git: last_make_outside_of_git: false
% 3.47/0.98  
% 3.47/0.98  ------ 
% 3.47/0.98  
% 3.47/0.98  ------ Input Options
% 3.47/0.98  
% 3.47/0.98  --out_options                           all
% 3.47/0.98  --tptp_safe_out                         true
% 3.47/0.98  --problem_path                          ""
% 3.47/0.98  --include_path                          ""
% 3.47/0.98  --clausifier                            res/vclausify_rel
% 3.47/0.98  --clausifier_options                    --mode clausify
% 3.47/0.98  --stdin                                 false
% 3.47/0.98  --stats_out                             all
% 3.47/0.98  
% 3.47/0.98  ------ General Options
% 3.47/0.98  
% 3.47/0.98  --fof                                   false
% 3.47/0.98  --time_out_real                         305.
% 3.47/0.98  --time_out_virtual                      -1.
% 3.47/0.98  --symbol_type_check                     false
% 3.47/0.98  --clausify_out                          false
% 3.47/0.98  --sig_cnt_out                           false
% 3.47/0.98  --trig_cnt_out                          false
% 3.47/0.98  --trig_cnt_out_tolerance                1.
% 3.47/0.98  --trig_cnt_out_sk_spl                   false
% 3.47/0.98  --abstr_cl_out                          false
% 3.47/0.98  
% 3.47/0.98  ------ Global Options
% 3.47/0.98  
% 3.47/0.98  --schedule                              default
% 3.47/0.98  --add_important_lit                     false
% 3.47/0.98  --prop_solver_per_cl                    1000
% 3.47/0.98  --min_unsat_core                        false
% 3.47/0.98  --soft_assumptions                      false
% 3.47/0.98  --soft_lemma_size                       3
% 3.47/0.98  --prop_impl_unit_size                   0
% 3.47/0.98  --prop_impl_unit                        []
% 3.47/0.98  --share_sel_clauses                     true
% 3.47/0.98  --reset_solvers                         false
% 3.47/0.98  --bc_imp_inh                            [conj_cone]
% 3.47/0.98  --conj_cone_tolerance                   3.
% 3.47/0.98  --extra_neg_conj                        none
% 3.47/0.98  --large_theory_mode                     true
% 3.47/0.98  --prolific_symb_bound                   200
% 3.47/0.98  --lt_threshold                          2000
% 3.47/0.98  --clause_weak_htbl                      true
% 3.47/0.98  --gc_record_bc_elim                     false
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing Options
% 3.47/0.98  
% 3.47/0.98  --preprocessing_flag                    true
% 3.47/0.98  --time_out_prep_mult                    0.1
% 3.47/0.98  --splitting_mode                        input
% 3.47/0.98  --splitting_grd                         true
% 3.47/0.98  --splitting_cvd                         false
% 3.47/0.98  --splitting_cvd_svl                     false
% 3.47/0.98  --splitting_nvd                         32
% 3.47/0.98  --sub_typing                            true
% 3.47/0.98  --prep_gs_sim                           true
% 3.47/0.98  --prep_unflatten                        true
% 3.47/0.98  --prep_res_sim                          true
% 3.47/0.98  --prep_upred                            true
% 3.47/0.98  --prep_sem_filter                       exhaustive
% 3.47/0.98  --prep_sem_filter_out                   false
% 3.47/0.98  --pred_elim                             true
% 3.47/0.98  --res_sim_input                         true
% 3.47/0.98  --eq_ax_congr_red                       true
% 3.47/0.98  --pure_diseq_elim                       true
% 3.47/0.98  --brand_transform                       false
% 3.47/0.98  --non_eq_to_eq                          false
% 3.47/0.98  --prep_def_merge                        true
% 3.47/0.98  --prep_def_merge_prop_impl              false
% 3.47/0.98  --prep_def_merge_mbd                    true
% 3.47/0.98  --prep_def_merge_tr_red                 false
% 3.47/0.98  --prep_def_merge_tr_cl                  false
% 3.47/0.98  --smt_preprocessing                     true
% 3.47/0.98  --smt_ac_axioms                         fast
% 3.47/0.98  --preprocessed_out                      false
% 3.47/0.98  --preprocessed_stats                    false
% 3.47/0.98  
% 3.47/0.98  ------ Abstraction refinement Options
% 3.47/0.98  
% 3.47/0.98  --abstr_ref                             []
% 3.47/0.98  --abstr_ref_prep                        false
% 3.47/0.98  --abstr_ref_until_sat                   false
% 3.47/0.98  --abstr_ref_sig_restrict                funpre
% 3.47/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/0.98  --abstr_ref_under                       []
% 3.47/0.98  
% 3.47/0.98  ------ SAT Options
% 3.47/0.98  
% 3.47/0.98  --sat_mode                              false
% 3.47/0.98  --sat_fm_restart_options                ""
% 3.47/0.98  --sat_gr_def                            false
% 3.47/0.98  --sat_epr_types                         true
% 3.47/0.98  --sat_non_cyclic_types                  false
% 3.47/0.98  --sat_finite_models                     false
% 3.47/0.98  --sat_fm_lemmas                         false
% 3.47/0.98  --sat_fm_prep                           false
% 3.47/0.98  --sat_fm_uc_incr                        true
% 3.47/0.98  --sat_out_model                         small
% 3.47/0.98  --sat_out_clauses                       false
% 3.47/0.98  
% 3.47/0.98  ------ QBF Options
% 3.47/0.98  
% 3.47/0.98  --qbf_mode                              false
% 3.47/0.98  --qbf_elim_univ                         false
% 3.47/0.98  --qbf_dom_inst                          none
% 3.47/0.98  --qbf_dom_pre_inst                      false
% 3.47/0.98  --qbf_sk_in                             false
% 3.47/0.98  --qbf_pred_elim                         true
% 3.47/0.98  --qbf_split                             512
% 3.47/0.98  
% 3.47/0.98  ------ BMC1 Options
% 3.47/0.98  
% 3.47/0.98  --bmc1_incremental                      false
% 3.47/0.98  --bmc1_axioms                           reachable_all
% 3.47/0.98  --bmc1_min_bound                        0
% 3.47/0.98  --bmc1_max_bound                        -1
% 3.47/0.98  --bmc1_max_bound_default                -1
% 3.47/0.98  --bmc1_symbol_reachability              true
% 3.47/0.98  --bmc1_property_lemmas                  false
% 3.47/0.98  --bmc1_k_induction                      false
% 3.47/0.98  --bmc1_non_equiv_states                 false
% 3.47/0.98  --bmc1_deadlock                         false
% 3.47/0.98  --bmc1_ucm                              false
% 3.47/0.98  --bmc1_add_unsat_core                   none
% 3.47/0.98  --bmc1_unsat_core_children              false
% 3.47/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/0.98  --bmc1_out_stat                         full
% 3.47/0.98  --bmc1_ground_init                      false
% 3.47/0.98  --bmc1_pre_inst_next_state              false
% 3.47/0.98  --bmc1_pre_inst_state                   false
% 3.47/0.98  --bmc1_pre_inst_reach_state             false
% 3.47/0.98  --bmc1_out_unsat_core                   false
% 3.47/0.98  --bmc1_aig_witness_out                  false
% 3.47/0.98  --bmc1_verbose                          false
% 3.47/0.98  --bmc1_dump_clauses_tptp                false
% 3.47/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.47/0.98  --bmc1_dump_file                        -
% 3.47/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.47/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.47/0.98  --bmc1_ucm_extend_mode                  1
% 3.47/0.98  --bmc1_ucm_init_mode                    2
% 3.47/0.98  --bmc1_ucm_cone_mode                    none
% 3.47/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.47/0.98  --bmc1_ucm_relax_model                  4
% 3.47/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.47/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/0.98  --bmc1_ucm_layered_model                none
% 3.47/0.98  --bmc1_ucm_max_lemma_size               10
% 3.47/0.98  
% 3.47/0.98  ------ AIG Options
% 3.47/0.98  
% 3.47/0.98  --aig_mode                              false
% 3.47/0.98  
% 3.47/0.98  ------ Instantiation Options
% 3.47/0.98  
% 3.47/0.98  --instantiation_flag                    true
% 3.47/0.98  --inst_sos_flag                         false
% 3.47/0.98  --inst_sos_phase                        true
% 3.47/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/0.98  --inst_lit_sel_side                     num_symb
% 3.47/0.98  --inst_solver_per_active                1400
% 3.47/0.98  --inst_solver_calls_frac                1.
% 3.47/0.98  --inst_passive_queue_type               priority_queues
% 3.47/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/0.98  --inst_passive_queues_freq              [25;2]
% 3.47/0.98  --inst_dismatching                      true
% 3.47/0.98  --inst_eager_unprocessed_to_passive     true
% 3.47/0.98  --inst_prop_sim_given                   true
% 3.47/0.98  --inst_prop_sim_new                     false
% 3.47/0.98  --inst_subs_new                         false
% 3.47/0.98  --inst_eq_res_simp                      false
% 3.47/0.98  --inst_subs_given                       false
% 3.47/0.98  --inst_orphan_elimination               true
% 3.47/0.98  --inst_learning_loop_flag               true
% 3.47/0.98  --inst_learning_start                   3000
% 3.47/0.98  --inst_learning_factor                  2
% 3.47/0.98  --inst_start_prop_sim_after_learn       3
% 3.47/0.98  --inst_sel_renew                        solver
% 3.47/0.98  --inst_lit_activity_flag                true
% 3.47/0.98  --inst_restr_to_given                   false
% 3.47/0.98  --inst_activity_threshold               500
% 3.47/0.98  --inst_out_proof                        true
% 3.47/0.98  
% 3.47/0.98  ------ Resolution Options
% 3.47/0.98  
% 3.47/0.98  --resolution_flag                       true
% 3.47/0.98  --res_lit_sel                           adaptive
% 3.47/0.98  --res_lit_sel_side                      none
% 3.47/0.98  --res_ordering                          kbo
% 3.47/0.98  --res_to_prop_solver                    active
% 3.47/0.98  --res_prop_simpl_new                    false
% 3.47/0.98  --res_prop_simpl_given                  true
% 3.47/0.98  --res_passive_queue_type                priority_queues
% 3.47/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/0.98  --res_passive_queues_freq               [15;5]
% 3.47/0.98  --res_forward_subs                      full
% 3.47/0.98  --res_backward_subs                     full
% 3.47/0.98  --res_forward_subs_resolution           true
% 3.47/0.98  --res_backward_subs_resolution          true
% 3.47/0.98  --res_orphan_elimination                true
% 3.47/0.98  --res_time_limit                        2.
% 3.47/0.98  --res_out_proof                         true
% 3.47/0.98  
% 3.47/0.98  ------ Superposition Options
% 3.47/0.98  
% 3.47/0.98  --superposition_flag                    true
% 3.47/0.98  --sup_passive_queue_type                priority_queues
% 3.47/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.47/0.98  --demod_completeness_check              fast
% 3.47/0.98  --demod_use_ground                      true
% 3.47/0.98  --sup_to_prop_solver                    passive
% 3.47/0.98  --sup_prop_simpl_new                    true
% 3.47/0.98  --sup_prop_simpl_given                  true
% 3.47/0.98  --sup_fun_splitting                     false
% 3.47/0.98  --sup_smt_interval                      50000
% 3.47/0.98  
% 3.47/0.98  ------ Superposition Simplification Setup
% 3.47/0.98  
% 3.47/0.98  --sup_indices_passive                   []
% 3.47/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_full_bw                           [BwDemod]
% 3.47/0.98  --sup_immed_triv                        [TrivRules]
% 3.47/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_immed_bw_main                     []
% 3.47/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.98  
% 3.47/0.98  ------ Combination Options
% 3.47/0.98  
% 3.47/0.98  --comb_res_mult                         3
% 3.47/0.98  --comb_sup_mult                         2
% 3.47/0.98  --comb_inst_mult                        10
% 3.47/0.98  
% 3.47/0.98  ------ Debug Options
% 3.47/0.98  
% 3.47/0.98  --dbg_backtrace                         false
% 3.47/0.98  --dbg_dump_prop_clauses                 false
% 3.47/0.98  --dbg_dump_prop_clauses_file            -
% 3.47/0.98  --dbg_out_stat                          false
% 3.47/0.98  ------ Parsing...
% 3.47/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.98  ------ Proving...
% 3.47/0.98  ------ Problem Properties 
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  clauses                                 14
% 3.47/0.98  conjectures                             2
% 3.47/0.98  EPR                                     1
% 3.47/0.98  Horn                                    14
% 3.47/0.98  unary                                   6
% 3.47/0.98  binary                                  5
% 3.47/0.98  lits                                    25
% 3.47/0.98  lits eq                                 5
% 3.47/0.98  fd_pure                                 0
% 3.47/0.98  fd_pseudo                               0
% 3.47/0.98  fd_cond                                 0
% 3.47/0.98  fd_pseudo_cond                          0
% 3.47/0.98  AC symbols                              0
% 3.47/0.98  
% 3.47/0.98  ------ Schedule dynamic 5 is on 
% 3.47/0.98  
% 3.47/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ 
% 3.47/0.98  Current options:
% 3.47/0.98  ------ 
% 3.47/0.98  
% 3.47/0.98  ------ Input Options
% 3.47/0.98  
% 3.47/0.98  --out_options                           all
% 3.47/0.98  --tptp_safe_out                         true
% 3.47/0.98  --problem_path                          ""
% 3.47/0.98  --include_path                          ""
% 3.47/0.98  --clausifier                            res/vclausify_rel
% 3.47/0.98  --clausifier_options                    --mode clausify
% 3.47/0.98  --stdin                                 false
% 3.47/0.98  --stats_out                             all
% 3.47/0.98  
% 3.47/0.98  ------ General Options
% 3.47/0.98  
% 3.47/0.98  --fof                                   false
% 3.47/0.98  --time_out_real                         305.
% 3.47/0.98  --time_out_virtual                      -1.
% 3.47/0.98  --symbol_type_check                     false
% 3.47/0.98  --clausify_out                          false
% 3.47/0.98  --sig_cnt_out                           false
% 3.47/0.98  --trig_cnt_out                          false
% 3.47/0.98  --trig_cnt_out_tolerance                1.
% 3.47/0.98  --trig_cnt_out_sk_spl                   false
% 3.47/0.98  --abstr_cl_out                          false
% 3.47/0.98  
% 3.47/0.98  ------ Global Options
% 3.47/0.98  
% 3.47/0.98  --schedule                              default
% 3.47/0.98  --add_important_lit                     false
% 3.47/0.98  --prop_solver_per_cl                    1000
% 3.47/0.98  --min_unsat_core                        false
% 3.47/0.98  --soft_assumptions                      false
% 3.47/0.98  --soft_lemma_size                       3
% 3.47/0.98  --prop_impl_unit_size                   0
% 3.47/0.98  --prop_impl_unit                        []
% 3.47/0.98  --share_sel_clauses                     true
% 3.47/0.98  --reset_solvers                         false
% 3.47/0.98  --bc_imp_inh                            [conj_cone]
% 3.47/0.98  --conj_cone_tolerance                   3.
% 3.47/0.98  --extra_neg_conj                        none
% 3.47/0.98  --large_theory_mode                     true
% 3.47/0.98  --prolific_symb_bound                   200
% 3.47/0.98  --lt_threshold                          2000
% 3.47/0.98  --clause_weak_htbl                      true
% 3.47/0.98  --gc_record_bc_elim                     false
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing Options
% 3.47/0.98  
% 3.47/0.98  --preprocessing_flag                    true
% 3.47/0.98  --time_out_prep_mult                    0.1
% 3.47/0.98  --splitting_mode                        input
% 3.47/0.98  --splitting_grd                         true
% 3.47/0.98  --splitting_cvd                         false
% 3.47/0.98  --splitting_cvd_svl                     false
% 3.47/0.98  --splitting_nvd                         32
% 3.47/0.98  --sub_typing                            true
% 3.47/0.98  --prep_gs_sim                           true
% 3.47/0.98  --prep_unflatten                        true
% 3.47/0.98  --prep_res_sim                          true
% 3.47/0.98  --prep_upred                            true
% 3.47/0.98  --prep_sem_filter                       exhaustive
% 3.47/0.98  --prep_sem_filter_out                   false
% 3.47/0.98  --pred_elim                             true
% 3.47/0.98  --res_sim_input                         true
% 3.47/0.98  --eq_ax_congr_red                       true
% 3.47/0.98  --pure_diseq_elim                       true
% 3.47/0.98  --brand_transform                       false
% 3.47/0.98  --non_eq_to_eq                          false
% 3.47/0.98  --prep_def_merge                        true
% 3.47/0.98  --prep_def_merge_prop_impl              false
% 3.47/0.98  --prep_def_merge_mbd                    true
% 3.47/0.98  --prep_def_merge_tr_red                 false
% 3.47/0.98  --prep_def_merge_tr_cl                  false
% 3.47/0.98  --smt_preprocessing                     true
% 3.47/0.98  --smt_ac_axioms                         fast
% 3.47/0.98  --preprocessed_out                      false
% 3.47/0.98  --preprocessed_stats                    false
% 3.47/0.98  
% 3.47/0.98  ------ Abstraction refinement Options
% 3.47/0.98  
% 3.47/0.98  --abstr_ref                             []
% 3.47/0.98  --abstr_ref_prep                        false
% 3.47/0.98  --abstr_ref_until_sat                   false
% 3.47/0.98  --abstr_ref_sig_restrict                funpre
% 3.47/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/0.98  --abstr_ref_under                       []
% 3.47/0.98  
% 3.47/0.98  ------ SAT Options
% 3.47/0.98  
% 3.47/0.98  --sat_mode                              false
% 3.47/0.98  --sat_fm_restart_options                ""
% 3.47/0.98  --sat_gr_def                            false
% 3.47/0.98  --sat_epr_types                         true
% 3.47/0.98  --sat_non_cyclic_types                  false
% 3.47/0.98  --sat_finite_models                     false
% 3.47/0.98  --sat_fm_lemmas                         false
% 3.47/0.98  --sat_fm_prep                           false
% 3.47/0.98  --sat_fm_uc_incr                        true
% 3.47/0.98  --sat_out_model                         small
% 3.47/0.98  --sat_out_clauses                       false
% 3.47/0.98  
% 3.47/0.98  ------ QBF Options
% 3.47/0.98  
% 3.47/0.98  --qbf_mode                              false
% 3.47/0.98  --qbf_elim_univ                         false
% 3.47/0.98  --qbf_dom_inst                          none
% 3.47/0.98  --qbf_dom_pre_inst                      false
% 3.47/0.98  --qbf_sk_in                             false
% 3.47/0.98  --qbf_pred_elim                         true
% 3.47/0.98  --qbf_split                             512
% 3.47/0.98  
% 3.47/0.98  ------ BMC1 Options
% 3.47/0.98  
% 3.47/0.98  --bmc1_incremental                      false
% 3.47/0.98  --bmc1_axioms                           reachable_all
% 3.47/0.98  --bmc1_min_bound                        0
% 3.47/0.98  --bmc1_max_bound                        -1
% 3.47/0.98  --bmc1_max_bound_default                -1
% 3.47/0.98  --bmc1_symbol_reachability              true
% 3.47/0.98  --bmc1_property_lemmas                  false
% 3.47/0.98  --bmc1_k_induction                      false
% 3.47/0.98  --bmc1_non_equiv_states                 false
% 3.47/0.98  --bmc1_deadlock                         false
% 3.47/0.98  --bmc1_ucm                              false
% 3.47/0.98  --bmc1_add_unsat_core                   none
% 3.47/0.98  --bmc1_unsat_core_children              false
% 3.47/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/0.98  --bmc1_out_stat                         full
% 3.47/0.98  --bmc1_ground_init                      false
% 3.47/0.98  --bmc1_pre_inst_next_state              false
% 3.47/0.98  --bmc1_pre_inst_state                   false
% 3.47/0.98  --bmc1_pre_inst_reach_state             false
% 3.47/0.98  --bmc1_out_unsat_core                   false
% 3.47/0.98  --bmc1_aig_witness_out                  false
% 3.47/0.98  --bmc1_verbose                          false
% 3.47/0.98  --bmc1_dump_clauses_tptp                false
% 3.47/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.47/0.98  --bmc1_dump_file                        -
% 3.47/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.47/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.47/0.98  --bmc1_ucm_extend_mode                  1
% 3.47/0.98  --bmc1_ucm_init_mode                    2
% 3.47/0.98  --bmc1_ucm_cone_mode                    none
% 3.47/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.47/0.98  --bmc1_ucm_relax_model                  4
% 3.47/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.47/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/0.98  --bmc1_ucm_layered_model                none
% 3.47/0.98  --bmc1_ucm_max_lemma_size               10
% 3.47/0.98  
% 3.47/0.98  ------ AIG Options
% 3.47/0.98  
% 3.47/0.98  --aig_mode                              false
% 3.47/0.98  
% 3.47/0.98  ------ Instantiation Options
% 3.47/0.98  
% 3.47/0.98  --instantiation_flag                    true
% 3.47/0.98  --inst_sos_flag                         false
% 3.47/0.98  --inst_sos_phase                        true
% 3.47/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/0.98  --inst_lit_sel_side                     none
% 3.47/0.98  --inst_solver_per_active                1400
% 3.47/0.98  --inst_solver_calls_frac                1.
% 3.47/0.98  --inst_passive_queue_type               priority_queues
% 3.47/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/0.98  --inst_passive_queues_freq              [25;2]
% 3.47/0.98  --inst_dismatching                      true
% 3.47/0.98  --inst_eager_unprocessed_to_passive     true
% 3.47/0.98  --inst_prop_sim_given                   true
% 3.47/0.98  --inst_prop_sim_new                     false
% 3.47/0.98  --inst_subs_new                         false
% 3.47/0.98  --inst_eq_res_simp                      false
% 3.47/0.98  --inst_subs_given                       false
% 3.47/0.98  --inst_orphan_elimination               true
% 3.47/0.98  --inst_learning_loop_flag               true
% 3.47/0.98  --inst_learning_start                   3000
% 3.47/0.98  --inst_learning_factor                  2
% 3.47/0.98  --inst_start_prop_sim_after_learn       3
% 3.47/0.98  --inst_sel_renew                        solver
% 3.47/0.98  --inst_lit_activity_flag                true
% 3.47/0.98  --inst_restr_to_given                   false
% 3.47/0.98  --inst_activity_threshold               500
% 3.47/0.98  --inst_out_proof                        true
% 3.47/0.98  
% 3.47/0.98  ------ Resolution Options
% 3.47/0.98  
% 3.47/0.98  --resolution_flag                       false
% 3.47/0.98  --res_lit_sel                           adaptive
% 3.47/0.98  --res_lit_sel_side                      none
% 3.47/0.98  --res_ordering                          kbo
% 3.47/0.98  --res_to_prop_solver                    active
% 3.47/0.98  --res_prop_simpl_new                    false
% 3.47/0.98  --res_prop_simpl_given                  true
% 3.47/0.98  --res_passive_queue_type                priority_queues
% 3.47/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/0.98  --res_passive_queues_freq               [15;5]
% 3.47/0.98  --res_forward_subs                      full
% 3.47/0.98  --res_backward_subs                     full
% 3.47/0.98  --res_forward_subs_resolution           true
% 3.47/0.98  --res_backward_subs_resolution          true
% 3.47/0.98  --res_orphan_elimination                true
% 3.47/0.98  --res_time_limit                        2.
% 3.47/0.98  --res_out_proof                         true
% 3.47/0.98  
% 3.47/0.98  ------ Superposition Options
% 3.47/0.98  
% 3.47/0.98  --superposition_flag                    true
% 3.47/0.98  --sup_passive_queue_type                priority_queues
% 3.47/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.47/0.98  --demod_completeness_check              fast
% 3.47/0.98  --demod_use_ground                      true
% 3.47/0.98  --sup_to_prop_solver                    passive
% 3.47/0.98  --sup_prop_simpl_new                    true
% 3.47/0.98  --sup_prop_simpl_given                  true
% 3.47/0.98  --sup_fun_splitting                     false
% 3.47/0.98  --sup_smt_interval                      50000
% 3.47/0.98  
% 3.47/0.98  ------ Superposition Simplification Setup
% 3.47/0.98  
% 3.47/0.98  --sup_indices_passive                   []
% 3.47/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_full_bw                           [BwDemod]
% 3.47/0.98  --sup_immed_triv                        [TrivRules]
% 3.47/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_immed_bw_main                     []
% 3.47/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.98  
% 3.47/0.98  ------ Combination Options
% 3.47/0.98  
% 3.47/0.98  --comb_res_mult                         3
% 3.47/0.98  --comb_sup_mult                         2
% 3.47/0.98  --comb_inst_mult                        10
% 3.47/0.98  
% 3.47/0.98  ------ Debug Options
% 3.47/0.98  
% 3.47/0.98  --dbg_backtrace                         false
% 3.47/0.98  --dbg_dump_prop_clauses                 false
% 3.47/0.98  --dbg_dump_prop_clauses_file            -
% 3.47/0.98  --dbg_out_stat                          false
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ Proving...
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  % SZS status Theorem for theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  fof(f19,conjecture,(
% 3.47/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f20,negated_conjecture,(
% 3.47/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.47/0.98    inference(negated_conjecture,[],[f19])).
% 3.47/0.98  
% 3.47/0.98  fof(f34,plain,(
% 3.47/0.98    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.47/0.98    inference(ennf_transformation,[],[f20])).
% 3.47/0.98  
% 3.47/0.98  fof(f35,plain,(
% 3.47/0.98    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.47/0.98    inference(flattening,[],[f34])).
% 3.47/0.98  
% 3.47/0.98  fof(f38,plain,(
% 3.47/0.98    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.47/0.98    introduced(choice_axiom,[])).
% 3.47/0.98  
% 3.47/0.98  fof(f37,plain,(
% 3.47/0.98    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.47/0.98    introduced(choice_axiom,[])).
% 3.47/0.98  
% 3.47/0.98  fof(f39,plain,(
% 3.47/0.98    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.47/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f38,f37])).
% 3.47/0.98  
% 3.47/0.98  fof(f60,plain,(
% 3.47/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.47/0.98    inference(cnf_transformation,[],[f39])).
% 3.47/0.98  
% 3.47/0.98  fof(f15,axiom,(
% 3.47/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f27,plain,(
% 3.47/0.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.47/0.98    inference(ennf_transformation,[],[f15])).
% 3.47/0.98  
% 3.47/0.98  fof(f28,plain,(
% 3.47/0.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.47/0.98    inference(flattening,[],[f27])).
% 3.47/0.98  
% 3.47/0.98  fof(f55,plain,(
% 3.47/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f28])).
% 3.47/0.98  
% 3.47/0.98  fof(f59,plain,(
% 3.47/0.98    l1_pre_topc(sK0)),
% 3.47/0.98    inference(cnf_transformation,[],[f39])).
% 3.47/0.98  
% 3.47/0.98  fof(f14,axiom,(
% 3.47/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f36,plain,(
% 3.47/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.47/0.98    inference(nnf_transformation,[],[f14])).
% 3.47/0.98  
% 3.47/0.98  fof(f53,plain,(
% 3.47/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.47/0.98    inference(cnf_transformation,[],[f36])).
% 3.47/0.98  
% 3.47/0.98  fof(f13,axiom,(
% 3.47/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f25,plain,(
% 3.47/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.47/0.98    inference(ennf_transformation,[],[f13])).
% 3.47/0.98  
% 3.47/0.98  fof(f26,plain,(
% 3.47/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.47/0.98    inference(flattening,[],[f25])).
% 3.47/0.98  
% 3.47/0.98  fof(f52,plain,(
% 3.47/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.47/0.98    inference(cnf_transformation,[],[f26])).
% 3.47/0.98  
% 3.47/0.98  fof(f9,axiom,(
% 3.47/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f48,plain,(
% 3.47/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.47/0.98    inference(cnf_transformation,[],[f9])).
% 3.47/0.98  
% 3.47/0.98  fof(f3,axiom,(
% 3.47/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f42,plain,(
% 3.47/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f3])).
% 3.47/0.98  
% 3.47/0.98  fof(f4,axiom,(
% 3.47/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f43,plain,(
% 3.47/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f4])).
% 3.47/0.98  
% 3.47/0.98  fof(f5,axiom,(
% 3.47/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f44,plain,(
% 3.47/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f5])).
% 3.47/0.98  
% 3.47/0.98  fof(f6,axiom,(
% 3.47/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f45,plain,(
% 3.47/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f6])).
% 3.47/0.98  
% 3.47/0.98  fof(f7,axiom,(
% 3.47/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f46,plain,(
% 3.47/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f7])).
% 3.47/0.98  
% 3.47/0.98  fof(f8,axiom,(
% 3.47/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f47,plain,(
% 3.47/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f8])).
% 3.47/0.98  
% 3.47/0.98  fof(f63,plain,(
% 3.47/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.47/0.98    inference(definition_unfolding,[],[f46,f47])).
% 3.47/0.98  
% 3.47/0.98  fof(f64,plain,(
% 3.47/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.47/0.98    inference(definition_unfolding,[],[f45,f63])).
% 3.47/0.98  
% 3.47/0.98  fof(f65,plain,(
% 3.47/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.47/0.98    inference(definition_unfolding,[],[f44,f64])).
% 3.47/0.98  
% 3.47/0.98  fof(f66,plain,(
% 3.47/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.47/0.98    inference(definition_unfolding,[],[f43,f65])).
% 3.47/0.98  
% 3.47/0.98  fof(f67,plain,(
% 3.47/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.47/0.98    inference(definition_unfolding,[],[f42,f66])).
% 3.47/0.98  
% 3.47/0.98  fof(f68,plain,(
% 3.47/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.47/0.98    inference(definition_unfolding,[],[f48,f67])).
% 3.47/0.98  
% 3.47/0.98  fof(f70,plain,(
% 3.47/0.98    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.47/0.98    inference(definition_unfolding,[],[f52,f68])).
% 3.47/0.98  
% 3.47/0.98  fof(f54,plain,(
% 3.47/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f36])).
% 3.47/0.98  
% 3.47/0.98  fof(f2,axiom,(
% 3.47/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f41,plain,(
% 3.47/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.47/0.98    inference(cnf_transformation,[],[f2])).
% 3.47/0.98  
% 3.47/0.98  fof(f69,plain,(
% 3.47/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.47/0.98    inference(definition_unfolding,[],[f41,f68])).
% 3.47/0.98  
% 3.47/0.98  fof(f1,axiom,(
% 3.47/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f21,plain,(
% 3.47/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.47/0.98    inference(ennf_transformation,[],[f1])).
% 3.47/0.98  
% 3.47/0.98  fof(f22,plain,(
% 3.47/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.47/0.98    inference(flattening,[],[f21])).
% 3.47/0.98  
% 3.47/0.98  fof(f40,plain,(
% 3.47/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f22])).
% 3.47/0.98  
% 3.47/0.98  fof(f17,axiom,(
% 3.47/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)))))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f31,plain,(
% 3.47/0.98    ! [X0] : (! [X1] : ((k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) | ~v5_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.47/0.98    inference(ennf_transformation,[],[f17])).
% 3.47/0.98  
% 3.47/0.98  fof(f32,plain,(
% 3.47/0.98    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.47/0.98    inference(flattening,[],[f31])).
% 3.47/0.98  
% 3.47/0.98  fof(f57,plain,(
% 3.47/0.98    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f32])).
% 3.47/0.98  
% 3.47/0.98  fof(f61,plain,(
% 3.47/0.98    v5_tops_1(sK1,sK0)),
% 3.47/0.98    inference(cnf_transformation,[],[f39])).
% 3.47/0.98  
% 3.47/0.98  fof(f16,axiom,(
% 3.47/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f29,plain,(
% 3.47/0.98    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.47/0.98    inference(ennf_transformation,[],[f16])).
% 3.47/0.98  
% 3.47/0.98  fof(f30,plain,(
% 3.47/0.98    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.47/0.98    inference(flattening,[],[f29])).
% 3.47/0.98  
% 3.47/0.98  fof(f56,plain,(
% 3.47/0.98    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f30])).
% 3.47/0.98  
% 3.47/0.98  fof(f10,axiom,(
% 3.47/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f23,plain,(
% 3.47/0.98    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.47/0.98    inference(ennf_transformation,[],[f10])).
% 3.47/0.98  
% 3.47/0.98  fof(f24,plain,(
% 3.47/0.98    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.47/0.98    inference(flattening,[],[f23])).
% 3.47/0.98  
% 3.47/0.98  fof(f49,plain,(
% 3.47/0.98    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.47/0.98    inference(cnf_transformation,[],[f24])).
% 3.47/0.98  
% 3.47/0.98  fof(f18,axiom,(
% 3.47/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.47/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f33,plain,(
% 3.47/0.98    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.47/0.98    inference(ennf_transformation,[],[f18])).
% 3.47/0.98  
% 3.47/0.98  fof(f58,plain,(
% 3.47/0.98    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f33])).
% 3.47/0.98  
% 3.47/0.98  fof(f62,plain,(
% 3.47/0.98    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 3.47/0.98    inference(cnf_transformation,[],[f39])).
% 3.47/0.98  
% 3.47/0.98  cnf(c_14,negated_conjecture,
% 3.47/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.47/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_699,plain,
% 3.47/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_8,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | ~ l1_pre_topc(X1) ),
% 3.47/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_15,negated_conjecture,
% 3.47/0.98      ( l1_pre_topc(sK0) ),
% 3.47/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_241,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | sK0 != X1 ),
% 3.47/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_242,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.47/0.98      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.47/0.98      inference(unflattening,[status(thm)],[c_241]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_696,plain,
% 3.47/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.47/0.98      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_242]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_7,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.47/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_701,plain,
% 3.47/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.47/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1155,plain,
% 3.47/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.47/0.98      | r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_696,c_701]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1153,plain,
% 3.47/0.98      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_699,c_701]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_5,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.47/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.47/0.98      | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 3.47/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_6,plain,
% 3.47/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.47/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_116,plain,
% 3.47/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.47/0.98      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_117,plain,
% 3.47/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.47/0.98      inference(renaming,[status(thm)],[c_116]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_142,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.47/0.98      | ~ r1_tarski(X2,X1)
% 3.47/0.98      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 3.47/0.98      inference(bin_hyper_res,[status(thm)],[c_5,c_117]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_305,plain,
% 3.47/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.47/0.98      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_306,plain,
% 3.47/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.47/0.98      inference(renaming,[status(thm)],[c_305]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_329,plain,
% 3.47/0.98      ( ~ r1_tarski(X0,X1)
% 3.47/0.98      | ~ r1_tarski(X2,X1)
% 3.47/0.98      | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 3.47/0.98      inference(bin_hyper_res,[status(thm)],[c_142,c_306]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_694,plain,
% 3.47/0.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.47/0.98      | r1_tarski(X1,X2) != iProver_top
% 3.47/0.98      | r1_tarski(X0,X2) != iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1273,plain,
% 3.47/0.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) = k4_subset_1(u1_struct_0(sK0),X0,sK1)
% 3.47/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_1153,c_694]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1822,plain,
% 3.47/0.98      ( k3_tarski(k6_enumset1(k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),sK1)
% 3.47/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_1155,c_1273]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_5531,plain,
% 3.47/0.98      ( k3_tarski(k6_enumset1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1) ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_699,c_1822]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1,plain,
% 3.47/0.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.47/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_704,plain,
% 3.47/0.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_0,plain,
% 3.47/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.47/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_705,plain,
% 3.47/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.47/0.98      | r1_tarski(X2,X0) != iProver_top
% 3.47/0.98      | r1_tarski(X2,X1) = iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1996,plain,
% 3.47/0.98      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 3.47/0.98      | r1_tarski(X0,sK1) != iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_1153,c_705]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_2136,plain,
% 3.47/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.47/0.98      | r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 3.47/0.98      | r1_tarski(X1,sK1) != iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_1996,c_705]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_3557,plain,
% 3.47/0.98      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 3.47/0.98      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),sK1) != iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_704,c_2136]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_6231,plain,
% 3.47/0.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),sK1),sK1) != iProver_top
% 3.47/0.98      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_5531,c_3557]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_17,plain,
% 3.47/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_788,plain,
% 3.47/0.98      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.47/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_242]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_789,plain,
% 3.47/0.98      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.47/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1031,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.47/0.98      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1518,plain,
% 3.47/0.98      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.47/0.98      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_1031]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1519,plain,
% 3.47/0.98      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.47/0.98      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_6490,plain,
% 3.47/0.98      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.47/0.98      inference(global_propositional_subsumption,
% 3.47/0.98                [status(thm)],
% 3.47/0.98                [c_6231,c_17,c_789,c_1519]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_10,plain,
% 3.47/0.98      ( ~ v5_tops_1(X0,X1)
% 3.47/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | ~ l1_pre_topc(X1)
% 3.47/0.98      | k2_tops_1(X1,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.47/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_13,negated_conjecture,
% 3.47/0.98      ( v5_tops_1(sK1,sK0) ),
% 3.47/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_208,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | ~ l1_pre_topc(X1)
% 3.47/0.98      | k2_tops_1(X1,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 3.47/0.98      | sK1 != X0
% 3.47/0.98      | sK0 != X1 ),
% 3.47/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_209,plain,
% 3.47/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.47/0.98      | ~ l1_pre_topc(sK0)
% 3.47/0.98      | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.47/0.98      inference(unflattening,[status(thm)],[c_208]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_211,plain,
% 3.47/0.98      ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.47/0.98      inference(global_propositional_subsumption,
% 3.47/0.98                [status(thm)],
% 3.47/0.98                [c_209,c_15,c_14]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_9,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | ~ l1_pre_topc(X1) ),
% 3.47/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_229,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | sK0 != X1 ),
% 3.47/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_230,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.47/0.98      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.47/0.98      inference(unflattening,[status(thm)],[c_229]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_697,plain,
% 3.47/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.47/0.98      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_230]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_880,plain,
% 3.47/0.98      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.47/0.98      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_211,c_697]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_785,plain,
% 3.47/0.98      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.47/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_230]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_786,plain,
% 3.47/0.98      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.47/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1001,plain,
% 3.47/0.98      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.47/0.98      inference(global_propositional_subsumption,
% 3.47/0.98                [status(thm)],
% 3.47/0.98                [c_880,c_17,c_786]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1157,plain,
% 3.47/0.98      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_1001,c_701]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_2,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.47/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.47/0.98      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 3.47/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_141,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.47/0.98      | ~ r1_tarski(X2,X1)
% 3.47/0.98      | k4_subset_1(X1,X2,X0) = k4_subset_1(X1,X0,X2) ),
% 3.47/0.98      inference(bin_hyper_res,[status(thm)],[c_2,c_117]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_328,plain,
% 3.47/0.98      ( ~ r1_tarski(X0,X1)
% 3.47/0.98      | ~ r1_tarski(X2,X1)
% 3.47/0.98      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 3.47/0.98      inference(bin_hyper_res,[status(thm)],[c_141,c_306]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_695,plain,
% 3.47/0.98      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
% 3.47/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.47/0.98      | r1_tarski(X2,X0) != iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1849,plain,
% 3.47/0.98      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1))
% 3.47/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_1157,c_695]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_9792,plain,
% 3.47/0.98      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_6490,c_1849]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_11,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | ~ l1_pre_topc(X1)
% 3.47/0.98      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.47/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_217,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.98      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 3.47/0.98      | sK0 != X1 ),
% 3.47/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_218,plain,
% 3.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.47/0.98      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 3.47/0.98      inference(unflattening,[status(thm)],[c_217]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_698,plain,
% 3.47/0.98      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 3.47/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_887,plain,
% 3.47/0.98      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
% 3.47/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_696,c_698]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_2503,plain,
% 3.47/0.98      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_699,c_887]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_2521,plain,
% 3.47/0.98      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 3.47/0.98      inference(light_normalisation,[status(thm)],[c_2503,c_211]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_9794,plain,
% 3.47/0.98      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 3.47/0.98      inference(light_normalisation,[status(thm)],[c_9792,c_2521]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1612,plain,
% 3.47/0.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_tops_1(sK0,X1))) = k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X1))
% 3.47/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.47/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_1155,c_694]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_4527,plain,
% 3.47/0.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK1))
% 3.47/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_699,c_1612]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_4750,plain,
% 3.47/0.98      ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_1157,c_4527]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_4870,plain,
% 3.47/0.98      ( r1_tarski(k2_tops_1(sK0,sK1),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = iProver_top ),
% 3.47/0.98      inference(superposition,[status(thm)],[c_4750,c_704]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_10209,plain,
% 3.47/0.98      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 3.47/0.98      inference(demodulation,[status(thm)],[c_9794,c_4870]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_12,negated_conjecture,
% 3.47/0.98      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.47/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_19,plain,
% 3.47/0.98      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 3.47/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(contradiction,plain,
% 3.47/0.98      ( $false ),
% 3.47/0.98      inference(minisat,[status(thm)],[c_10209,c_19]) ).
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  ------                               Statistics
% 3.47/0.98  
% 3.47/0.98  ------ General
% 3.47/0.98  
% 3.47/0.98  abstr_ref_over_cycles:                  0
% 3.47/0.98  abstr_ref_under_cycles:                 0
% 3.47/0.98  gc_basic_clause_elim:                   0
% 3.47/0.98  forced_gc_time:                         0
% 3.47/0.98  parsing_time:                           0.008
% 3.47/0.98  unif_index_cands_time:                  0.
% 3.47/0.98  unif_index_add_time:                    0.
% 3.47/0.98  orderings_time:                         0.
% 3.47/0.98  out_proof_time:                         0.009
% 3.47/0.98  total_time:                             0.32
% 3.47/0.98  num_of_symbols:                         46
% 3.47/0.98  num_of_terms:                           9315
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing
% 3.47/0.98  
% 3.47/0.98  num_of_splits:                          0
% 3.47/0.98  num_of_split_atoms:                     0
% 3.47/0.98  num_of_reused_defs:                     0
% 3.47/0.98  num_eq_ax_congr_red:                    30
% 3.47/0.98  num_of_sem_filtered_clauses:            1
% 3.47/0.98  num_of_subtypes:                        0
% 3.47/0.98  monotx_restored_types:                  0
% 3.47/0.98  sat_num_of_epr_types:                   0
% 3.47/0.98  sat_num_of_non_cyclic_types:            0
% 3.47/0.98  sat_guarded_non_collapsed_types:        0
% 3.47/0.98  num_pure_diseq_elim:                    0
% 3.47/0.98  simp_replaced_by:                       0
% 3.47/0.98  res_preprocessed:                       81
% 3.47/0.98  prep_upred:                             0
% 3.47/0.98  prep_unflattend:                        5
% 3.47/0.98  smt_new_axioms:                         0
% 3.47/0.98  pred_elim_cands:                        2
% 3.47/0.98  pred_elim:                              2
% 3.47/0.98  pred_elim_cl:                           2
% 3.47/0.98  pred_elim_cycles:                       4
% 3.47/0.98  merged_defs:                            8
% 3.47/0.98  merged_defs_ncl:                        0
% 3.47/0.98  bin_hyper_res:                          12
% 3.47/0.98  prep_cycles:                            4
% 3.47/0.98  pred_elim_time:                         0.001
% 3.47/0.98  splitting_time:                         0.
% 3.47/0.98  sem_filter_time:                        0.
% 3.47/0.98  monotx_time:                            0.
% 3.47/0.98  subtype_inf_time:                       0.
% 3.47/0.98  
% 3.47/0.98  ------ Problem properties
% 3.47/0.98  
% 3.47/0.98  clauses:                                14
% 3.47/0.98  conjectures:                            2
% 3.47/0.98  epr:                                    1
% 3.47/0.98  horn:                                   14
% 3.47/0.98  ground:                                 3
% 3.47/0.98  unary:                                  6
% 3.47/0.98  binary:                                 5
% 3.47/0.98  lits:                                   25
% 3.47/0.98  lits_eq:                                5
% 3.47/0.98  fd_pure:                                0
% 3.47/0.98  fd_pseudo:                              0
% 3.47/0.98  fd_cond:                                0
% 3.47/0.98  fd_pseudo_cond:                         0
% 3.47/0.98  ac_symbols:                             0
% 3.47/0.98  
% 3.47/0.98  ------ Propositional Solver
% 3.47/0.98  
% 3.47/0.98  prop_solver_calls:                      30
% 3.47/0.98  prop_fast_solver_calls:                 598
% 3.47/0.98  smt_solver_calls:                       0
% 3.47/0.98  smt_fast_solver_calls:                  0
% 3.47/0.98  prop_num_of_clauses:                    4738
% 3.47/0.98  prop_preprocess_simplified:             7366
% 3.47/0.98  prop_fo_subsumed:                       4
% 3.47/0.98  prop_solver_time:                       0.
% 3.47/0.98  smt_solver_time:                        0.
% 3.47/0.98  smt_fast_solver_time:                   0.
% 3.47/0.98  prop_fast_solver_time:                  0.
% 3.47/0.98  prop_unsat_core_time:                   0.
% 3.47/0.98  
% 3.47/0.98  ------ QBF
% 3.47/0.98  
% 3.47/0.98  qbf_q_res:                              0
% 3.47/0.98  qbf_num_tautologies:                    0
% 3.47/0.98  qbf_prep_cycles:                        0
% 3.47/0.98  
% 3.47/0.98  ------ BMC1
% 3.47/0.98  
% 3.47/0.98  bmc1_current_bound:                     -1
% 3.47/0.98  bmc1_last_solved_bound:                 -1
% 3.47/0.98  bmc1_unsat_core_size:                   -1
% 3.47/0.98  bmc1_unsat_core_parents_size:           -1
% 3.47/0.98  bmc1_merge_next_fun:                    0
% 3.47/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.47/0.98  
% 3.47/0.98  ------ Instantiation
% 3.47/0.98  
% 3.47/0.98  inst_num_of_clauses:                    1420
% 3.47/0.98  inst_num_in_passive:                    284
% 3.47/0.98  inst_num_in_active:                     627
% 3.47/0.98  inst_num_in_unprocessed:                509
% 3.47/0.98  inst_num_of_loops:                      720
% 3.47/0.98  inst_num_of_learning_restarts:          0
% 3.47/0.98  inst_num_moves_active_passive:          90
% 3.47/0.98  inst_lit_activity:                      0
% 3.47/0.98  inst_lit_activity_moves:                1
% 3.47/0.98  inst_num_tautologies:                   0
% 3.47/0.98  inst_num_prop_implied:                  0
% 3.47/0.98  inst_num_existing_simplified:           0
% 3.47/0.98  inst_num_eq_res_simplified:             0
% 3.47/0.98  inst_num_child_elim:                    0
% 3.47/0.98  inst_num_of_dismatching_blockings:      537
% 3.47/0.98  inst_num_of_non_proper_insts:           1048
% 3.47/0.98  inst_num_of_duplicates:                 0
% 3.47/0.98  inst_inst_num_from_inst_to_res:         0
% 3.47/0.98  inst_dismatching_checking_time:         0.
% 3.47/0.98  
% 3.47/0.98  ------ Resolution
% 3.47/0.98  
% 3.47/0.98  res_num_of_clauses:                     0
% 3.47/0.98  res_num_in_passive:                     0
% 3.47/0.98  res_num_in_active:                      0
% 3.47/0.98  res_num_of_loops:                       85
% 3.47/0.98  res_forward_subset_subsumed:            21
% 3.47/0.98  res_backward_subset_subsumed:           0
% 3.47/0.98  res_forward_subsumed:                   0
% 3.47/0.98  res_backward_subsumed:                  0
% 3.47/0.98  res_forward_subsumption_resolution:     0
% 3.47/0.98  res_backward_subsumption_resolution:    0
% 3.47/0.98  res_clause_to_clause_subsumption:       1163
% 3.47/0.98  res_orphan_elimination:                 0
% 3.47/0.98  res_tautology_del:                      135
% 3.47/0.98  res_num_eq_res_simplified:              0
% 3.47/0.98  res_num_sel_changes:                    0
% 3.47/0.98  res_moves_from_active_to_pass:          0
% 3.47/0.98  
% 3.47/0.98  ------ Superposition
% 3.47/0.98  
% 3.47/0.98  sup_time_total:                         0.
% 3.47/0.98  sup_time_generating:                    0.
% 3.47/0.98  sup_time_sim_full:                      0.
% 3.47/0.98  sup_time_sim_immed:                     0.
% 3.47/0.98  
% 3.47/0.98  sup_num_of_clauses:                     380
% 3.47/0.98  sup_num_in_active:                      141
% 3.47/0.98  sup_num_in_passive:                     239
% 3.47/0.98  sup_num_of_loops:                       143
% 3.47/0.98  sup_fw_superposition:                   370
% 3.47/0.98  sup_bw_superposition:                   146
% 3.47/0.98  sup_immediate_simplified:               60
% 3.47/0.98  sup_given_eliminated:                   0
% 3.47/0.98  comparisons_done:                       0
% 3.47/0.98  comparisons_avoided:                    0
% 3.47/0.98  
% 3.47/0.98  ------ Simplifications
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  sim_fw_subset_subsumed:                 47
% 3.47/0.98  sim_bw_subset_subsumed:                 2
% 3.47/0.98  sim_fw_subsumed:                        1
% 3.47/0.98  sim_bw_subsumed:                        0
% 3.47/0.98  sim_fw_subsumption_res:                 0
% 3.47/0.98  sim_bw_subsumption_res:                 0
% 3.47/0.98  sim_tautology_del:                      2
% 3.47/0.98  sim_eq_tautology_del:                   5
% 3.47/0.98  sim_eq_res_simp:                        0
% 3.47/0.98  sim_fw_demodulated:                     0
% 3.47/0.98  sim_bw_demodulated:                     2
% 3.47/0.98  sim_light_normalised:                   14
% 3.47/0.98  sim_joinable_taut:                      0
% 3.47/0.98  sim_joinable_simp:                      0
% 3.47/0.98  sim_ac_normalised:                      0
% 3.47/0.98  sim_smt_subsumption:                    0
% 3.47/0.98  
%------------------------------------------------------------------------------
