%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:38 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 309 expanded)
%              Number of clauses        :   69 (  89 expanded)
%              Number of leaves         :   21 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          :  286 ( 845 expanded)
%              Number of equality atoms :  132 ( 208 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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

fof(f33,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f32,f31])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f61,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f58,f58])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f59])).

fof(f53,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_275,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_418,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_182,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_182])).

cnf(c_421,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_422,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_545,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_422])).

cnf(c_1178,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_418,c_545])).

cnf(c_5,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_148,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_149,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_151,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_149,c_12,c_11])).

cnf(c_273,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_151])).

cnf(c_1190,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1178,c_273])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_157,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_158,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_157])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
    inference(subtyping,[status(esa)],[c_158])).

cnf(c_419,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_587,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_418,c_419])).

cnf(c_1199,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1190,c_587])).

cnf(c_281,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_581,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0_42
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X1_42))
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X1_42)) != X0_42 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_925,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42))
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) != k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_927,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1)))
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_803,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) != X2_42
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X2_42
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_804,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != sK1
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_582,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0_42
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(X0_46)
    | k3_tarski(X0_46) != X0_42 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_723,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,X1_42)))
    | k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,X1_42))) != k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_724,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1)))
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_1,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_277,plain,
    ( k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X1_42) = k6_enumset1(X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_608,plain,
    ( k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42) = k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_610,plain,
    ( k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_284,plain,
    ( X0_46 != X1_46
    | k3_tarski(X0_46) = k3_tarski(X1_46) ),
    theory(equality)).

cnf(c_518,plain,
    ( k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42) != X0_46
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) = k3_tarski(X0_46) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_607,plain,
    ( k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42) != k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,sK1))
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) = k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_609,plain,
    ( k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_279,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_513,plain,
    ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) = k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_515,plain,
    ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_495,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0_42
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X1_42)) != X0_42
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X1_42)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_512,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42))
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) != k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_514,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1))
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) != k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X0_44))
    | ~ m1_subset_1(X1_42,k1_zfmisc_1(X0_44))
    | k3_tarski(k6_enumset1(X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X0_42)) = k4_subset_1(X0_44,X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,X1_42),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,X1_42))) = k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_492,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_169,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_170])).

cnf(c_310,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_0,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_140,plain,
    ( k2_tops_1(sK0,sK1) != X0
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_141,plain,
    ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_140])).

cnf(c_274,plain,
    ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_141])).

cnf(c_305,plain,
    ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1199,c_927,c_804,c_724,c_610,c_609,c_515,c_514,c_492,c_310,c_273,c_305,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:42:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 2.05/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.02  
% 2.05/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/1.02  
% 2.05/1.02  ------  iProver source info
% 2.05/1.02  
% 2.05/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.05/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/1.02  git: non_committed_changes: false
% 2.05/1.02  git: last_make_outside_of_git: false
% 2.05/1.02  
% 2.05/1.02  ------ 
% 2.05/1.02  
% 2.05/1.02  ------ Input Options
% 2.05/1.02  
% 2.05/1.02  --out_options                           all
% 2.05/1.02  --tptp_safe_out                         true
% 2.05/1.02  --problem_path                          ""
% 2.05/1.02  --include_path                          ""
% 2.05/1.02  --clausifier                            res/vclausify_rel
% 2.05/1.02  --clausifier_options                    --mode clausify
% 2.05/1.02  --stdin                                 false
% 2.05/1.02  --stats_out                             all
% 2.05/1.02  
% 2.05/1.02  ------ General Options
% 2.05/1.02  
% 2.05/1.02  --fof                                   false
% 2.05/1.02  --time_out_real                         305.
% 2.05/1.02  --time_out_virtual                      -1.
% 2.05/1.02  --symbol_type_check                     false
% 2.05/1.02  --clausify_out                          false
% 2.05/1.02  --sig_cnt_out                           false
% 2.05/1.02  --trig_cnt_out                          false
% 2.05/1.02  --trig_cnt_out_tolerance                1.
% 2.05/1.02  --trig_cnt_out_sk_spl                   false
% 2.05/1.02  --abstr_cl_out                          false
% 2.05/1.02  
% 2.05/1.02  ------ Global Options
% 2.05/1.02  
% 2.05/1.02  --schedule                              default
% 2.05/1.02  --add_important_lit                     false
% 2.05/1.02  --prop_solver_per_cl                    1000
% 2.05/1.02  --min_unsat_core                        false
% 2.05/1.02  --soft_assumptions                      false
% 2.05/1.02  --soft_lemma_size                       3
% 2.05/1.02  --prop_impl_unit_size                   0
% 2.05/1.02  --prop_impl_unit                        []
% 2.05/1.02  --share_sel_clauses                     true
% 2.05/1.02  --reset_solvers                         false
% 2.05/1.02  --bc_imp_inh                            [conj_cone]
% 2.05/1.02  --conj_cone_tolerance                   3.
% 2.05/1.02  --extra_neg_conj                        none
% 2.05/1.02  --large_theory_mode                     true
% 2.05/1.02  --prolific_symb_bound                   200
% 2.05/1.02  --lt_threshold                          2000
% 2.05/1.02  --clause_weak_htbl                      true
% 2.05/1.02  --gc_record_bc_elim                     false
% 2.05/1.02  
% 2.05/1.02  ------ Preprocessing Options
% 2.05/1.02  
% 2.05/1.02  --preprocessing_flag                    true
% 2.05/1.02  --time_out_prep_mult                    0.1
% 2.05/1.02  --splitting_mode                        input
% 2.05/1.02  --splitting_grd                         true
% 2.05/1.02  --splitting_cvd                         false
% 2.05/1.02  --splitting_cvd_svl                     false
% 2.05/1.02  --splitting_nvd                         32
% 2.05/1.02  --sub_typing                            true
% 2.05/1.02  --prep_gs_sim                           true
% 2.05/1.02  --prep_unflatten                        true
% 2.05/1.02  --prep_res_sim                          true
% 2.05/1.02  --prep_upred                            true
% 2.05/1.02  --prep_sem_filter                       exhaustive
% 2.05/1.02  --prep_sem_filter_out                   false
% 2.05/1.02  --pred_elim                             true
% 2.05/1.02  --res_sim_input                         true
% 2.05/1.02  --eq_ax_congr_red                       true
% 2.05/1.02  --pure_diseq_elim                       true
% 2.05/1.02  --brand_transform                       false
% 2.05/1.02  --non_eq_to_eq                          false
% 2.05/1.02  --prep_def_merge                        true
% 2.05/1.02  --prep_def_merge_prop_impl              false
% 2.05/1.02  --prep_def_merge_mbd                    true
% 2.05/1.02  --prep_def_merge_tr_red                 false
% 2.05/1.02  --prep_def_merge_tr_cl                  false
% 2.05/1.02  --smt_preprocessing                     true
% 2.05/1.02  --smt_ac_axioms                         fast
% 2.05/1.02  --preprocessed_out                      false
% 2.05/1.02  --preprocessed_stats                    false
% 2.05/1.02  
% 2.05/1.02  ------ Abstraction refinement Options
% 2.05/1.02  
% 2.05/1.02  --abstr_ref                             []
% 2.05/1.02  --abstr_ref_prep                        false
% 2.05/1.02  --abstr_ref_until_sat                   false
% 2.05/1.02  --abstr_ref_sig_restrict                funpre
% 2.05/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/1.02  --abstr_ref_under                       []
% 2.05/1.02  
% 2.05/1.02  ------ SAT Options
% 2.05/1.02  
% 2.05/1.02  --sat_mode                              false
% 2.05/1.02  --sat_fm_restart_options                ""
% 2.05/1.02  --sat_gr_def                            false
% 2.05/1.02  --sat_epr_types                         true
% 2.05/1.02  --sat_non_cyclic_types                  false
% 2.05/1.02  --sat_finite_models                     false
% 2.05/1.02  --sat_fm_lemmas                         false
% 2.05/1.02  --sat_fm_prep                           false
% 2.05/1.02  --sat_fm_uc_incr                        true
% 2.05/1.02  --sat_out_model                         small
% 2.05/1.02  --sat_out_clauses                       false
% 2.05/1.02  
% 2.05/1.02  ------ QBF Options
% 2.05/1.02  
% 2.05/1.02  --qbf_mode                              false
% 2.05/1.02  --qbf_elim_univ                         false
% 2.05/1.02  --qbf_dom_inst                          none
% 2.05/1.02  --qbf_dom_pre_inst                      false
% 2.05/1.02  --qbf_sk_in                             false
% 2.05/1.02  --qbf_pred_elim                         true
% 2.05/1.02  --qbf_split                             512
% 2.05/1.02  
% 2.05/1.02  ------ BMC1 Options
% 2.05/1.02  
% 2.05/1.02  --bmc1_incremental                      false
% 2.05/1.02  --bmc1_axioms                           reachable_all
% 2.05/1.02  --bmc1_min_bound                        0
% 2.05/1.02  --bmc1_max_bound                        -1
% 2.05/1.02  --bmc1_max_bound_default                -1
% 2.05/1.02  --bmc1_symbol_reachability              true
% 2.05/1.02  --bmc1_property_lemmas                  false
% 2.05/1.02  --bmc1_k_induction                      false
% 2.05/1.02  --bmc1_non_equiv_states                 false
% 2.05/1.02  --bmc1_deadlock                         false
% 2.05/1.02  --bmc1_ucm                              false
% 2.05/1.02  --bmc1_add_unsat_core                   none
% 2.05/1.02  --bmc1_unsat_core_children              false
% 2.05/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/1.02  --bmc1_out_stat                         full
% 2.05/1.02  --bmc1_ground_init                      false
% 2.05/1.02  --bmc1_pre_inst_next_state              false
% 2.05/1.02  --bmc1_pre_inst_state                   false
% 2.05/1.02  --bmc1_pre_inst_reach_state             false
% 2.05/1.02  --bmc1_out_unsat_core                   false
% 2.05/1.02  --bmc1_aig_witness_out                  false
% 2.05/1.02  --bmc1_verbose                          false
% 2.05/1.02  --bmc1_dump_clauses_tptp                false
% 2.05/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.05/1.02  --bmc1_dump_file                        -
% 2.05/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.05/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.05/1.02  --bmc1_ucm_extend_mode                  1
% 2.05/1.02  --bmc1_ucm_init_mode                    2
% 2.05/1.02  --bmc1_ucm_cone_mode                    none
% 2.05/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.05/1.02  --bmc1_ucm_relax_model                  4
% 2.05/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.05/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/1.02  --bmc1_ucm_layered_model                none
% 2.05/1.02  --bmc1_ucm_max_lemma_size               10
% 2.05/1.02  
% 2.05/1.02  ------ AIG Options
% 2.05/1.02  
% 2.05/1.02  --aig_mode                              false
% 2.05/1.02  
% 2.05/1.02  ------ Instantiation Options
% 2.05/1.02  
% 2.05/1.02  --instantiation_flag                    true
% 2.05/1.02  --inst_sos_flag                         false
% 2.05/1.02  --inst_sos_phase                        true
% 2.05/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/1.02  --inst_lit_sel_side                     num_symb
% 2.05/1.02  --inst_solver_per_active                1400
% 2.05/1.02  --inst_solver_calls_frac                1.
% 2.05/1.02  --inst_passive_queue_type               priority_queues
% 2.05/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/1.02  --inst_passive_queues_freq              [25;2]
% 2.05/1.02  --inst_dismatching                      true
% 2.05/1.02  --inst_eager_unprocessed_to_passive     true
% 2.05/1.02  --inst_prop_sim_given                   true
% 2.05/1.02  --inst_prop_sim_new                     false
% 2.05/1.02  --inst_subs_new                         false
% 2.05/1.02  --inst_eq_res_simp                      false
% 2.05/1.02  --inst_subs_given                       false
% 2.05/1.02  --inst_orphan_elimination               true
% 2.05/1.02  --inst_learning_loop_flag               true
% 2.05/1.02  --inst_learning_start                   3000
% 2.05/1.02  --inst_learning_factor                  2
% 2.05/1.02  --inst_start_prop_sim_after_learn       3
% 2.05/1.02  --inst_sel_renew                        solver
% 2.05/1.02  --inst_lit_activity_flag                true
% 2.05/1.02  --inst_restr_to_given                   false
% 2.05/1.02  --inst_activity_threshold               500
% 2.05/1.02  --inst_out_proof                        true
% 2.05/1.02  
% 2.05/1.02  ------ Resolution Options
% 2.05/1.02  
% 2.05/1.02  --resolution_flag                       true
% 2.05/1.02  --res_lit_sel                           adaptive
% 2.05/1.02  --res_lit_sel_side                      none
% 2.05/1.02  --res_ordering                          kbo
% 2.05/1.02  --res_to_prop_solver                    active
% 2.05/1.02  --res_prop_simpl_new                    false
% 2.05/1.02  --res_prop_simpl_given                  true
% 2.05/1.02  --res_passive_queue_type                priority_queues
% 2.05/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/1.02  --res_passive_queues_freq               [15;5]
% 2.05/1.02  --res_forward_subs                      full
% 2.05/1.02  --res_backward_subs                     full
% 2.05/1.02  --res_forward_subs_resolution           true
% 2.05/1.02  --res_backward_subs_resolution          true
% 2.05/1.02  --res_orphan_elimination                true
% 2.05/1.02  --res_time_limit                        2.
% 2.05/1.02  --res_out_proof                         true
% 2.05/1.02  
% 2.05/1.02  ------ Superposition Options
% 2.05/1.02  
% 2.05/1.02  --superposition_flag                    true
% 2.05/1.02  --sup_passive_queue_type                priority_queues
% 2.05/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.05/1.02  --demod_completeness_check              fast
% 2.05/1.02  --demod_use_ground                      true
% 2.05/1.02  --sup_to_prop_solver                    passive
% 2.05/1.02  --sup_prop_simpl_new                    true
% 2.05/1.02  --sup_prop_simpl_given                  true
% 2.05/1.02  --sup_fun_splitting                     false
% 2.05/1.02  --sup_smt_interval                      50000
% 2.05/1.02  
% 2.05/1.02  ------ Superposition Simplification Setup
% 2.05/1.02  
% 2.05/1.02  --sup_indices_passive                   []
% 2.05/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.02  --sup_full_bw                           [BwDemod]
% 2.05/1.02  --sup_immed_triv                        [TrivRules]
% 2.05/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.02  --sup_immed_bw_main                     []
% 2.05/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.02  
% 2.05/1.02  ------ Combination Options
% 2.05/1.02  
% 2.05/1.02  --comb_res_mult                         3
% 2.05/1.02  --comb_sup_mult                         2
% 2.05/1.02  --comb_inst_mult                        10
% 2.05/1.02  
% 2.05/1.02  ------ Debug Options
% 2.05/1.02  
% 2.05/1.02  --dbg_backtrace                         false
% 2.05/1.02  --dbg_dump_prop_clauses                 false
% 2.05/1.02  --dbg_dump_prop_clauses_file            -
% 2.05/1.02  --dbg_out_stat                          false
% 2.05/1.02  ------ Parsing...
% 2.05/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/1.02  
% 2.05/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.05/1.02  
% 2.05/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/1.02  
% 2.05/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/1.02  ------ Proving...
% 2.05/1.02  ------ Problem Properties 
% 2.05/1.02  
% 2.05/1.02  
% 2.05/1.02  clauses                                 9
% 2.05/1.02  conjectures                             1
% 2.05/1.02  EPR                                     0
% 2.05/1.02  Horn                                    9
% 2.05/1.02  unary                                   4
% 2.05/1.02  binary                                  4
% 2.05/1.02  lits                                    15
% 2.05/1.02  lits eq                                 6
% 2.05/1.02  fd_pure                                 0
% 2.05/1.02  fd_pseudo                               0
% 2.05/1.02  fd_cond                                 0
% 2.05/1.02  fd_pseudo_cond                          0
% 2.05/1.02  AC symbols                              0
% 2.05/1.02  
% 2.05/1.02  ------ Schedule dynamic 5 is on 
% 2.05/1.02  
% 2.05/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/1.02  
% 2.05/1.02  
% 2.05/1.02  ------ 
% 2.05/1.02  Current options:
% 2.05/1.02  ------ 
% 2.05/1.02  
% 2.05/1.02  ------ Input Options
% 2.05/1.02  
% 2.05/1.02  --out_options                           all
% 2.05/1.02  --tptp_safe_out                         true
% 2.05/1.02  --problem_path                          ""
% 2.05/1.02  --include_path                          ""
% 2.05/1.02  --clausifier                            res/vclausify_rel
% 2.05/1.02  --clausifier_options                    --mode clausify
% 2.05/1.02  --stdin                                 false
% 2.05/1.02  --stats_out                             all
% 2.05/1.02  
% 2.05/1.02  ------ General Options
% 2.05/1.02  
% 2.05/1.02  --fof                                   false
% 2.05/1.02  --time_out_real                         305.
% 2.05/1.02  --time_out_virtual                      -1.
% 2.05/1.02  --symbol_type_check                     false
% 2.05/1.02  --clausify_out                          false
% 2.05/1.02  --sig_cnt_out                           false
% 2.05/1.02  --trig_cnt_out                          false
% 2.05/1.02  --trig_cnt_out_tolerance                1.
% 2.05/1.02  --trig_cnt_out_sk_spl                   false
% 2.05/1.02  --abstr_cl_out                          false
% 2.05/1.02  
% 2.05/1.02  ------ Global Options
% 2.05/1.02  
% 2.05/1.02  --schedule                              default
% 2.05/1.02  --add_important_lit                     false
% 2.05/1.02  --prop_solver_per_cl                    1000
% 2.05/1.02  --min_unsat_core                        false
% 2.05/1.02  --soft_assumptions                      false
% 2.05/1.02  --soft_lemma_size                       3
% 2.05/1.02  --prop_impl_unit_size                   0
% 2.05/1.02  --prop_impl_unit                        []
% 2.05/1.02  --share_sel_clauses                     true
% 2.05/1.02  --reset_solvers                         false
% 2.05/1.02  --bc_imp_inh                            [conj_cone]
% 2.05/1.02  --conj_cone_tolerance                   3.
% 2.05/1.02  --extra_neg_conj                        none
% 2.05/1.02  --large_theory_mode                     true
% 2.05/1.02  --prolific_symb_bound                   200
% 2.05/1.02  --lt_threshold                          2000
% 2.05/1.02  --clause_weak_htbl                      true
% 2.05/1.02  --gc_record_bc_elim                     false
% 2.05/1.02  
% 2.05/1.02  ------ Preprocessing Options
% 2.05/1.02  
% 2.05/1.02  --preprocessing_flag                    true
% 2.05/1.02  --time_out_prep_mult                    0.1
% 2.05/1.02  --splitting_mode                        input
% 2.05/1.02  --splitting_grd                         true
% 2.05/1.02  --splitting_cvd                         false
% 2.05/1.02  --splitting_cvd_svl                     false
% 2.05/1.02  --splitting_nvd                         32
% 2.05/1.02  --sub_typing                            true
% 2.05/1.02  --prep_gs_sim                           true
% 2.05/1.02  --prep_unflatten                        true
% 2.05/1.02  --prep_res_sim                          true
% 2.05/1.02  --prep_upred                            true
% 2.05/1.02  --prep_sem_filter                       exhaustive
% 2.05/1.02  --prep_sem_filter_out                   false
% 2.05/1.02  --pred_elim                             true
% 2.05/1.02  --res_sim_input                         true
% 2.05/1.02  --eq_ax_congr_red                       true
% 2.05/1.02  --pure_diseq_elim                       true
% 2.05/1.02  --brand_transform                       false
% 2.05/1.02  --non_eq_to_eq                          false
% 2.05/1.02  --prep_def_merge                        true
% 2.05/1.02  --prep_def_merge_prop_impl              false
% 2.05/1.02  --prep_def_merge_mbd                    true
% 2.05/1.02  --prep_def_merge_tr_red                 false
% 2.05/1.02  --prep_def_merge_tr_cl                  false
% 2.05/1.02  --smt_preprocessing                     true
% 2.05/1.02  --smt_ac_axioms                         fast
% 2.05/1.02  --preprocessed_out                      false
% 2.05/1.02  --preprocessed_stats                    false
% 2.05/1.02  
% 2.05/1.02  ------ Abstraction refinement Options
% 2.05/1.02  
% 2.05/1.02  --abstr_ref                             []
% 2.05/1.02  --abstr_ref_prep                        false
% 2.05/1.02  --abstr_ref_until_sat                   false
% 2.05/1.02  --abstr_ref_sig_restrict                funpre
% 2.05/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/1.02  --abstr_ref_under                       []
% 2.05/1.02  
% 2.05/1.02  ------ SAT Options
% 2.05/1.02  
% 2.05/1.02  --sat_mode                              false
% 2.05/1.02  --sat_fm_restart_options                ""
% 2.05/1.02  --sat_gr_def                            false
% 2.05/1.02  --sat_epr_types                         true
% 2.05/1.02  --sat_non_cyclic_types                  false
% 2.05/1.02  --sat_finite_models                     false
% 2.05/1.02  --sat_fm_lemmas                         false
% 2.05/1.02  --sat_fm_prep                           false
% 2.05/1.02  --sat_fm_uc_incr                        true
% 2.05/1.02  --sat_out_model                         small
% 2.05/1.02  --sat_out_clauses                       false
% 2.05/1.02  
% 2.05/1.02  ------ QBF Options
% 2.05/1.02  
% 2.05/1.02  --qbf_mode                              false
% 2.05/1.02  --qbf_elim_univ                         false
% 2.05/1.02  --qbf_dom_inst                          none
% 2.05/1.02  --qbf_dom_pre_inst                      false
% 2.05/1.02  --qbf_sk_in                             false
% 2.05/1.02  --qbf_pred_elim                         true
% 2.05/1.02  --qbf_split                             512
% 2.05/1.02  
% 2.05/1.02  ------ BMC1 Options
% 2.05/1.02  
% 2.05/1.02  --bmc1_incremental                      false
% 2.05/1.02  --bmc1_axioms                           reachable_all
% 2.05/1.02  --bmc1_min_bound                        0
% 2.05/1.02  --bmc1_max_bound                        -1
% 2.05/1.02  --bmc1_max_bound_default                -1
% 2.05/1.02  --bmc1_symbol_reachability              true
% 2.05/1.02  --bmc1_property_lemmas                  false
% 2.05/1.02  --bmc1_k_induction                      false
% 2.05/1.02  --bmc1_non_equiv_states                 false
% 2.05/1.02  --bmc1_deadlock                         false
% 2.05/1.02  --bmc1_ucm                              false
% 2.05/1.02  --bmc1_add_unsat_core                   none
% 2.05/1.02  --bmc1_unsat_core_children              false
% 2.05/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/1.02  --bmc1_out_stat                         full
% 2.05/1.02  --bmc1_ground_init                      false
% 2.05/1.02  --bmc1_pre_inst_next_state              false
% 2.05/1.02  --bmc1_pre_inst_state                   false
% 2.05/1.02  --bmc1_pre_inst_reach_state             false
% 2.05/1.02  --bmc1_out_unsat_core                   false
% 2.05/1.02  --bmc1_aig_witness_out                  false
% 2.05/1.02  --bmc1_verbose                          false
% 2.05/1.02  --bmc1_dump_clauses_tptp                false
% 2.05/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.05/1.02  --bmc1_dump_file                        -
% 2.05/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.05/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.05/1.02  --bmc1_ucm_extend_mode                  1
% 2.05/1.02  --bmc1_ucm_init_mode                    2
% 2.05/1.02  --bmc1_ucm_cone_mode                    none
% 2.05/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.05/1.02  --bmc1_ucm_relax_model                  4
% 2.05/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.05/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/1.02  --bmc1_ucm_layered_model                none
% 2.05/1.02  --bmc1_ucm_max_lemma_size               10
% 2.05/1.02  
% 2.05/1.02  ------ AIG Options
% 2.05/1.02  
% 2.05/1.02  --aig_mode                              false
% 2.05/1.02  
% 2.05/1.02  ------ Instantiation Options
% 2.05/1.02  
% 2.05/1.02  --instantiation_flag                    true
% 2.05/1.02  --inst_sos_flag                         false
% 2.05/1.02  --inst_sos_phase                        true
% 2.05/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/1.02  --inst_lit_sel_side                     none
% 2.05/1.02  --inst_solver_per_active                1400
% 2.05/1.02  --inst_solver_calls_frac                1.
% 2.05/1.02  --inst_passive_queue_type               priority_queues
% 2.05/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/1.02  --inst_passive_queues_freq              [25;2]
% 2.05/1.02  --inst_dismatching                      true
% 2.05/1.02  --inst_eager_unprocessed_to_passive     true
% 2.05/1.02  --inst_prop_sim_given                   true
% 2.05/1.02  --inst_prop_sim_new                     false
% 2.05/1.02  --inst_subs_new                         false
% 2.05/1.02  --inst_eq_res_simp                      false
% 2.05/1.02  --inst_subs_given                       false
% 2.05/1.02  --inst_orphan_elimination               true
% 2.05/1.02  --inst_learning_loop_flag               true
% 2.05/1.02  --inst_learning_start                   3000
% 2.05/1.02  --inst_learning_factor                  2
% 2.05/1.02  --inst_start_prop_sim_after_learn       3
% 2.05/1.02  --inst_sel_renew                        solver
% 2.05/1.02  --inst_lit_activity_flag                true
% 2.05/1.02  --inst_restr_to_given                   false
% 2.05/1.02  --inst_activity_threshold               500
% 2.05/1.02  --inst_out_proof                        true
% 2.05/1.02  
% 2.05/1.02  ------ Resolution Options
% 2.05/1.02  
% 2.05/1.02  --resolution_flag                       false
% 2.05/1.02  --res_lit_sel                           adaptive
% 2.05/1.02  --res_lit_sel_side                      none
% 2.05/1.02  --res_ordering                          kbo
% 2.05/1.02  --res_to_prop_solver                    active
% 2.05/1.02  --res_prop_simpl_new                    false
% 2.05/1.02  --res_prop_simpl_given                  true
% 2.05/1.02  --res_passive_queue_type                priority_queues
% 2.05/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/1.02  --res_passive_queues_freq               [15;5]
% 2.05/1.02  --res_forward_subs                      full
% 2.05/1.02  --res_backward_subs                     full
% 2.05/1.02  --res_forward_subs_resolution           true
% 2.05/1.02  --res_backward_subs_resolution          true
% 2.05/1.02  --res_orphan_elimination                true
% 2.05/1.02  --res_time_limit                        2.
% 2.05/1.02  --res_out_proof                         true
% 2.05/1.02  
% 2.05/1.02  ------ Superposition Options
% 2.05/1.02  
% 2.05/1.02  --superposition_flag                    true
% 2.05/1.02  --sup_passive_queue_type                priority_queues
% 2.05/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.05/1.02  --demod_completeness_check              fast
% 2.05/1.02  --demod_use_ground                      true
% 2.05/1.02  --sup_to_prop_solver                    passive
% 2.05/1.02  --sup_prop_simpl_new                    true
% 2.05/1.02  --sup_prop_simpl_given                  true
% 2.05/1.02  --sup_fun_splitting                     false
% 2.05/1.02  --sup_smt_interval                      50000
% 2.05/1.02  
% 2.05/1.02  ------ Superposition Simplification Setup
% 2.05/1.02  
% 2.05/1.02  --sup_indices_passive                   []
% 2.05/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.02  --sup_full_bw                           [BwDemod]
% 2.05/1.02  --sup_immed_triv                        [TrivRules]
% 2.05/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.02  --sup_immed_bw_main                     []
% 2.05/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/1.02  
% 2.05/1.02  ------ Combination Options
% 2.05/1.02  
% 2.05/1.02  --comb_res_mult                         3
% 2.05/1.02  --comb_sup_mult                         2
% 2.05/1.02  --comb_inst_mult                        10
% 2.05/1.02  
% 2.05/1.02  ------ Debug Options
% 2.05/1.02  
% 2.05/1.02  --dbg_backtrace                         false
% 2.05/1.02  --dbg_dump_prop_clauses                 false
% 2.05/1.02  --dbg_dump_prop_clauses_file            -
% 2.05/1.02  --dbg_out_stat                          false
% 2.05/1.02  
% 2.05/1.02  
% 2.05/1.02  
% 2.05/1.02  
% 2.05/1.02  ------ Proving...
% 2.05/1.02  
% 2.05/1.02  
% 2.05/1.02  % SZS status Theorem for theBenchmark.p
% 2.05/1.02  
% 2.05/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/1.02  
% 2.05/1.02  fof(f16,conjecture,(
% 2.05/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f17,negated_conjecture,(
% 2.05/1.02    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 2.05/1.02    inference(negated_conjecture,[],[f16])).
% 2.05/1.02  
% 2.05/1.02  fof(f28,plain,(
% 2.05/1.02    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.05/1.02    inference(ennf_transformation,[],[f17])).
% 2.05/1.02  
% 2.05/1.02  fof(f29,plain,(
% 2.05/1.02    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.05/1.02    inference(flattening,[],[f28])).
% 2.05/1.02  
% 2.05/1.02  fof(f32,plain,(
% 2.05/1.02    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.05/1.02    introduced(choice_axiom,[])).
% 2.05/1.02  
% 2.05/1.02  fof(f31,plain,(
% 2.05/1.02    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.05/1.02    introduced(choice_axiom,[])).
% 2.05/1.02  
% 2.05/1.02  fof(f33,plain,(
% 2.05/1.02    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.05/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f32,f31])).
% 2.05/1.02  
% 2.05/1.02  fof(f51,plain,(
% 2.05/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.05/1.02    inference(cnf_transformation,[],[f33])).
% 2.05/1.02  
% 2.05/1.02  fof(f13,axiom,(
% 2.05/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f23,plain,(
% 2.05/1.02    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.05/1.02    inference(ennf_transformation,[],[f13])).
% 2.05/1.02  
% 2.05/1.02  fof(f24,plain,(
% 2.05/1.02    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.05/1.02    inference(flattening,[],[f23])).
% 2.05/1.02  
% 2.05/1.02  fof(f47,plain,(
% 2.05/1.02    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f24])).
% 2.05/1.02  
% 2.05/1.02  fof(f50,plain,(
% 2.05/1.02    l1_pre_topc(sK0)),
% 2.05/1.02    inference(cnf_transformation,[],[f33])).
% 2.05/1.02  
% 2.05/1.02  fof(f11,axiom,(
% 2.05/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f20,plain,(
% 2.05/1.02    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.05/1.02    inference(ennf_transformation,[],[f11])).
% 2.05/1.02  
% 2.05/1.02  fof(f21,plain,(
% 2.05/1.02    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.05/1.02    inference(flattening,[],[f20])).
% 2.05/1.02  
% 2.05/1.02  fof(f44,plain,(
% 2.05/1.02    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f21])).
% 2.05/1.02  
% 2.05/1.02  fof(f12,axiom,(
% 2.05/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f22,plain,(
% 2.05/1.02    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.02    inference(ennf_transformation,[],[f12])).
% 2.05/1.02  
% 2.05/1.02  fof(f30,plain,(
% 2.05/1.02    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.02    inference(nnf_transformation,[],[f22])).
% 2.05/1.02  
% 2.05/1.02  fof(f45,plain,(
% 2.05/1.02    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f30])).
% 2.05/1.02  
% 2.05/1.02  fof(f52,plain,(
% 2.05/1.02    v5_tops_1(sK1,sK0)),
% 2.05/1.02    inference(cnf_transformation,[],[f33])).
% 2.05/1.02  
% 2.05/1.02  fof(f15,axiom,(
% 2.05/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f27,plain,(
% 2.05/1.02    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/1.02    inference(ennf_transformation,[],[f15])).
% 2.05/1.02  
% 2.05/1.02  fof(f49,plain,(
% 2.05/1.02    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f27])).
% 2.05/1.02  
% 2.05/1.02  fof(f2,axiom,(
% 2.05/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f35,plain,(
% 2.05/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f2])).
% 2.05/1.02  
% 2.05/1.02  fof(f3,axiom,(
% 2.05/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f36,plain,(
% 2.05/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f3])).
% 2.05/1.02  
% 2.05/1.02  fof(f4,axiom,(
% 2.05/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f37,plain,(
% 2.05/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f4])).
% 2.05/1.02  
% 2.05/1.02  fof(f5,axiom,(
% 2.05/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f38,plain,(
% 2.05/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f5])).
% 2.05/1.02  
% 2.05/1.02  fof(f6,axiom,(
% 2.05/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f39,plain,(
% 2.05/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f6])).
% 2.05/1.02  
% 2.05/1.02  fof(f7,axiom,(
% 2.05/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f40,plain,(
% 2.05/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f7])).
% 2.05/1.02  
% 2.05/1.02  fof(f8,axiom,(
% 2.05/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f41,plain,(
% 2.05/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f8])).
% 2.05/1.02  
% 2.05/1.02  fof(f54,plain,(
% 2.05/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.05/1.02    inference(definition_unfolding,[],[f40,f41])).
% 2.05/1.02  
% 2.05/1.02  fof(f55,plain,(
% 2.05/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.05/1.02    inference(definition_unfolding,[],[f39,f54])).
% 2.05/1.02  
% 2.05/1.02  fof(f56,plain,(
% 2.05/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.05/1.02    inference(definition_unfolding,[],[f38,f55])).
% 2.05/1.02  
% 2.05/1.02  fof(f57,plain,(
% 2.05/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.05/1.02    inference(definition_unfolding,[],[f37,f56])).
% 2.05/1.02  
% 2.05/1.02  fof(f58,plain,(
% 2.05/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.05/1.02    inference(definition_unfolding,[],[f36,f57])).
% 2.05/1.02  
% 2.05/1.02  fof(f61,plain,(
% 2.05/1.02    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 2.05/1.02    inference(definition_unfolding,[],[f35,f58,f58])).
% 2.05/1.02  
% 2.05/1.02  fof(f10,axiom,(
% 2.05/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f18,plain,(
% 2.05/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.05/1.02    inference(ennf_transformation,[],[f10])).
% 2.05/1.02  
% 2.05/1.02  fof(f19,plain,(
% 2.05/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/1.02    inference(flattening,[],[f18])).
% 2.05/1.02  
% 2.05/1.02  fof(f43,plain,(
% 2.05/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/1.02    inference(cnf_transformation,[],[f19])).
% 2.05/1.02  
% 2.05/1.02  fof(f9,axiom,(
% 2.05/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f42,plain,(
% 2.05/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.05/1.02    inference(cnf_transformation,[],[f9])).
% 2.05/1.02  
% 2.05/1.02  fof(f59,plain,(
% 2.05/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.05/1.02    inference(definition_unfolding,[],[f42,f58])).
% 2.05/1.02  
% 2.05/1.02  fof(f62,plain,(
% 2.05/1.02    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/1.02    inference(definition_unfolding,[],[f43,f59])).
% 2.05/1.02  
% 2.05/1.02  fof(f14,axiom,(
% 2.05/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f25,plain,(
% 2.05/1.02    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.05/1.02    inference(ennf_transformation,[],[f14])).
% 2.05/1.02  
% 2.05/1.02  fof(f26,plain,(
% 2.05/1.02    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.05/1.02    inference(flattening,[],[f25])).
% 2.05/1.02  
% 2.05/1.02  fof(f48,plain,(
% 2.05/1.02    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/1.02    inference(cnf_transformation,[],[f26])).
% 2.05/1.02  
% 2.05/1.02  fof(f1,axiom,(
% 2.05/1.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.05/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/1.02  
% 2.05/1.02  fof(f34,plain,(
% 2.05/1.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.05/1.02    inference(cnf_transformation,[],[f1])).
% 2.05/1.02  
% 2.05/1.02  fof(f60,plain,(
% 2.05/1.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.05/1.02    inference(definition_unfolding,[],[f34,f59])).
% 2.05/1.02  
% 2.05/1.02  fof(f53,plain,(
% 2.05/1.02    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 2.05/1.02    inference(cnf_transformation,[],[f33])).
% 2.05/1.02  
% 2.05/1.02  cnf(c_11,negated_conjecture,
% 2.05/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.05/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_275,negated_conjecture,
% 2.05/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.05/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_418,plain,
% 2.05/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.05/1.02      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_6,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | ~ l1_pre_topc(X1) ),
% 2.05/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_12,negated_conjecture,
% 2.05/1.02      ( l1_pre_topc(sK0) ),
% 2.05/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_181,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | sK0 != X1 ),
% 2.05/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_182,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.05/1.02      inference(unflattening,[status(thm)],[c_181]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_270,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.05/1.02      inference(subtyping,[status(esa)],[c_182]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_421,plain,
% 2.05/1.02      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.05/1.02      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.05/1.02      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_3,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | ~ l1_pre_topc(X1)
% 2.05/1.02      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 2.05/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_193,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 2.05/1.02      | sK0 != X1 ),
% 2.05/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_12]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_194,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 2.05/1.02      inference(unflattening,[status(thm)],[c_193]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_269,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
% 2.05/1.02      inference(subtyping,[status(esa)],[c_194]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_422,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
% 2.05/1.02      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.05/1.02      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_545,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))
% 2.05/1.02      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.05/1.02      inference(superposition,[status(thm)],[c_421,c_422]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_1178,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 2.05/1.02      inference(superposition,[status(thm)],[c_418,c_545]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_5,plain,
% 2.05/1.02      ( ~ v5_tops_1(X0,X1)
% 2.05/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | ~ l1_pre_topc(X1)
% 2.05/1.02      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 2.05/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_10,negated_conjecture,
% 2.05/1.02      ( v5_tops_1(sK1,sK0) ),
% 2.05/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_148,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | ~ l1_pre_topc(X1)
% 2.05/1.02      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 2.05/1.02      | sK1 != X0
% 2.05/1.02      | sK0 != X1 ),
% 2.05/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_149,plain,
% 2.05/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | ~ l1_pre_topc(sK0)
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 2.05/1.02      inference(unflattening,[status(thm)],[c_148]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_151,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 2.05/1.02      inference(global_propositional_subsumption,
% 2.05/1.02                [status(thm)],
% 2.05/1.02                [c_149,c_12,c_11]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_273,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 2.05/1.02      inference(subtyping,[status(esa)],[c_151]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_1190,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 2.05/1.02      inference(light_normalisation,[status(thm)],[c_1178,c_273]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_8,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | ~ l1_pre_topc(X1)
% 2.05/1.02      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 2.05/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_157,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 2.05/1.02      | sK0 != X1 ),
% 2.05/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_158,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 2.05/1.02      inference(unflattening,[status(thm)],[c_157]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_272,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
% 2.05/1.02      inference(subtyping,[status(esa)],[c_158]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_419,plain,
% 2.05/1.02      ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
% 2.05/1.02      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.05/1.02      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_587,plain,
% 2.05/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 2.05/1.02      inference(superposition,[status(thm)],[c_418,c_419]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_1199,plain,
% 2.05/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 2.05/1.02      inference(demodulation,[status(thm)],[c_1190,c_587]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_281,plain,
% 2.05/1.02      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 2.05/1.02      theory(equality) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_581,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0_42
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X1_42))
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X1_42)) != X0_42 ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_281]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_925,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,sK1)))
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42))
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) != k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,sK1))) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_581]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_927,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1))
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1)))
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_925]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_803,plain,
% 2.05/1.02      ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) != X2_42
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X2_42
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_281]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_804,plain,
% 2.05/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != sK1
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != sK1 ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_803]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_582,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0_42
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(X0_46)
% 2.05/1.02      | k3_tarski(X0_46) != X0_42 ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_281]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_723,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42))
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,X1_42)))
% 2.05/1.02      | k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,X1_42))) != k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_582]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_724,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
% 2.05/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1)))
% 2.05/1.02      | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_723]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_1,plain,
% 2.05/1.02      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 2.05/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_277,plain,
% 2.05/1.02      ( k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X1_42) = k6_enumset1(X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X0_42) ),
% 2.05/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_608,plain,
% 2.05/1.02      ( k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42) = k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,sK1)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_277]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_610,plain,
% 2.05/1.02      ( k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_608]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_284,plain,
% 2.05/1.02      ( X0_46 != X1_46 | k3_tarski(X0_46) = k3_tarski(X1_46) ),
% 2.05/1.02      theory(equality) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_518,plain,
% 2.05/1.02      ( k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42) != X0_46
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) = k3_tarski(X0_46) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_284]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_607,plain,
% 2.05/1.02      ( k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42) != k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,sK1))
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) = k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,sK1))) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_518]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_609,plain,
% 2.05/1.02      ( k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_607]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_279,plain,( X0_42 = X0_42 ),theory(equality) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_513,plain,
% 2.05/1.02      ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) = k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_279]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_515,plain,
% 2.05/1.02      ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_513]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_495,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0_42
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X1_42)) != X0_42
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X1_42)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_281]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_512,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42))
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) != k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_495]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_514,plain,
% 2.05/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1))
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 2.05/1.02      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) != k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_512]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_2,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.05/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.05/1.02      | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 2.05/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_276,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X0_44))
% 2.05/1.02      | ~ m1_subset_1(X1_42,k1_zfmisc_1(X0_44))
% 2.05/1.02      | k3_tarski(k6_enumset1(X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X0_42)) = k4_subset_1(X0_44,X1_42,X0_42) ),
% 2.05/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_490,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | ~ m1_subset_1(k2_tops_1(sK0,X1_42),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | k3_tarski(k6_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,k2_tops_1(sK0,X1_42))) = k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_276]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_492,plain,
% 2.05/1.02      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_490]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_7,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | ~ l1_pre_topc(X1) ),
% 2.05/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_169,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/1.02      | sK0 != X1 ),
% 2.05/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_170,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.05/1.02      inference(unflattening,[status(thm)],[c_169]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_271,plain,
% 2.05/1.02      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | m1_subset_1(k2_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.05/1.02      inference(subtyping,[status(esa)],[c_170]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_310,plain,
% 2.05/1.02      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.05/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_271]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_0,plain,
% 2.05/1.02      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 2.05/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_9,negated_conjecture,
% 2.05/1.02      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 2.05/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_140,plain,
% 2.05/1.02      ( k2_tops_1(sK0,sK1) != X0
% 2.05/1.02      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 2.05/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_141,plain,
% 2.05/1.02      ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 2.05/1.02      inference(unflattening,[status(thm)],[c_140]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_274,plain,
% 2.05/1.02      ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0_42)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 2.05/1.02      inference(subtyping,[status(esa)],[c_141]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(c_305,plain,
% 2.05/1.02      ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 2.05/1.02      inference(instantiation,[status(thm)],[c_274]) ).
% 2.05/1.02  
% 2.05/1.02  cnf(contradiction,plain,
% 2.05/1.02      ( $false ),
% 2.05/1.02      inference(minisat,
% 2.05/1.02                [status(thm)],
% 2.05/1.02                [c_1199,c_927,c_804,c_724,c_610,c_609,c_515,c_514,c_492,
% 2.05/1.02                 c_310,c_273,c_305,c_11]) ).
% 2.05/1.02  
% 2.05/1.02  
% 2.05/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/1.02  
% 2.05/1.02  ------                               Statistics
% 2.05/1.02  
% 2.05/1.02  ------ General
% 2.05/1.02  
% 2.05/1.02  abstr_ref_over_cycles:                  0
% 2.05/1.02  abstr_ref_under_cycles:                 0
% 2.05/1.02  gc_basic_clause_elim:                   0
% 2.05/1.02  forced_gc_time:                         0
% 2.05/1.02  parsing_time:                           0.009
% 2.05/1.02  unif_index_cands_time:                  0.
% 2.05/1.02  unif_index_add_time:                    0.
% 2.05/1.02  orderings_time:                         0.
% 2.05/1.02  out_proof_time:                         0.025
% 2.05/1.02  total_time:                             0.134
% 2.05/1.02  num_of_symbols:                         47
% 2.05/1.02  num_of_terms:                           1513
% 2.05/1.02  
% 2.05/1.02  ------ Preprocessing
% 2.05/1.02  
% 2.05/1.02  num_of_splits:                          0
% 2.05/1.02  num_of_split_atoms:                     0
% 2.05/1.02  num_of_reused_defs:                     0
% 2.05/1.02  num_eq_ax_congr_red:                    20
% 2.05/1.02  num_of_sem_filtered_clauses:            1
% 2.05/1.02  num_of_subtypes:                        5
% 2.05/1.02  monotx_restored_types:                  0
% 2.05/1.02  sat_num_of_epr_types:                   0
% 2.05/1.02  sat_num_of_non_cyclic_types:            0
% 2.05/1.02  sat_guarded_non_collapsed_types:        0
% 2.05/1.02  num_pure_diseq_elim:                    0
% 2.05/1.02  simp_replaced_by:                       0
% 2.05/1.02  res_preprocessed:                       63
% 2.05/1.02  prep_upred:                             0
% 2.05/1.02  prep_unflattend:                        7
% 2.05/1.02  smt_new_axioms:                         0
% 2.05/1.02  pred_elim_cands:                        1
% 2.05/1.02  pred_elim:                              3
% 2.05/1.02  pred_elim_cl:                           4
% 2.05/1.02  pred_elim_cycles:                       5
% 2.05/1.02  merged_defs:                            0
% 2.05/1.02  merged_defs_ncl:                        0
% 2.05/1.02  bin_hyper_res:                          0
% 2.05/1.02  prep_cycles:                            4
% 2.05/1.02  pred_elim_time:                         0.002
% 2.05/1.02  splitting_time:                         0.
% 2.05/1.02  sem_filter_time:                        0.
% 2.05/1.02  monotx_time:                            0.
% 2.05/1.02  subtype_inf_time:                       0.
% 2.05/1.02  
% 2.05/1.02  ------ Problem properties
% 2.05/1.02  
% 2.05/1.02  clauses:                                9
% 2.05/1.02  conjectures:                            1
% 2.05/1.02  epr:                                    0
% 2.05/1.02  horn:                                   9
% 2.05/1.02  ground:                                 2
% 2.05/1.02  unary:                                  4
% 2.05/1.02  binary:                                 4
% 2.05/1.02  lits:                                   15
% 2.05/1.02  lits_eq:                                6
% 2.05/1.02  fd_pure:                                0
% 2.05/1.02  fd_pseudo:                              0
% 2.05/1.02  fd_cond:                                0
% 2.05/1.02  fd_pseudo_cond:                         0
% 2.05/1.02  ac_symbols:                             0
% 2.05/1.02  
% 2.05/1.02  ------ Propositional Solver
% 2.05/1.02  
% 2.05/1.02  prop_solver_calls:                      27
% 2.05/1.02  prop_fast_solver_calls:                 310
% 2.05/1.02  smt_solver_calls:                       0
% 2.05/1.02  smt_fast_solver_calls:                  0
% 2.05/1.02  prop_num_of_clauses:                    471
% 2.05/1.02  prop_preprocess_simplified:             1898
% 2.05/1.02  prop_fo_subsumed:                       2
% 2.05/1.02  prop_solver_time:                       0.
% 2.05/1.02  smt_solver_time:                        0.
% 2.05/1.02  smt_fast_solver_time:                   0.
% 2.05/1.02  prop_fast_solver_time:                  0.
% 2.05/1.02  prop_unsat_core_time:                   0.
% 2.05/1.02  
% 2.05/1.02  ------ QBF
% 2.05/1.02  
% 2.05/1.02  qbf_q_res:                              0
% 2.05/1.02  qbf_num_tautologies:                    0
% 2.05/1.02  qbf_prep_cycles:                        0
% 2.05/1.02  
% 2.05/1.02  ------ BMC1
% 2.05/1.02  
% 2.05/1.02  bmc1_current_bound:                     -1
% 2.05/1.02  bmc1_last_solved_bound:                 -1
% 2.05/1.02  bmc1_unsat_core_size:                   -1
% 2.05/1.02  bmc1_unsat_core_parents_size:           -1
% 2.05/1.02  bmc1_merge_next_fun:                    0
% 2.05/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.05/1.02  
% 2.05/1.02  ------ Instantiation
% 2.05/1.02  
% 2.05/1.02  inst_num_of_clauses:                    196
% 2.05/1.02  inst_num_in_passive:                    86
% 2.05/1.02  inst_num_in_active:                     95
% 2.05/1.02  inst_num_in_unprocessed:                17
% 2.05/1.02  inst_num_of_loops:                      100
% 2.05/1.02  inst_num_of_learning_restarts:          0
% 2.05/1.02  inst_num_moves_active_passive:          1
% 2.05/1.02  inst_lit_activity:                      0
% 2.05/1.02  inst_lit_activity_moves:                0
% 2.05/1.02  inst_num_tautologies:                   0
% 2.05/1.02  inst_num_prop_implied:                  0
% 2.05/1.02  inst_num_existing_simplified:           0
% 2.05/1.02  inst_num_eq_res_simplified:             0
% 2.05/1.02  inst_num_child_elim:                    0
% 2.05/1.02  inst_num_of_dismatching_blockings:      14
% 2.05/1.02  inst_num_of_non_proper_insts:           141
% 2.05/1.02  inst_num_of_duplicates:                 0
% 2.05/1.02  inst_inst_num_from_inst_to_res:         0
% 2.05/1.02  inst_dismatching_checking_time:         0.
% 2.05/1.02  
% 2.05/1.02  ------ Resolution
% 2.05/1.02  
% 2.05/1.02  res_num_of_clauses:                     0
% 2.05/1.02  res_num_in_passive:                     0
% 2.05/1.02  res_num_in_active:                      0
% 2.05/1.02  res_num_of_loops:                       67
% 2.05/1.02  res_forward_subset_subsumed:            13
% 2.05/1.02  res_backward_subset_subsumed:           4
% 2.05/1.02  res_forward_subsumed:                   0
% 2.05/1.02  res_backward_subsumed:                  0
% 2.05/1.02  res_forward_subsumption_resolution:     0
% 2.05/1.02  res_backward_subsumption_resolution:    0
% 2.05/1.02  res_clause_to_clause_subsumption:       68
% 2.05/1.02  res_orphan_elimination:                 0
% 2.05/1.02  res_tautology_del:                      32
% 2.05/1.02  res_num_eq_res_simplified:              0
% 2.05/1.02  res_num_sel_changes:                    0
% 2.05/1.02  res_moves_from_active_to_pass:          0
% 2.05/1.02  
% 2.05/1.02  ------ Superposition
% 2.05/1.02  
% 2.05/1.02  sup_time_total:                         0.
% 2.05/1.02  sup_time_generating:                    0.
% 2.05/1.02  sup_time_sim_full:                      0.
% 2.05/1.02  sup_time_sim_immed:                     0.
% 2.05/1.02  
% 2.05/1.02  sup_num_of_clauses:                     31
% 2.05/1.02  sup_num_in_active:                      17
% 2.05/1.02  sup_num_in_passive:                     14
% 2.05/1.02  sup_num_of_loops:                       19
% 2.05/1.02  sup_fw_superposition:                   27
% 2.05/1.02  sup_bw_superposition:                   0
% 2.05/1.02  sup_immediate_simplified:               1
% 2.05/1.02  sup_given_eliminated:                   0
% 2.05/1.02  comparisons_done:                       0
% 2.05/1.02  comparisons_avoided:                    0
% 2.05/1.02  
% 2.05/1.02  ------ Simplifications
% 2.05/1.02  
% 2.05/1.02  
% 2.05/1.02  sim_fw_subset_subsumed:                 0
% 2.05/1.02  sim_bw_subset_subsumed:                 0
% 2.05/1.02  sim_fw_subsumed:                        0
% 2.05/1.02  sim_bw_subsumed:                        0
% 2.05/1.02  sim_fw_subsumption_res:                 0
% 2.05/1.02  sim_bw_subsumption_res:                 0
% 2.05/1.02  sim_tautology_del:                      0
% 2.05/1.02  sim_eq_tautology_del:                   0
% 2.05/1.02  sim_eq_res_simp:                        0
% 2.05/1.02  sim_fw_demodulated:                     0
% 2.05/1.02  sim_bw_demodulated:                     2
% 2.05/1.02  sim_light_normalised:                   2
% 2.05/1.02  sim_joinable_taut:                      0
% 2.05/1.02  sim_joinable_simp:                      0
% 2.05/1.02  sim_ac_normalised:                      0
% 2.05/1.02  sim_smt_subsumption:                    0
% 2.05/1.02  
%------------------------------------------------------------------------------
