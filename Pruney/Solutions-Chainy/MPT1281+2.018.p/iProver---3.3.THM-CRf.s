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
% DateTime   : Thu Dec  3 12:15:42 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 810 expanded)
%              Number of clauses        :   87 ( 264 expanded)
%              Number of leaves         :   16 ( 192 expanded)
%              Depth                    :   22
%              Number of atoms          :  351 (2573 expanded)
%              Number of equality atoms :  122 ( 329 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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

fof(f40,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f39,f38])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
          | ~ v5_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
          | ~ v5_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f62,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_961,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_963,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1578,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_963])).

cnf(c_18,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_326,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_327,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_327])).

cnf(c_408,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_410,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_19])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_964,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_957,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_1665,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_957])).

cnf(c_2128,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_1665])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_1020,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_1021,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_1149,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1858,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_1859,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1858])).

cnf(c_2227,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2128,c_22,c_1021,c_1859])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_966,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2364,plain,
    ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_2227,c_966])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_967,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2587,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_967])).

cnf(c_3821,plain,
    ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),X0)) = X0
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2587,c_966])).

cnf(c_4319,plain,
    ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1578,c_3821])).

cnf(c_5,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_965,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4432,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4319,c_965])).

cnf(c_15,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_287,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_tops_1(X1,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_288,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_288])).

cnf(c_416,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_418,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_19])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_959,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_1332,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_418,c_959])).

cnf(c_1007,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_1008,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1007])).

cnf(c_2036,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1332,c_22,c_1008])).

cnf(c_2040,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2036,c_963])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_163,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_164,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_163])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k4_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_164])).

cnf(c_487,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_488,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_487])).

cnf(c_515,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k4_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_193,c_488])).

cnf(c_955,plain,
    ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_2242,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2040,c_955])).

cnf(c_8979,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4432,c_2242])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_960,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_1799,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_960])).

cnf(c_3823,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2587,c_1799])).

cnf(c_3826,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3823,c_410,c_418])).

cnf(c_4064,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3826,c_1578])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_164])).

cnf(c_516,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_194,c_488])).

cnf(c_954,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_2046,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),X0))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2040,c_954])).

cnf(c_5258,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_4432,c_2046])).

cnf(c_8984,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_8979,c_4064,c_5258])).

cnf(c_9215,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8984,c_965])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_962,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_970,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_962,c_410])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9215,c_970])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : iproveropt_run.sh %d %s
% 0.09/0.29  % Computer   : n016.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 18:49:34 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.30  % Running in FOF mode
% 3.77/0.89  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/0.89  
% 3.77/0.89  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/0.89  
% 3.77/0.89  ------  iProver source info
% 3.77/0.89  
% 3.77/0.89  git: date: 2020-06-30 10:37:57 +0100
% 3.77/0.89  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/0.89  git: non_committed_changes: false
% 3.77/0.89  git: last_make_outside_of_git: false
% 3.77/0.89  
% 3.77/0.89  ------ 
% 3.77/0.89  
% 3.77/0.89  ------ Input Options
% 3.77/0.89  
% 3.77/0.89  --out_options                           all
% 3.77/0.89  --tptp_safe_out                         true
% 3.77/0.89  --problem_path                          ""
% 3.77/0.89  --include_path                          ""
% 3.77/0.89  --clausifier                            res/vclausify_rel
% 3.77/0.89  --clausifier_options                    ""
% 3.77/0.89  --stdin                                 false
% 3.77/0.89  --stats_out                             all
% 3.77/0.89  
% 3.77/0.89  ------ General Options
% 3.77/0.89  
% 3.77/0.89  --fof                                   false
% 3.77/0.89  --time_out_real                         305.
% 3.77/0.89  --time_out_virtual                      -1.
% 3.77/0.89  --symbol_type_check                     false
% 3.77/0.89  --clausify_out                          false
% 3.77/0.89  --sig_cnt_out                           false
% 3.77/0.89  --trig_cnt_out                          false
% 3.77/0.89  --trig_cnt_out_tolerance                1.
% 3.77/0.89  --trig_cnt_out_sk_spl                   false
% 3.77/0.89  --abstr_cl_out                          false
% 3.77/0.89  
% 3.77/0.89  ------ Global Options
% 3.77/0.89  
% 3.77/0.89  --schedule                              default
% 3.77/0.89  --add_important_lit                     false
% 3.77/0.89  --prop_solver_per_cl                    1000
% 3.77/0.89  --min_unsat_core                        false
% 3.77/0.89  --soft_assumptions                      false
% 3.77/0.89  --soft_lemma_size                       3
% 3.77/0.89  --prop_impl_unit_size                   0
% 3.77/0.89  --prop_impl_unit                        []
% 3.77/0.89  --share_sel_clauses                     true
% 3.77/0.89  --reset_solvers                         false
% 3.77/0.89  --bc_imp_inh                            [conj_cone]
% 3.77/0.89  --conj_cone_tolerance                   3.
% 3.77/0.89  --extra_neg_conj                        none
% 3.77/0.89  --large_theory_mode                     true
% 3.77/0.89  --prolific_symb_bound                   200
% 3.77/0.89  --lt_threshold                          2000
% 3.77/0.89  --clause_weak_htbl                      true
% 3.77/0.89  --gc_record_bc_elim                     false
% 3.77/0.89  
% 3.77/0.89  ------ Preprocessing Options
% 3.77/0.89  
% 3.77/0.89  --preprocessing_flag                    true
% 3.77/0.89  --time_out_prep_mult                    0.1
% 3.77/0.89  --splitting_mode                        input
% 3.77/0.89  --splitting_grd                         true
% 3.77/0.89  --splitting_cvd                         false
% 3.77/0.89  --splitting_cvd_svl                     false
% 3.77/0.89  --splitting_nvd                         32
% 3.77/0.89  --sub_typing                            true
% 3.77/0.89  --prep_gs_sim                           true
% 3.77/0.89  --prep_unflatten                        true
% 3.77/0.89  --prep_res_sim                          true
% 3.77/0.89  --prep_upred                            true
% 3.77/0.89  --prep_sem_filter                       exhaustive
% 3.77/0.89  --prep_sem_filter_out                   false
% 3.77/0.89  --pred_elim                             true
% 3.77/0.89  --res_sim_input                         true
% 3.77/0.89  --eq_ax_congr_red                       true
% 3.77/0.89  --pure_diseq_elim                       true
% 3.77/0.89  --brand_transform                       false
% 3.77/0.89  --non_eq_to_eq                          false
% 3.77/0.89  --prep_def_merge                        true
% 3.77/0.89  --prep_def_merge_prop_impl              false
% 3.77/0.89  --prep_def_merge_mbd                    true
% 3.77/0.89  --prep_def_merge_tr_red                 false
% 3.77/0.89  --prep_def_merge_tr_cl                  false
% 3.77/0.89  --smt_preprocessing                     true
% 3.77/0.89  --smt_ac_axioms                         fast
% 3.77/0.89  --preprocessed_out                      false
% 3.77/0.89  --preprocessed_stats                    false
% 3.77/0.89  
% 3.77/0.89  ------ Abstraction refinement Options
% 3.77/0.89  
% 3.77/0.89  --abstr_ref                             []
% 3.77/0.89  --abstr_ref_prep                        false
% 3.77/0.89  --abstr_ref_until_sat                   false
% 3.77/0.89  --abstr_ref_sig_restrict                funpre
% 3.77/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.89  --abstr_ref_under                       []
% 3.77/0.89  
% 3.77/0.89  ------ SAT Options
% 3.77/0.89  
% 3.77/0.89  --sat_mode                              false
% 3.77/0.89  --sat_fm_restart_options                ""
% 3.77/0.89  --sat_gr_def                            false
% 3.77/0.89  --sat_epr_types                         true
% 3.77/0.89  --sat_non_cyclic_types                  false
% 3.77/0.89  --sat_finite_models                     false
% 3.77/0.89  --sat_fm_lemmas                         false
% 3.77/0.89  --sat_fm_prep                           false
% 3.77/0.89  --sat_fm_uc_incr                        true
% 3.77/0.89  --sat_out_model                         small
% 3.77/0.89  --sat_out_clauses                       false
% 3.77/0.89  
% 3.77/0.89  ------ QBF Options
% 3.77/0.89  
% 3.77/0.89  --qbf_mode                              false
% 3.77/0.89  --qbf_elim_univ                         false
% 3.77/0.89  --qbf_dom_inst                          none
% 3.77/0.89  --qbf_dom_pre_inst                      false
% 3.77/0.89  --qbf_sk_in                             false
% 3.77/0.89  --qbf_pred_elim                         true
% 3.77/0.89  --qbf_split                             512
% 3.77/0.89  
% 3.77/0.89  ------ BMC1 Options
% 3.77/0.89  
% 3.77/0.89  --bmc1_incremental                      false
% 3.77/0.89  --bmc1_axioms                           reachable_all
% 3.77/0.89  --bmc1_min_bound                        0
% 3.77/0.89  --bmc1_max_bound                        -1
% 3.77/0.89  --bmc1_max_bound_default                -1
% 3.77/0.89  --bmc1_symbol_reachability              true
% 3.77/0.89  --bmc1_property_lemmas                  false
% 3.77/0.89  --bmc1_k_induction                      false
% 3.77/0.89  --bmc1_non_equiv_states                 false
% 3.77/0.89  --bmc1_deadlock                         false
% 3.77/0.89  --bmc1_ucm                              false
% 3.77/0.89  --bmc1_add_unsat_core                   none
% 3.77/0.89  --bmc1_unsat_core_children              false
% 3.77/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.89  --bmc1_out_stat                         full
% 3.77/0.89  --bmc1_ground_init                      false
% 3.77/0.89  --bmc1_pre_inst_next_state              false
% 3.77/0.89  --bmc1_pre_inst_state                   false
% 3.77/0.89  --bmc1_pre_inst_reach_state             false
% 3.77/0.89  --bmc1_out_unsat_core                   false
% 3.77/0.89  --bmc1_aig_witness_out                  false
% 3.77/0.89  --bmc1_verbose                          false
% 3.77/0.89  --bmc1_dump_clauses_tptp                false
% 3.77/0.89  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.89  --bmc1_dump_file                        -
% 3.77/0.89  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.89  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.89  --bmc1_ucm_extend_mode                  1
% 3.77/0.89  --bmc1_ucm_init_mode                    2
% 3.77/0.89  --bmc1_ucm_cone_mode                    none
% 3.77/0.89  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.89  --bmc1_ucm_relax_model                  4
% 3.77/0.89  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.89  --bmc1_ucm_layered_model                none
% 3.77/0.89  --bmc1_ucm_max_lemma_size               10
% 3.77/0.89  
% 3.77/0.89  ------ AIG Options
% 3.77/0.89  
% 3.77/0.89  --aig_mode                              false
% 3.77/0.89  
% 3.77/0.89  ------ Instantiation Options
% 3.77/0.89  
% 3.77/0.89  --instantiation_flag                    true
% 3.77/0.89  --inst_sos_flag                         true
% 3.77/0.89  --inst_sos_phase                        true
% 3.77/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.89  --inst_lit_sel_side                     num_symb
% 3.77/0.89  --inst_solver_per_active                1400
% 3.77/0.89  --inst_solver_calls_frac                1.
% 3.77/0.89  --inst_passive_queue_type               priority_queues
% 3.77/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.89  --inst_passive_queues_freq              [25;2]
% 3.77/0.89  --inst_dismatching                      true
% 3.77/0.89  --inst_eager_unprocessed_to_passive     true
% 3.77/0.89  --inst_prop_sim_given                   true
% 3.77/0.89  --inst_prop_sim_new                     false
% 3.77/0.89  --inst_subs_new                         false
% 3.77/0.89  --inst_eq_res_simp                      false
% 3.77/0.89  --inst_subs_given                       false
% 3.77/0.89  --inst_orphan_elimination               true
% 3.77/0.89  --inst_learning_loop_flag               true
% 3.77/0.89  --inst_learning_start                   3000
% 3.77/0.89  --inst_learning_factor                  2
% 3.77/0.89  --inst_start_prop_sim_after_learn       3
% 3.77/0.89  --inst_sel_renew                        solver
% 3.77/0.89  --inst_lit_activity_flag                true
% 3.77/0.89  --inst_restr_to_given                   false
% 3.77/0.89  --inst_activity_threshold               500
% 3.77/0.89  --inst_out_proof                        true
% 3.77/0.89  
% 3.77/0.89  ------ Resolution Options
% 3.77/0.89  
% 3.77/0.89  --resolution_flag                       true
% 3.77/0.89  --res_lit_sel                           adaptive
% 3.77/0.89  --res_lit_sel_side                      none
% 3.77/0.89  --res_ordering                          kbo
% 3.77/0.89  --res_to_prop_solver                    active
% 3.77/0.89  --res_prop_simpl_new                    false
% 3.77/0.89  --res_prop_simpl_given                  true
% 3.77/0.89  --res_passive_queue_type                priority_queues
% 3.77/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.89  --res_passive_queues_freq               [15;5]
% 3.77/0.89  --res_forward_subs                      full
% 3.77/0.89  --res_backward_subs                     full
% 3.77/0.89  --res_forward_subs_resolution           true
% 3.77/0.89  --res_backward_subs_resolution          true
% 3.77/0.89  --res_orphan_elimination                true
% 3.77/0.89  --res_time_limit                        2.
% 3.77/0.89  --res_out_proof                         true
% 3.77/0.89  
% 3.77/0.89  ------ Superposition Options
% 3.77/0.89  
% 3.77/0.89  --superposition_flag                    true
% 3.77/0.89  --sup_passive_queue_type                priority_queues
% 3.77/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.89  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.89  --demod_completeness_check              fast
% 3.77/0.89  --demod_use_ground                      true
% 3.77/0.89  --sup_to_prop_solver                    passive
% 3.77/0.89  --sup_prop_simpl_new                    true
% 3.77/0.89  --sup_prop_simpl_given                  true
% 3.77/0.89  --sup_fun_splitting                     true
% 3.77/0.89  --sup_smt_interval                      50000
% 3.77/0.89  
% 3.77/0.89  ------ Superposition Simplification Setup
% 3.77/0.89  
% 3.77/0.89  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.77/0.89  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.77/0.89  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.77/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.77/0.89  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.77/0.89  --sup_immed_triv                        [TrivRules]
% 3.77/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.89  --sup_immed_bw_main                     []
% 3.77/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.77/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.89  --sup_input_bw                          []
% 3.77/0.89  
% 3.77/0.89  ------ Combination Options
% 3.77/0.89  
% 3.77/0.89  --comb_res_mult                         3
% 3.77/0.89  --comb_sup_mult                         2
% 3.77/0.89  --comb_inst_mult                        10
% 3.77/0.89  
% 3.77/0.89  ------ Debug Options
% 3.77/0.89  
% 3.77/0.89  --dbg_backtrace                         false
% 3.77/0.89  --dbg_dump_prop_clauses                 false
% 3.77/0.89  --dbg_dump_prop_clauses_file            -
% 3.77/0.89  --dbg_out_stat                          false
% 3.77/0.89  ------ Parsing...
% 3.77/0.89  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/0.89  
% 3.77/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.77/0.89  
% 3.77/0.89  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/0.89  
% 3.77/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/0.89  ------ Proving...
% 3.77/0.89  ------ Problem Properties 
% 3.77/0.89  
% 3.77/0.89  
% 3.77/0.89  clauses                                 18
% 3.77/0.89  conjectures                             2
% 3.77/0.89  EPR                                     2
% 3.77/0.89  Horn                                    18
% 3.77/0.89  unary                                   6
% 3.77/0.89  binary                                  8
% 3.77/0.89  lits                                    34
% 3.77/0.89  lits eq                                 9
% 3.77/0.89  fd_pure                                 0
% 3.77/0.89  fd_pseudo                               0
% 3.77/0.89  fd_cond                                 0
% 3.77/0.89  fd_pseudo_cond                          1
% 3.77/0.89  AC symbols                              0
% 3.77/0.89  
% 3.77/0.89  ------ Schedule dynamic 5 is on 
% 3.77/0.89  
% 3.77/0.89  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.77/0.89  
% 3.77/0.89  
% 3.77/0.89  ------ 
% 3.77/0.89  Current options:
% 3.77/0.89  ------ 
% 3.77/0.89  
% 3.77/0.89  ------ Input Options
% 3.77/0.89  
% 3.77/0.89  --out_options                           all
% 3.77/0.89  --tptp_safe_out                         true
% 3.77/0.89  --problem_path                          ""
% 3.77/0.89  --include_path                          ""
% 3.77/0.89  --clausifier                            res/vclausify_rel
% 3.77/0.89  --clausifier_options                    ""
% 3.77/0.89  --stdin                                 false
% 3.77/0.89  --stats_out                             all
% 3.77/0.89  
% 3.77/0.89  ------ General Options
% 3.77/0.89  
% 3.77/0.89  --fof                                   false
% 3.77/0.89  --time_out_real                         305.
% 3.77/0.89  --time_out_virtual                      -1.
% 3.77/0.89  --symbol_type_check                     false
% 3.77/0.89  --clausify_out                          false
% 3.77/0.89  --sig_cnt_out                           false
% 3.77/0.89  --trig_cnt_out                          false
% 3.77/0.89  --trig_cnt_out_tolerance                1.
% 3.77/0.89  --trig_cnt_out_sk_spl                   false
% 3.77/0.89  --abstr_cl_out                          false
% 3.77/0.89  
% 3.77/0.89  ------ Global Options
% 3.77/0.89  
% 3.77/0.89  --schedule                              default
% 3.77/0.89  --add_important_lit                     false
% 3.77/0.89  --prop_solver_per_cl                    1000
% 3.77/0.89  --min_unsat_core                        false
% 3.77/0.89  --soft_assumptions                      false
% 3.77/0.89  --soft_lemma_size                       3
% 3.77/0.89  --prop_impl_unit_size                   0
% 3.77/0.89  --prop_impl_unit                        []
% 3.77/0.89  --share_sel_clauses                     true
% 3.77/0.89  --reset_solvers                         false
% 3.77/0.89  --bc_imp_inh                            [conj_cone]
% 3.77/0.89  --conj_cone_tolerance                   3.
% 3.77/0.89  --extra_neg_conj                        none
% 3.77/0.89  --large_theory_mode                     true
% 3.77/0.89  --prolific_symb_bound                   200
% 3.77/0.89  --lt_threshold                          2000
% 3.77/0.89  --clause_weak_htbl                      true
% 3.77/0.89  --gc_record_bc_elim                     false
% 3.77/0.89  
% 3.77/0.89  ------ Preprocessing Options
% 3.77/0.89  
% 3.77/0.89  --preprocessing_flag                    true
% 3.77/0.89  --time_out_prep_mult                    0.1
% 3.77/0.89  --splitting_mode                        input
% 3.77/0.89  --splitting_grd                         true
% 3.77/0.89  --splitting_cvd                         false
% 3.77/0.89  --splitting_cvd_svl                     false
% 3.77/0.89  --splitting_nvd                         32
% 3.77/0.89  --sub_typing                            true
% 3.77/0.89  --prep_gs_sim                           true
% 3.77/0.89  --prep_unflatten                        true
% 3.77/0.89  --prep_res_sim                          true
% 3.77/0.89  --prep_upred                            true
% 3.77/0.89  --prep_sem_filter                       exhaustive
% 3.77/0.89  --prep_sem_filter_out                   false
% 3.77/0.89  --pred_elim                             true
% 3.77/0.89  --res_sim_input                         true
% 3.77/0.89  --eq_ax_congr_red                       true
% 3.77/0.89  --pure_diseq_elim                       true
% 3.77/0.89  --brand_transform                       false
% 3.77/0.89  --non_eq_to_eq                          false
% 3.77/0.89  --prep_def_merge                        true
% 3.77/0.89  --prep_def_merge_prop_impl              false
% 3.77/0.89  --prep_def_merge_mbd                    true
% 3.77/0.89  --prep_def_merge_tr_red                 false
% 3.77/0.89  --prep_def_merge_tr_cl                  false
% 3.77/0.89  --smt_preprocessing                     true
% 3.77/0.89  --smt_ac_axioms                         fast
% 3.77/0.89  --preprocessed_out                      false
% 3.77/0.89  --preprocessed_stats                    false
% 3.77/0.89  
% 3.77/0.89  ------ Abstraction refinement Options
% 3.77/0.89  
% 3.77/0.89  --abstr_ref                             []
% 3.77/0.89  --abstr_ref_prep                        false
% 3.77/0.89  --abstr_ref_until_sat                   false
% 3.77/0.89  --abstr_ref_sig_restrict                funpre
% 3.77/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.89  --abstr_ref_under                       []
% 3.77/0.89  
% 3.77/0.89  ------ SAT Options
% 3.77/0.89  
% 3.77/0.89  --sat_mode                              false
% 3.77/0.89  --sat_fm_restart_options                ""
% 3.77/0.89  --sat_gr_def                            false
% 3.77/0.89  --sat_epr_types                         true
% 3.77/0.89  --sat_non_cyclic_types                  false
% 3.77/0.89  --sat_finite_models                     false
% 3.77/0.89  --sat_fm_lemmas                         false
% 3.77/0.89  --sat_fm_prep                           false
% 3.77/0.89  --sat_fm_uc_incr                        true
% 3.77/0.89  --sat_out_model                         small
% 3.77/0.89  --sat_out_clauses                       false
% 3.77/0.89  
% 3.77/0.89  ------ QBF Options
% 3.77/0.89  
% 3.77/0.89  --qbf_mode                              false
% 3.77/0.89  --qbf_elim_univ                         false
% 3.77/0.89  --qbf_dom_inst                          none
% 3.77/0.89  --qbf_dom_pre_inst                      false
% 3.77/0.89  --qbf_sk_in                             false
% 3.77/0.89  --qbf_pred_elim                         true
% 3.77/0.89  --qbf_split                             512
% 3.77/0.89  
% 3.77/0.89  ------ BMC1 Options
% 3.77/0.89  
% 3.77/0.89  --bmc1_incremental                      false
% 3.77/0.89  --bmc1_axioms                           reachable_all
% 3.77/0.89  --bmc1_min_bound                        0
% 3.77/0.89  --bmc1_max_bound                        -1
% 3.77/0.89  --bmc1_max_bound_default                -1
% 3.77/0.89  --bmc1_symbol_reachability              true
% 3.77/0.89  --bmc1_property_lemmas                  false
% 3.77/0.89  --bmc1_k_induction                      false
% 3.77/0.89  --bmc1_non_equiv_states                 false
% 3.77/0.89  --bmc1_deadlock                         false
% 3.77/0.89  --bmc1_ucm                              false
% 3.77/0.89  --bmc1_add_unsat_core                   none
% 3.77/0.89  --bmc1_unsat_core_children              false
% 3.77/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.89  --bmc1_out_stat                         full
% 3.77/0.89  --bmc1_ground_init                      false
% 3.77/0.89  --bmc1_pre_inst_next_state              false
% 3.77/0.89  --bmc1_pre_inst_state                   false
% 3.77/0.89  --bmc1_pre_inst_reach_state             false
% 3.77/0.89  --bmc1_out_unsat_core                   false
% 3.77/0.89  --bmc1_aig_witness_out                  false
% 3.77/0.89  --bmc1_verbose                          false
% 3.77/0.89  --bmc1_dump_clauses_tptp                false
% 3.77/0.89  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.89  --bmc1_dump_file                        -
% 3.77/0.89  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.89  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.89  --bmc1_ucm_extend_mode                  1
% 3.77/0.89  --bmc1_ucm_init_mode                    2
% 3.77/0.89  --bmc1_ucm_cone_mode                    none
% 3.77/0.89  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.89  --bmc1_ucm_relax_model                  4
% 3.77/0.89  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.89  --bmc1_ucm_layered_model                none
% 3.77/0.89  --bmc1_ucm_max_lemma_size               10
% 3.77/0.89  
% 3.77/0.89  ------ AIG Options
% 3.77/0.89  
% 3.77/0.89  --aig_mode                              false
% 3.77/0.89  
% 3.77/0.89  ------ Instantiation Options
% 3.77/0.89  
% 3.77/0.89  --instantiation_flag                    true
% 3.77/0.89  --inst_sos_flag                         true
% 3.77/0.89  --inst_sos_phase                        true
% 3.77/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.89  --inst_lit_sel_side                     none
% 3.77/0.89  --inst_solver_per_active                1400
% 3.77/0.89  --inst_solver_calls_frac                1.
% 3.77/0.89  --inst_passive_queue_type               priority_queues
% 3.77/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.89  --inst_passive_queues_freq              [25;2]
% 3.77/0.89  --inst_dismatching                      true
% 3.77/0.89  --inst_eager_unprocessed_to_passive     true
% 3.77/0.89  --inst_prop_sim_given                   true
% 3.77/0.89  --inst_prop_sim_new                     false
% 3.77/0.89  --inst_subs_new                         false
% 3.77/0.89  --inst_eq_res_simp                      false
% 3.77/0.89  --inst_subs_given                       false
% 3.77/0.89  --inst_orphan_elimination               true
% 3.77/0.89  --inst_learning_loop_flag               true
% 3.77/0.89  --inst_learning_start                   3000
% 3.77/0.89  --inst_learning_factor                  2
% 3.77/0.89  --inst_start_prop_sim_after_learn       3
% 3.77/0.89  --inst_sel_renew                        solver
% 3.77/0.89  --inst_lit_activity_flag                true
% 3.77/0.89  --inst_restr_to_given                   false
% 3.77/0.89  --inst_activity_threshold               500
% 3.77/0.89  --inst_out_proof                        true
% 3.77/0.89  
% 3.77/0.89  ------ Resolution Options
% 3.77/0.89  
% 3.77/0.89  --resolution_flag                       false
% 3.77/0.89  --res_lit_sel                           adaptive
% 3.77/0.89  --res_lit_sel_side                      none
% 3.77/0.89  --res_ordering                          kbo
% 3.77/0.89  --res_to_prop_solver                    active
% 3.77/0.89  --res_prop_simpl_new                    false
% 3.77/0.89  --res_prop_simpl_given                  true
% 3.77/0.89  --res_passive_queue_type                priority_queues
% 3.77/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.89  --res_passive_queues_freq               [15;5]
% 3.77/0.89  --res_forward_subs                      full
% 3.77/0.89  --res_backward_subs                     full
% 3.77/0.89  --res_forward_subs_resolution           true
% 3.77/0.89  --res_backward_subs_resolution          true
% 3.77/0.89  --res_orphan_elimination                true
% 3.77/0.89  --res_time_limit                        2.
% 3.77/0.89  --res_out_proof                         true
% 3.77/0.89  
% 3.77/0.89  ------ Superposition Options
% 3.77/0.89  
% 3.77/0.89  --superposition_flag                    true
% 3.77/0.89  --sup_passive_queue_type                priority_queues
% 3.77/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.89  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.89  --demod_completeness_check              fast
% 3.77/0.89  --demod_use_ground                      true
% 3.77/0.89  --sup_to_prop_solver                    passive
% 3.77/0.89  --sup_prop_simpl_new                    true
% 3.77/0.89  --sup_prop_simpl_given                  true
% 3.77/0.89  --sup_fun_splitting                     true
% 3.77/0.89  --sup_smt_interval                      50000
% 3.77/0.89  
% 3.77/0.89  ------ Superposition Simplification Setup
% 3.77/0.89  
% 3.77/0.89  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.77/0.89  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.77/0.89  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.77/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.77/0.89  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.77/0.89  --sup_immed_triv                        [TrivRules]
% 3.77/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.89  --sup_immed_bw_main                     []
% 3.77/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.77/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.89  --sup_input_bw                          []
% 3.77/0.89  
% 3.77/0.89  ------ Combination Options
% 3.77/0.89  
% 3.77/0.89  --comb_res_mult                         3
% 3.77/0.89  --comb_sup_mult                         2
% 3.77/0.89  --comb_inst_mult                        10
% 3.77/0.89  
% 3.77/0.89  ------ Debug Options
% 3.77/0.89  
% 3.77/0.89  --dbg_backtrace                         false
% 3.77/0.89  --dbg_dump_prop_clauses                 false
% 3.77/0.89  --dbg_dump_prop_clauses_file            -
% 3.77/0.89  --dbg_out_stat                          false
% 3.77/0.89  
% 3.77/0.89  
% 3.77/0.89  
% 3.77/0.89  
% 3.77/0.89  ------ Proving...
% 3.77/0.89  
% 3.77/0.89  
% 3.77/0.89  % SZS status Theorem for theBenchmark.p
% 3.77/0.89  
% 3.77/0.89  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/0.89  
% 3.77/0.89  fof(f15,conjecture,(
% 3.77/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f16,negated_conjecture,(
% 3.77/0.89    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.77/0.89    inference(negated_conjecture,[],[f15])).
% 3.77/0.89  
% 3.77/0.89  fof(f32,plain,(
% 3.77/0.89    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.77/0.89    inference(ennf_transformation,[],[f16])).
% 3.77/0.89  
% 3.77/0.89  fof(f33,plain,(
% 3.77/0.89    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.77/0.89    inference(flattening,[],[f32])).
% 3.77/0.89  
% 3.77/0.89  fof(f39,plain,(
% 3.77/0.89    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.77/0.89    introduced(choice_axiom,[])).
% 3.77/0.89  
% 3.77/0.89  fof(f38,plain,(
% 3.77/0.89    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.77/0.89    introduced(choice_axiom,[])).
% 3.77/0.89  
% 3.77/0.89  fof(f40,plain,(
% 3.77/0.89    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.77/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f39,f38])).
% 3.77/0.89  
% 3.77/0.89  fof(f60,plain,(
% 3.77/0.89    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.77/0.89    inference(cnf_transformation,[],[f40])).
% 3.77/0.89  
% 3.77/0.89  fof(f8,axiom,(
% 3.77/0.89    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f36,plain,(
% 3.77/0.89    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.77/0.89    inference(nnf_transformation,[],[f8])).
% 3.77/0.89  
% 3.77/0.89  fof(f50,plain,(
% 3.77/0.89    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.77/0.89    inference(cnf_transformation,[],[f36])).
% 3.77/0.89  
% 3.77/0.89  fof(f61,plain,(
% 3.77/0.89    v5_tops_1(sK1,sK0)),
% 3.77/0.89    inference(cnf_transformation,[],[f40])).
% 3.77/0.89  
% 3.77/0.89  fof(f10,axiom,(
% 3.77/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f24,plain,(
% 3.77/0.89    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.77/0.89    inference(ennf_transformation,[],[f10])).
% 3.77/0.89  
% 3.77/0.89  fof(f37,plain,(
% 3.77/0.89    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.77/0.89    inference(nnf_transformation,[],[f24])).
% 3.77/0.89  
% 3.77/0.89  fof(f53,plain,(
% 3.77/0.89    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/0.89    inference(cnf_transformation,[],[f37])).
% 3.77/0.89  
% 3.77/0.89  fof(f59,plain,(
% 3.77/0.89    l1_pre_topc(sK0)),
% 3.77/0.89    inference(cnf_transformation,[],[f40])).
% 3.77/0.89  
% 3.77/0.89  fof(f51,plain,(
% 3.77/0.89    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.77/0.89    inference(cnf_transformation,[],[f36])).
% 3.77/0.89  
% 3.77/0.89  fof(f9,axiom,(
% 3.77/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f23,plain,(
% 3.77/0.89    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.77/0.89    inference(ennf_transformation,[],[f9])).
% 3.77/0.89  
% 3.77/0.89  fof(f52,plain,(
% 3.77/0.89    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/0.89    inference(cnf_transformation,[],[f23])).
% 3.77/0.89  
% 3.77/0.89  fof(f11,axiom,(
% 3.77/0.89    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f25,plain,(
% 3.77/0.89    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.77/0.89    inference(ennf_transformation,[],[f11])).
% 3.77/0.89  
% 3.77/0.89  fof(f26,plain,(
% 3.77/0.89    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.77/0.89    inference(flattening,[],[f25])).
% 3.77/0.89  
% 3.77/0.89  fof(f55,plain,(
% 3.77/0.89    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/0.89    inference(cnf_transformation,[],[f26])).
% 3.77/0.89  
% 3.77/0.89  fof(f3,axiom,(
% 3.77/0.89    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f18,plain,(
% 3.77/0.89    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.77/0.89    inference(ennf_transformation,[],[f3])).
% 3.77/0.89  
% 3.77/0.89  fof(f45,plain,(
% 3.77/0.89    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.77/0.89    inference(cnf_transformation,[],[f18])).
% 3.77/0.89  
% 3.77/0.89  fof(f5,axiom,(
% 3.77/0.89    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f47,plain,(
% 3.77/0.89    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.77/0.89    inference(cnf_transformation,[],[f5])).
% 3.77/0.89  
% 3.77/0.89  fof(f64,plain,(
% 3.77/0.89    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.77/0.89    inference(definition_unfolding,[],[f45,f47])).
% 3.77/0.89  
% 3.77/0.89  fof(f2,axiom,(
% 3.77/0.89    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f17,plain,(
% 3.77/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.77/0.89    inference(ennf_transformation,[],[f2])).
% 3.77/0.89  
% 3.77/0.89  fof(f44,plain,(
% 3.77/0.89    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.77/0.89    inference(cnf_transformation,[],[f17])).
% 3.77/0.89  
% 3.77/0.89  fof(f63,plain,(
% 3.77/0.89    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)) )),
% 3.77/0.89    inference(definition_unfolding,[],[f44,f47])).
% 3.77/0.89  
% 3.77/0.89  fof(f4,axiom,(
% 3.77/0.89    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f46,plain,(
% 3.77/0.89    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.77/0.89    inference(cnf_transformation,[],[f4])).
% 3.77/0.89  
% 3.77/0.89  fof(f65,plain,(
% 3.77/0.89    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 3.77/0.89    inference(definition_unfolding,[],[f46,f47])).
% 3.77/0.89  
% 3.77/0.89  fof(f13,axiom,(
% 3.77/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)))))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f29,plain,(
% 3.77/0.89    ! [X0] : (! [X1] : ((k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) | ~v5_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.77/0.89    inference(ennf_transformation,[],[f13])).
% 3.77/0.89  
% 3.77/0.89  fof(f30,plain,(
% 3.77/0.89    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.77/0.89    inference(flattening,[],[f29])).
% 3.77/0.89  
% 3.77/0.89  fof(f57,plain,(
% 3.77/0.89    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/0.89    inference(cnf_transformation,[],[f30])).
% 3.77/0.89  
% 3.77/0.89  fof(f12,axiom,(
% 3.77/0.89    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f27,plain,(
% 3.77/0.89    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.77/0.89    inference(ennf_transformation,[],[f12])).
% 3.77/0.89  
% 3.77/0.89  fof(f28,plain,(
% 3.77/0.89    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.77/0.89    inference(flattening,[],[f27])).
% 3.77/0.89  
% 3.77/0.89  fof(f56,plain,(
% 3.77/0.89    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/0.89    inference(cnf_transformation,[],[f28])).
% 3.77/0.89  
% 3.77/0.89  fof(f6,axiom,(
% 3.77/0.89    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f19,plain,(
% 3.77/0.89    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.77/0.89    inference(ennf_transformation,[],[f6])).
% 3.77/0.89  
% 3.77/0.89  fof(f20,plain,(
% 3.77/0.89    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.77/0.89    inference(flattening,[],[f19])).
% 3.77/0.89  
% 3.77/0.89  fof(f48,plain,(
% 3.77/0.89    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.77/0.89    inference(cnf_transformation,[],[f20])).
% 3.77/0.89  
% 3.77/0.89  fof(f14,axiom,(
% 3.77/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f31,plain,(
% 3.77/0.89    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.77/0.89    inference(ennf_transformation,[],[f14])).
% 3.77/0.89  
% 3.77/0.89  fof(f58,plain,(
% 3.77/0.89    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/0.89    inference(cnf_transformation,[],[f31])).
% 3.77/0.89  
% 3.77/0.89  fof(f7,axiom,(
% 3.77/0.89    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.77/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.89  
% 3.77/0.89  fof(f21,plain,(
% 3.77/0.89    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.77/0.89    inference(ennf_transformation,[],[f7])).
% 3.77/0.89  
% 3.77/0.89  fof(f22,plain,(
% 3.77/0.89    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.77/0.89    inference(flattening,[],[f21])).
% 3.77/0.89  
% 3.77/0.89  fof(f49,plain,(
% 3.77/0.89    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.77/0.89    inference(cnf_transformation,[],[f22])).
% 3.77/0.89  
% 3.77/0.89  fof(f66,plain,(
% 3.77/0.89    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.77/0.89    inference(definition_unfolding,[],[f49,f47])).
% 3.77/0.89  
% 3.77/0.89  fof(f62,plain,(
% 3.77/0.89    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 3.77/0.89    inference(cnf_transformation,[],[f40])).
% 3.77/0.89  
% 3.77/0.89  cnf(c_19,negated_conjecture,
% 3.77/0.89      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.77/0.89      inference(cnf_transformation,[],[f60]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_961,plain,
% 3.77/0.89      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_9,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.77/0.89      inference(cnf_transformation,[],[f50]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_963,plain,
% 3.77/0.89      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.77/0.89      | r1_tarski(X0,X1) = iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1578,plain,
% 3.77/0.89      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_961,c_963]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_18,negated_conjecture,
% 3.77/0.89      ( v5_tops_1(sK1,sK0) ),
% 3.77/0.89      inference(cnf_transformation,[],[f61]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_12,plain,
% 3.77/0.89      ( ~ v5_tops_1(X0,X1)
% 3.77/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | ~ l1_pre_topc(X1)
% 3.77/0.89      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 3.77/0.89      inference(cnf_transformation,[],[f53]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_20,negated_conjecture,
% 3.77/0.89      ( l1_pre_topc(sK0) ),
% 3.77/0.89      inference(cnf_transformation,[],[f59]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_326,plain,
% 3.77/0.89      ( ~ v5_tops_1(X0,X1)
% 3.77/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 3.77/0.89      | sK0 != X1 ),
% 3.77/0.89      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_327,plain,
% 3.77/0.89      ( ~ v5_tops_1(X0,sK0)
% 3.77/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
% 3.77/0.89      inference(unflattening,[status(thm)],[c_326]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_407,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
% 3.77/0.89      | sK1 != X0
% 3.77/0.89      | sK0 != sK0 ),
% 3.77/0.89      inference(resolution_lifted,[status(thm)],[c_18,c_327]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_408,plain,
% 3.77/0.89      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.77/0.89      inference(unflattening,[status(thm)],[c_407]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_410,plain,
% 3.77/0.89      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.77/0.89      inference(global_propositional_subsumption,
% 3.77/0.89                [status(thm)],
% 3.77/0.89                [c_408,c_19]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_8,plain,
% 3.77/0.89      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.77/0.89      inference(cnf_transformation,[],[f51]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_964,plain,
% 3.77/0.89      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.77/0.89      | r1_tarski(X0,X1) != iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_10,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.77/0.89      | ~ l1_pre_topc(X1) ),
% 3.77/0.89      inference(cnf_transformation,[],[f52]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_356,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.77/0.89      | sK0 != X1 ),
% 3.77/0.89      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_357,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 3.77/0.89      inference(unflattening,[status(thm)],[c_356]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_957,plain,
% 3.77/0.89      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.89      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1665,plain,
% 3.77/0.89      ( r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
% 3.77/0.89      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_964,c_957]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_2128,plain,
% 3.77/0.89      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top
% 3.77/0.89      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_410,c_1665]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_22,plain,
% 3.77/0.89      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_13,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | ~ l1_pre_topc(X1) ),
% 3.77/0.89      inference(cnf_transformation,[],[f55]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_314,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | sK0 != X1 ),
% 3.77/0.89      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_315,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.77/0.89      inference(unflattening,[status(thm)],[c_314]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1020,plain,
% 3.77/0.89      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.77/0.89      inference(instantiation,[status(thm)],[c_315]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1021,plain,
% 3.77/0.89      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.77/0.89      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1149,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 3.77/0.89      inference(instantiation,[status(thm)],[c_9]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1858,plain,
% 3.77/0.89      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
% 3.77/0.89      inference(instantiation,[status(thm)],[c_1149]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1859,plain,
% 3.77/0.89      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.89      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_1858]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_2227,plain,
% 3.77/0.89      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.77/0.89      inference(global_propositional_subsumption,
% 3.77/0.89                [status(thm)],
% 3.77/0.89                [c_2128,c_22,c_1021,c_1859]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_4,plain,
% 3.77/0.89      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 3.77/0.89      inference(cnf_transformation,[],[f64]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_966,plain,
% 3.77/0.89      ( k3_tarski(k2_tarski(X0,X1)) = X1
% 3.77/0.89      | r1_tarski(X0,X1) != iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_2364,plain,
% 3.77/0.89      ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = sK1 ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_2227,c_966]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_3,plain,
% 3.77/0.89      ( r1_tarski(X0,X1) | ~ r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 3.77/0.89      inference(cnf_transformation,[],[f63]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_967,plain,
% 3.77/0.89      ( r1_tarski(X0,X1) = iProver_top
% 3.77/0.89      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) != iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_2587,plain,
% 3.77/0.89      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 3.77/0.89      | r1_tarski(sK1,X0) != iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_2364,c_967]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_3821,plain,
% 3.77/0.89      ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),X0)) = X0
% 3.77/0.89      | r1_tarski(sK1,X0) != iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_2587,c_966]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_4319,plain,
% 3.77/0.89      ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_1578,c_3821]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_5,plain,
% 3.77/0.89      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 3.77/0.89      inference(cnf_transformation,[],[f65]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_965,plain,
% 3.77/0.89      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_4432,plain,
% 3.77/0.89      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_4319,c_965]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_15,plain,
% 3.77/0.89      ( ~ v5_tops_1(X0,X1)
% 3.77/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | ~ l1_pre_topc(X1)
% 3.77/0.89      | k2_tops_1(X1,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.77/0.89      inference(cnf_transformation,[],[f57]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_287,plain,
% 3.77/0.89      ( ~ v5_tops_1(X0,X1)
% 3.77/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | k2_tops_1(X1,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 3.77/0.89      | sK0 != X1 ),
% 3.77/0.89      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_288,plain,
% 3.77/0.89      ( ~ v5_tops_1(X0,sK0)
% 3.77/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | k2_tops_1(sK0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 3.77/0.89      inference(unflattening,[status(thm)],[c_287]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_415,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | k2_tops_1(sK0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 3.77/0.89      | sK1 != X0
% 3.77/0.89      | sK0 != sK0 ),
% 3.77/0.89      inference(resolution_lifted,[status(thm)],[c_18,c_288]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_416,plain,
% 3.77/0.89      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.77/0.89      inference(unflattening,[status(thm)],[c_415]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_418,plain,
% 3.77/0.89      ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.77/0.89      inference(global_propositional_subsumption,
% 3.77/0.89                [status(thm)],
% 3.77/0.89                [c_416,c_19]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_14,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | ~ l1_pre_topc(X1) ),
% 3.77/0.89      inference(cnf_transformation,[],[f56]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_302,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | sK0 != X1 ),
% 3.77/0.89      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_303,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.77/0.89      inference(unflattening,[status(thm)],[c_302]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_959,plain,
% 3.77/0.89      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.89      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1332,plain,
% 3.77/0.89      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.77/0.89      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_418,c_959]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1007,plain,
% 3.77/0.89      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.77/0.89      inference(instantiation,[status(thm)],[c_303]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1008,plain,
% 3.77/0.89      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.77/0.89      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_1007]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_2036,plain,
% 3.77/0.89      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.77/0.89      inference(global_propositional_subsumption,
% 3.77/0.89                [status(thm)],
% 3.77/0.89                [c_1332,c_22,c_1008]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_2040,plain,
% 3.77/0.89      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_2036,c_963]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_6,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/0.89      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.77/0.89      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 3.77/0.89      inference(cnf_transformation,[],[f48]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_163,plain,
% 3.77/0.89      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.77/0.89      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_164,plain,
% 3.77/0.89      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.77/0.89      inference(renaming,[status(thm)],[c_163]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_193,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/0.89      | ~ r1_tarski(X2,X1)
% 3.77/0.89      | k4_subset_1(X1,X2,X0) = k4_subset_1(X1,X0,X2) ),
% 3.77/0.89      inference(bin_hyper_res,[status(thm)],[c_6,c_164]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_487,plain,
% 3.77/0.89      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.77/0.89      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_488,plain,
% 3.77/0.89      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.77/0.89      inference(renaming,[status(thm)],[c_487]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_515,plain,
% 3.77/0.89      ( ~ r1_tarski(X0,X1)
% 3.77/0.89      | ~ r1_tarski(X2,X1)
% 3.77/0.89      | k4_subset_1(X1,X2,X0) = k4_subset_1(X1,X0,X2) ),
% 3.77/0.89      inference(bin_hyper_res,[status(thm)],[c_193,c_488]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_955,plain,
% 3.77/0.89      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
% 3.77/0.89      | r1_tarski(X2,X0) != iProver_top
% 3.77/0.89      | r1_tarski(X1,X0) != iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_2242,plain,
% 3.77/0.89      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
% 3.77/0.89      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_2040,c_955]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_8979,plain,
% 3.77/0.89      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_4432,c_2242]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_16,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | ~ l1_pre_topc(X1)
% 3.77/0.89      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.77/0.89      inference(cnf_transformation,[],[f58]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_275,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.89      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 3.77/0.89      | sK0 != X1 ),
% 3.77/0.89      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_276,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.89      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 3.77/0.89      inference(unflattening,[status(thm)],[c_275]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_960,plain,
% 3.77/0.89      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 3.77/0.89      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_1799,plain,
% 3.77/0.89      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 3.77/0.89      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_964,c_960]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_3823,plain,
% 3.77/0.89      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 3.77/0.89      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_2587,c_1799]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_3826,plain,
% 3.77/0.89      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1
% 3.77/0.89      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 3.77/0.89      inference(light_normalisation,[status(thm)],[c_3823,c_410,c_418]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_4064,plain,
% 3.77/0.89      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
% 3.77/0.89      inference(global_propositional_subsumption,
% 3.77/0.89                [status(thm)],
% 3.77/0.89                [c_3826,c_1578]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_7,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/0.89      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.77/0.89      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.77/0.89      inference(cnf_transformation,[],[f66]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_194,plain,
% 3.77/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/0.89      | ~ r1_tarski(X2,X1)
% 3.77/0.89      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 3.77/0.89      inference(bin_hyper_res,[status(thm)],[c_7,c_164]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_516,plain,
% 3.77/0.89      ( ~ r1_tarski(X0,X1)
% 3.77/0.89      | ~ r1_tarski(X2,X1)
% 3.77/0.89      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 3.77/0.89      inference(bin_hyper_res,[status(thm)],[c_194,c_488]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_954,plain,
% 3.77/0.89      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.77/0.89      | r1_tarski(X1,X0) != iProver_top
% 3.77/0.89      | r1_tarski(X2,X0) != iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_2046,plain,
% 3.77/0.89      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),X0))
% 3.77/0.89      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_2040,c_954]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_5258,plain,
% 3.77/0.89      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_4432,c_2046]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_8984,plain,
% 3.77/0.89      ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = sK1 ),
% 3.77/0.89      inference(light_normalisation,[status(thm)],[c_8979,c_4064,c_5258]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_9215,plain,
% 3.77/0.89      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.77/0.89      inference(superposition,[status(thm)],[c_8984,c_965]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_17,negated_conjecture,
% 3.77/0.89      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.77/0.89      inference(cnf_transformation,[],[f62]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_962,plain,
% 3.77/0.89      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 3.77/0.89      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(c_970,plain,
% 3.77/0.89      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 3.77/0.89      inference(light_normalisation,[status(thm)],[c_962,c_410]) ).
% 3.77/0.89  
% 3.77/0.89  cnf(contradiction,plain,
% 3.77/0.89      ( $false ),
% 3.77/0.89      inference(minisat,[status(thm)],[c_9215,c_970]) ).
% 3.77/0.89  
% 3.77/0.89  
% 3.77/0.89  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/0.89  
% 3.77/0.89  ------                               Statistics
% 3.77/0.89  
% 3.77/0.89  ------ General
% 3.77/0.89  
% 3.77/0.89  abstr_ref_over_cycles:                  0
% 3.77/0.89  abstr_ref_under_cycles:                 0
% 3.77/0.89  gc_basic_clause_elim:                   0
% 3.77/0.89  forced_gc_time:                         0
% 3.77/0.89  parsing_time:                           0.007
% 3.77/0.89  unif_index_cands_time:                  0.
% 3.77/0.89  unif_index_add_time:                    0.
% 3.77/0.89  orderings_time:                         0.
% 3.77/0.89  out_proof_time:                         0.01
% 3.77/0.89  total_time:                             0.361
% 3.77/0.89  num_of_symbols:                         45
% 3.77/0.89  num_of_terms:                           11730
% 3.77/0.89  
% 3.77/0.89  ------ Preprocessing
% 3.77/0.89  
% 3.77/0.89  num_of_splits:                          0
% 3.77/0.89  num_of_split_atoms:                     0
% 3.77/0.89  num_of_reused_defs:                     0
% 3.77/0.89  num_eq_ax_congr_red:                    9
% 3.77/0.89  num_of_sem_filtered_clauses:            1
% 3.77/0.89  num_of_subtypes:                        0
% 3.77/0.89  monotx_restored_types:                  0
% 3.77/0.89  sat_num_of_epr_types:                   0
% 3.77/0.89  sat_num_of_non_cyclic_types:            0
% 3.77/0.89  sat_guarded_non_collapsed_types:        0
% 3.77/0.89  num_pure_diseq_elim:                    0
% 3.77/0.89  simp_replaced_by:                       0
% 3.77/0.89  res_preprocessed:                       97
% 3.77/0.89  prep_upred:                             0
% 3.77/0.89  prep_unflattend:                        9
% 3.77/0.89  smt_new_axioms:                         0
% 3.77/0.89  pred_elim_cands:                        2
% 3.77/0.89  pred_elim:                              2
% 3.77/0.89  pred_elim_cl:                           2
% 3.77/0.89  pred_elim_cycles:                       4
% 3.77/0.89  merged_defs:                            8
% 3.77/0.89  merged_defs_ncl:                        0
% 3.77/0.89  bin_hyper_res:                          12
% 3.77/0.89  prep_cycles:                            4
% 3.77/0.89  pred_elim_time:                         0.001
% 3.77/0.89  splitting_time:                         0.
% 3.77/0.89  sem_filter_time:                        0.
% 3.77/0.89  monotx_time:                            0.
% 3.77/0.89  subtype_inf_time:                       0.
% 3.77/0.89  
% 3.77/0.89  ------ Problem properties
% 3.77/0.89  
% 3.77/0.89  clauses:                                18
% 3.77/0.89  conjectures:                            2
% 3.77/0.89  epr:                                    2
% 3.77/0.89  horn:                                   18
% 3.77/0.89  ground:                                 4
% 3.77/0.89  unary:                                  6
% 3.77/0.89  binary:                                 8
% 3.77/0.89  lits:                                   34
% 3.77/0.89  lits_eq:                                9
% 3.77/0.89  fd_pure:                                0
% 3.77/0.89  fd_pseudo:                              0
% 3.77/0.89  fd_cond:                                0
% 3.77/0.89  fd_pseudo_cond:                         1
% 3.77/0.89  ac_symbols:                             0
% 3.77/0.89  
% 3.77/0.89  ------ Propositional Solver
% 3.77/0.89  
% 3.77/0.89  prop_solver_calls:                      30
% 3.77/0.89  prop_fast_solver_calls:                 718
% 3.77/0.89  smt_solver_calls:                       0
% 3.77/0.89  smt_fast_solver_calls:                  0
% 3.77/0.89  prop_num_of_clauses:                    4663
% 3.77/0.89  prop_preprocess_simplified:             8220
% 3.77/0.89  prop_fo_subsumed:                       5
% 3.77/0.89  prop_solver_time:                       0.
% 3.77/0.89  smt_solver_time:                        0.
% 3.77/0.89  smt_fast_solver_time:                   0.
% 3.77/0.89  prop_fast_solver_time:                  0.
% 3.77/0.89  prop_unsat_core_time:                   0.
% 3.77/0.89  
% 3.77/0.89  ------ QBF
% 3.77/0.89  
% 3.77/0.89  qbf_q_res:                              0
% 3.77/0.89  qbf_num_tautologies:                    0
% 3.77/0.89  qbf_prep_cycles:                        0
% 3.77/0.89  
% 3.77/0.89  ------ BMC1
% 3.77/0.89  
% 3.77/0.89  bmc1_current_bound:                     -1
% 3.77/0.89  bmc1_last_solved_bound:                 -1
% 3.77/0.89  bmc1_unsat_core_size:                   -1
% 3.77/0.89  bmc1_unsat_core_parents_size:           -1
% 3.77/0.89  bmc1_merge_next_fun:                    0
% 3.77/0.89  bmc1_unsat_core_clauses_time:           0.
% 3.77/0.89  
% 3.77/0.89  ------ Instantiation
% 3.77/0.89  
% 3.77/0.89  inst_num_of_clauses:                    1203
% 3.77/0.89  inst_num_in_passive:                    117
% 3.77/0.89  inst_num_in_active:                     829
% 3.77/0.89  inst_num_in_unprocessed:                257
% 3.77/0.89  inst_num_of_loops:                      850
% 3.77/0.89  inst_num_of_learning_restarts:          0
% 3.77/0.89  inst_num_moves_active_passive:          20
% 3.77/0.89  inst_lit_activity:                      0
% 3.77/0.89  inst_lit_activity_moves:                1
% 3.77/0.89  inst_num_tautologies:                   0
% 3.77/0.89  inst_num_prop_implied:                  0
% 3.77/0.89  inst_num_existing_simplified:           0
% 3.77/0.89  inst_num_eq_res_simplified:             0
% 3.77/0.89  inst_num_child_elim:                    0
% 3.77/0.89  inst_num_of_dismatching_blockings:      640
% 3.77/0.89  inst_num_of_non_proper_insts:           1135
% 3.77/0.89  inst_num_of_duplicates:                 0
% 3.77/0.89  inst_inst_num_from_inst_to_res:         0
% 3.77/0.89  inst_dismatching_checking_time:         0.
% 3.77/0.89  
% 3.77/0.89  ------ Resolution
% 3.77/0.89  
% 3.77/0.89  res_num_of_clauses:                     0
% 3.77/0.89  res_num_in_passive:                     0
% 3.77/0.89  res_num_in_active:                      0
% 3.77/0.89  res_num_of_loops:                       101
% 3.77/0.89  res_forward_subset_subsumed:            72
% 3.77/0.89  res_backward_subset_subsumed:           0
% 3.77/0.89  res_forward_subsumed:                   0
% 3.77/0.89  res_backward_subsumed:                  0
% 3.77/0.89  res_forward_subsumption_resolution:     0
% 3.77/0.89  res_backward_subsumption_resolution:    0
% 3.77/0.89  res_clause_to_clause_subsumption:       2280
% 3.77/0.89  res_orphan_elimination:                 0
% 3.77/0.89  res_tautology_del:                      61
% 3.77/0.89  res_num_eq_res_simplified:              0
% 3.77/0.89  res_num_sel_changes:                    0
% 3.77/0.89  res_moves_from_active_to_pass:          0
% 3.77/0.89  
% 3.77/0.89  ------ Superposition
% 3.77/0.89  
% 3.77/0.89  sup_time_total:                         0.
% 3.77/0.89  sup_time_generating:                    0.
% 3.77/0.89  sup_time_sim_full:                      0.
% 3.77/0.89  sup_time_sim_immed:                     0.
% 3.77/0.89  
% 3.77/0.89  sup_num_of_clauses:                     544
% 3.77/0.89  sup_num_in_active:                      169
% 3.77/0.89  sup_num_in_passive:                     375
% 3.77/0.89  sup_num_of_loops:                       169
% 3.77/0.89  sup_fw_superposition:                   569
% 3.77/0.89  sup_bw_superposition:                   319
% 3.77/0.89  sup_immediate_simplified:               247
% 3.77/0.89  sup_given_eliminated:                   0
% 3.77/0.89  comparisons_done:                       0
% 3.77/0.89  comparisons_avoided:                    0
% 3.77/0.89  
% 3.77/0.89  ------ Simplifications
% 3.77/0.89  
% 3.77/0.89  
% 3.77/0.89  sim_fw_subset_subsumed:                 11
% 3.77/0.89  sim_bw_subset_subsumed:                 9
% 3.77/0.89  sim_fw_subsumed:                        11
% 3.77/0.89  sim_bw_subsumed:                        5
% 3.77/0.89  sim_fw_subsumption_res:                 0
% 3.77/0.89  sim_bw_subsumption_res:                 0
% 3.77/0.89  sim_tautology_del:                      2
% 3.77/0.89  sim_eq_tautology_del:                   71
% 3.77/0.89  sim_eq_res_simp:                        0
% 3.77/0.89  sim_fw_demodulated:                     91
% 3.77/0.89  sim_bw_demodulated:                     0
% 3.77/0.89  sim_light_normalised:                   131
% 3.77/0.89  sim_joinable_taut:                      0
% 3.77/0.89  sim_joinable_simp:                      0
% 3.77/0.89  sim_ac_normalised:                      0
% 3.77/0.89  sim_smt_subsumption:                    0
% 3.77/0.89  
%------------------------------------------------------------------------------
