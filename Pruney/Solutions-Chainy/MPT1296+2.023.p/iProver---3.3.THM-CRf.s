%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:17 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 405 expanded)
%              Number of clauses        :   84 ( 184 expanded)
%              Number of leaves         :   12 (  71 expanded)
%              Depth                    :   19
%              Number of atoms          :  274 ( 983 expanded)
%              Number of equality atoms :  157 ( 422 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) != k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) != k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
              | ~ r1_tarski(X1,k7_setfam_1(X0,X2)) )
            & ( r1_tarski(X1,k7_setfam_1(X0,X2))
              | ~ r1_tarski(k7_setfam_1(X0,X1),X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k7_setfam_1(X0,X2))
      | ~ r1_tarski(k7_setfam_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_setfam_1(X0,X1),X2)
      | ~ r1_tarski(X1,k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) != k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_499,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_496,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1061,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k7_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_496])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_497,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_492,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r1_tarski(X0,k7_setfam_1(X1,X2))
    | ~ r1_tarski(k7_setfam_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_494,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(X0,k7_setfam_1(X1,X2)) = iProver_top
    | r1_tarski(k7_setfam_1(X1,X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_766,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | r1_tarski(k7_setfam_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_492,c_494])).

cnf(c_1134,plain,
    ( r1_tarski(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k7_setfam_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_766])).

cnf(c_3460,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,k1_zfmisc_1(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_1134])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3868,plain,
    ( r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,k1_zfmisc_1(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3460,c_14])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X0,k7_setfam_1(X1,X2))
    | r1_tarski(k7_setfam_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_495,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(X0,k7_setfam_1(X1,X2)) != iProver_top
    | r1_tarski(k7_setfam_1(X1,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1497,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | r1_tarski(k7_setfam_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_492,c_495])).

cnf(c_1717,plain,
    ( r1_tarski(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k7_setfam_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_1497])).

cnf(c_3875,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
    | r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3868,c_1717])).

cnf(c_601,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_602,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_999,plain,
    ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(X2))
    | r1_tarski(k7_setfam_1(X0,X1),X2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2279,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(X0))
    | r1_tarski(k7_setfam_1(sK0,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_3501,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_3502,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3501])).

cnf(c_3992,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3875,c_14,c_602,c_3502])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,k7_setfam_1(X1,X0)) = k3_subset_1(X1,k5_setfam_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_493,plain,
    ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1542,plain,
    ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_493])).

cnf(c_5209,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | k7_setfam_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3992,c_1542])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_498,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_883,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_492,c_498])).

cnf(c_5231,plain,
    ( k7_setfam_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k6_setfam_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_5209,c_883])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_500,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1030,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k5_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_496])).

cnf(c_2599,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k5_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_1030])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_105,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_106,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_105])).

cnf(c_128,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_106])).

cnf(c_491,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_128])).

cnf(c_2743,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,X1))) = k5_setfam_1(X0,X1)
    | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2599,c_491])).

cnf(c_16672,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))) = k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3992,c_2743])).

cnf(c_17263,plain,
    ( k7_setfam_1(sK0,sK1) = k1_xboole_0
    | k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_5231,c_16672])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_43,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_46,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_45,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_47,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_587,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_588,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_182,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1014,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_setfam_1(X2,X3),X4)
    | X4 != X1
    | k7_setfam_1(X2,X3) != X0 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_2713,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_setfam_1(sK0,sK1),X2)
    | X2 != X1
    | k7_setfam_1(sK0,sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_2714,plain,
    ( X0 != X1
    | k7_setfam_1(sK0,sK1) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k7_setfam_1(sK0,sK1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2713])).

cnf(c_2716,plain,
    ( k7_setfam_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k7_setfam_1(sK0,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2714])).

cnf(c_502,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_882,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_498])).

cnf(c_1647,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_502,c_882])).

cnf(c_1696,plain,
    ( m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1647,c_499])).

cnf(c_590,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X0,k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_648,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_650,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top
    | r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_649,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_652,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_3633,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1696,c_650,c_652])).

cnf(c_3645,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k7_setfam_1(X1,k1_xboole_0),X0) = iProver_top
    | r1_tarski(k1_xboole_0,k7_setfam_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3633,c_495])).

cnf(c_7642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k7_setfam_1(X1,k1_xboole_0),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3645,c_502])).

cnf(c_7646,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k7_setfam_1(X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_7642])).

cnf(c_501,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7680,plain,
    ( k7_setfam_1(X0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7646,c_501])).

cnf(c_7918,plain,
    ( k7_setfam_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7680,c_652])).

cnf(c_3648,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3633,c_766])).

cnf(c_7925,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7918,c_3648])).

cnf(c_17373,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17263,c_12,c_43,c_46,c_47,c_588,c_2716,c_7925])).

cnf(c_11,negated_conjecture,
    ( k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) != k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17378,plain,
    ( k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_17373,c_11])).

cnf(c_17379,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_17378])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.48/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/0.99  
% 3.48/0.99  ------  iProver source info
% 3.48/0.99  
% 3.48/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.48/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/0.99  git: non_committed_changes: false
% 3.48/0.99  git: last_make_outside_of_git: false
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options
% 3.48/0.99  
% 3.48/0.99  --out_options                           all
% 3.48/0.99  --tptp_safe_out                         true
% 3.48/0.99  --problem_path                          ""
% 3.48/0.99  --include_path                          ""
% 3.48/0.99  --clausifier                            res/vclausify_rel
% 3.48/0.99  --clausifier_options                    --mode clausify
% 3.48/0.99  --stdin                                 false
% 3.48/0.99  --stats_out                             all
% 3.48/0.99  
% 3.48/0.99  ------ General Options
% 3.48/0.99  
% 3.48/0.99  --fof                                   false
% 3.48/0.99  --time_out_real                         305.
% 3.48/0.99  --time_out_virtual                      -1.
% 3.48/0.99  --symbol_type_check                     false
% 3.48/0.99  --clausify_out                          false
% 3.48/0.99  --sig_cnt_out                           false
% 3.48/0.99  --trig_cnt_out                          false
% 3.48/0.99  --trig_cnt_out_tolerance                1.
% 3.48/0.99  --trig_cnt_out_sk_spl                   false
% 3.48/0.99  --abstr_cl_out                          false
% 3.48/0.99  
% 3.48/0.99  ------ Global Options
% 3.48/0.99  
% 3.48/0.99  --schedule                              default
% 3.48/0.99  --add_important_lit                     false
% 3.48/0.99  --prop_solver_per_cl                    1000
% 3.48/0.99  --min_unsat_core                        false
% 3.48/0.99  --soft_assumptions                      false
% 3.48/0.99  --soft_lemma_size                       3
% 3.48/0.99  --prop_impl_unit_size                   0
% 3.48/0.99  --prop_impl_unit                        []
% 3.48/0.99  --share_sel_clauses                     true
% 3.48/0.99  --reset_solvers                         false
% 3.48/0.99  --bc_imp_inh                            [conj_cone]
% 3.48/0.99  --conj_cone_tolerance                   3.
% 3.48/0.99  --extra_neg_conj                        none
% 3.48/0.99  --large_theory_mode                     true
% 3.48/0.99  --prolific_symb_bound                   200
% 3.48/0.99  --lt_threshold                          2000
% 3.48/0.99  --clause_weak_htbl                      true
% 3.48/0.99  --gc_record_bc_elim                     false
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing Options
% 3.48/0.99  
% 3.48/0.99  --preprocessing_flag                    true
% 3.48/0.99  --time_out_prep_mult                    0.1
% 3.48/0.99  --splitting_mode                        input
% 3.48/0.99  --splitting_grd                         true
% 3.48/0.99  --splitting_cvd                         false
% 3.48/0.99  --splitting_cvd_svl                     false
% 3.48/0.99  --splitting_nvd                         32
% 3.48/0.99  --sub_typing                            true
% 3.48/0.99  --prep_gs_sim                           true
% 3.48/0.99  --prep_unflatten                        true
% 3.48/0.99  --prep_res_sim                          true
% 3.48/0.99  --prep_upred                            true
% 3.48/0.99  --prep_sem_filter                       exhaustive
% 3.48/0.99  --prep_sem_filter_out                   false
% 3.48/0.99  --pred_elim                             true
% 3.48/0.99  --res_sim_input                         true
% 3.48/0.99  --eq_ax_congr_red                       true
% 3.48/0.99  --pure_diseq_elim                       true
% 3.48/0.99  --brand_transform                       false
% 3.48/0.99  --non_eq_to_eq                          false
% 3.48/0.99  --prep_def_merge                        true
% 3.48/0.99  --prep_def_merge_prop_impl              false
% 3.48/0.99  --prep_def_merge_mbd                    true
% 3.48/0.99  --prep_def_merge_tr_red                 false
% 3.48/0.99  --prep_def_merge_tr_cl                  false
% 3.48/0.99  --smt_preprocessing                     true
% 3.48/0.99  --smt_ac_axioms                         fast
% 3.48/0.99  --preprocessed_out                      false
% 3.48/0.99  --preprocessed_stats                    false
% 3.48/0.99  
% 3.48/0.99  ------ Abstraction refinement Options
% 3.48/0.99  
% 3.48/0.99  --abstr_ref                             []
% 3.48/0.99  --abstr_ref_prep                        false
% 3.48/0.99  --abstr_ref_until_sat                   false
% 3.48/0.99  --abstr_ref_sig_restrict                funpre
% 3.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/0.99  --abstr_ref_under                       []
% 3.48/0.99  
% 3.48/0.99  ------ SAT Options
% 3.48/0.99  
% 3.48/0.99  --sat_mode                              false
% 3.48/0.99  --sat_fm_restart_options                ""
% 3.48/0.99  --sat_gr_def                            false
% 3.48/0.99  --sat_epr_types                         true
% 3.48/0.99  --sat_non_cyclic_types                  false
% 3.48/0.99  --sat_finite_models                     false
% 3.48/0.99  --sat_fm_lemmas                         false
% 3.48/0.99  --sat_fm_prep                           false
% 3.48/0.99  --sat_fm_uc_incr                        true
% 3.48/0.99  --sat_out_model                         small
% 3.48/0.99  --sat_out_clauses                       false
% 3.48/0.99  
% 3.48/0.99  ------ QBF Options
% 3.48/0.99  
% 3.48/0.99  --qbf_mode                              false
% 3.48/0.99  --qbf_elim_univ                         false
% 3.48/0.99  --qbf_dom_inst                          none
% 3.48/0.99  --qbf_dom_pre_inst                      false
% 3.48/0.99  --qbf_sk_in                             false
% 3.48/0.99  --qbf_pred_elim                         true
% 3.48/0.99  --qbf_split                             512
% 3.48/0.99  
% 3.48/0.99  ------ BMC1 Options
% 3.48/0.99  
% 3.48/0.99  --bmc1_incremental                      false
% 3.48/0.99  --bmc1_axioms                           reachable_all
% 3.48/0.99  --bmc1_min_bound                        0
% 3.48/0.99  --bmc1_max_bound                        -1
% 3.48/0.99  --bmc1_max_bound_default                -1
% 3.48/0.99  --bmc1_symbol_reachability              true
% 3.48/0.99  --bmc1_property_lemmas                  false
% 3.48/0.99  --bmc1_k_induction                      false
% 3.48/0.99  --bmc1_non_equiv_states                 false
% 3.48/0.99  --bmc1_deadlock                         false
% 3.48/0.99  --bmc1_ucm                              false
% 3.48/0.99  --bmc1_add_unsat_core                   none
% 3.48/0.99  --bmc1_unsat_core_children              false
% 3.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/0.99  --bmc1_out_stat                         full
% 3.48/0.99  --bmc1_ground_init                      false
% 3.48/0.99  --bmc1_pre_inst_next_state              false
% 3.48/0.99  --bmc1_pre_inst_state                   false
% 3.48/0.99  --bmc1_pre_inst_reach_state             false
% 3.48/0.99  --bmc1_out_unsat_core                   false
% 3.48/0.99  --bmc1_aig_witness_out                  false
% 3.48/0.99  --bmc1_verbose                          false
% 3.48/0.99  --bmc1_dump_clauses_tptp                false
% 3.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.48/0.99  --bmc1_dump_file                        -
% 3.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.48/0.99  --bmc1_ucm_extend_mode                  1
% 3.48/0.99  --bmc1_ucm_init_mode                    2
% 3.48/0.99  --bmc1_ucm_cone_mode                    none
% 3.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.48/0.99  --bmc1_ucm_relax_model                  4
% 3.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/0.99  --bmc1_ucm_layered_model                none
% 3.48/0.99  --bmc1_ucm_max_lemma_size               10
% 3.48/0.99  
% 3.48/0.99  ------ AIG Options
% 3.48/0.99  
% 3.48/0.99  --aig_mode                              false
% 3.48/0.99  
% 3.48/0.99  ------ Instantiation Options
% 3.48/0.99  
% 3.48/0.99  --instantiation_flag                    true
% 3.48/0.99  --inst_sos_flag                         false
% 3.48/0.99  --inst_sos_phase                        true
% 3.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel_side                     num_symb
% 3.48/0.99  --inst_solver_per_active                1400
% 3.48/0.99  --inst_solver_calls_frac                1.
% 3.48/0.99  --inst_passive_queue_type               priority_queues
% 3.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/0.99  --inst_passive_queues_freq              [25;2]
% 3.48/0.99  --inst_dismatching                      true
% 3.48/0.99  --inst_eager_unprocessed_to_passive     true
% 3.48/0.99  --inst_prop_sim_given                   true
% 3.48/0.99  --inst_prop_sim_new                     false
% 3.48/0.99  --inst_subs_new                         false
% 3.48/0.99  --inst_eq_res_simp                      false
% 3.48/0.99  --inst_subs_given                       false
% 3.48/0.99  --inst_orphan_elimination               true
% 3.48/0.99  --inst_learning_loop_flag               true
% 3.48/0.99  --inst_learning_start                   3000
% 3.48/0.99  --inst_learning_factor                  2
% 3.48/0.99  --inst_start_prop_sim_after_learn       3
% 3.48/0.99  --inst_sel_renew                        solver
% 3.48/0.99  --inst_lit_activity_flag                true
% 3.48/0.99  --inst_restr_to_given                   false
% 3.48/0.99  --inst_activity_threshold               500
% 3.48/0.99  --inst_out_proof                        true
% 3.48/0.99  
% 3.48/0.99  ------ Resolution Options
% 3.48/0.99  
% 3.48/0.99  --resolution_flag                       true
% 3.48/0.99  --res_lit_sel                           adaptive
% 3.48/0.99  --res_lit_sel_side                      none
% 3.48/0.99  --res_ordering                          kbo
% 3.48/0.99  --res_to_prop_solver                    active
% 3.48/0.99  --res_prop_simpl_new                    false
% 3.48/0.99  --res_prop_simpl_given                  true
% 3.48/0.99  --res_passive_queue_type                priority_queues
% 3.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/0.99  --res_passive_queues_freq               [15;5]
% 3.48/0.99  --res_forward_subs                      full
% 3.48/0.99  --res_backward_subs                     full
% 3.48/0.99  --res_forward_subs_resolution           true
% 3.48/0.99  --res_backward_subs_resolution          true
% 3.48/0.99  --res_orphan_elimination                true
% 3.48/0.99  --res_time_limit                        2.
% 3.48/0.99  --res_out_proof                         true
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Options
% 3.48/0.99  
% 3.48/0.99  --superposition_flag                    true
% 3.48/0.99  --sup_passive_queue_type                priority_queues
% 3.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.48/0.99  --demod_completeness_check              fast
% 3.48/0.99  --demod_use_ground                      true
% 3.48/0.99  --sup_to_prop_solver                    passive
% 3.48/0.99  --sup_prop_simpl_new                    true
% 3.48/0.99  --sup_prop_simpl_given                  true
% 3.48/0.99  --sup_fun_splitting                     false
% 3.48/0.99  --sup_smt_interval                      50000
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Simplification Setup
% 3.48/0.99  
% 3.48/0.99  --sup_indices_passive                   []
% 3.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_full_bw                           [BwDemod]
% 3.48/0.99  --sup_immed_triv                        [TrivRules]
% 3.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_immed_bw_main                     []
% 3.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  
% 3.48/0.99  ------ Combination Options
% 3.48/0.99  
% 3.48/0.99  --comb_res_mult                         3
% 3.48/0.99  --comb_sup_mult                         2
% 3.48/0.99  --comb_inst_mult                        10
% 3.48/0.99  
% 3.48/0.99  ------ Debug Options
% 3.48/0.99  
% 3.48/0.99  --dbg_backtrace                         false
% 3.48/0.99  --dbg_dump_prop_clauses                 false
% 3.48/0.99  --dbg_dump_prop_clauses_file            -
% 3.48/0.99  --dbg_out_stat                          false
% 3.48/0.99  ------ Parsing...
% 3.48/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  ------ Proving...
% 3.48/0.99  ------ Problem Properties 
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  clauses                                 14
% 3.48/0.99  conjectures                             3
% 3.48/0.99  EPR                                     3
% 3.48/0.99  Horn                                    13
% 3.48/0.99  unary                                   4
% 3.48/0.99  binary                                  7
% 3.48/0.99  lits                                    29
% 3.48/0.99  lits eq                                 7
% 3.48/0.99  fd_pure                                 0
% 3.48/0.99  fd_pseudo                               0
% 3.48/0.99  fd_cond                                 2
% 3.48/0.99  fd_pseudo_cond                          0
% 3.48/0.99  AC symbols                              0
% 3.48/0.99  
% 3.48/0.99  ------ Schedule dynamic 5 is on 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  Current options:
% 3.48/0.99  ------ 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options
% 3.48/0.99  
% 3.48/0.99  --out_options                           all
% 3.48/0.99  --tptp_safe_out                         true
% 3.48/0.99  --problem_path                          ""
% 3.48/0.99  --include_path                          ""
% 3.48/0.99  --clausifier                            res/vclausify_rel
% 3.48/0.99  --clausifier_options                    --mode clausify
% 3.48/0.99  --stdin                                 false
% 3.48/0.99  --stats_out                             all
% 3.48/0.99  
% 3.48/0.99  ------ General Options
% 3.48/0.99  
% 3.48/0.99  --fof                                   false
% 3.48/0.99  --time_out_real                         305.
% 3.48/0.99  --time_out_virtual                      -1.
% 3.48/0.99  --symbol_type_check                     false
% 3.48/0.99  --clausify_out                          false
% 3.48/0.99  --sig_cnt_out                           false
% 3.48/0.99  --trig_cnt_out                          false
% 3.48/0.99  --trig_cnt_out_tolerance                1.
% 3.48/0.99  --trig_cnt_out_sk_spl                   false
% 3.48/0.99  --abstr_cl_out                          false
% 3.48/0.99  
% 3.48/0.99  ------ Global Options
% 3.48/0.99  
% 3.48/0.99  --schedule                              default
% 3.48/0.99  --add_important_lit                     false
% 3.48/0.99  --prop_solver_per_cl                    1000
% 3.48/0.99  --min_unsat_core                        false
% 3.48/0.99  --soft_assumptions                      false
% 3.48/0.99  --soft_lemma_size                       3
% 3.48/0.99  --prop_impl_unit_size                   0
% 3.48/0.99  --prop_impl_unit                        []
% 3.48/0.99  --share_sel_clauses                     true
% 3.48/0.99  --reset_solvers                         false
% 3.48/0.99  --bc_imp_inh                            [conj_cone]
% 3.48/0.99  --conj_cone_tolerance                   3.
% 3.48/0.99  --extra_neg_conj                        none
% 3.48/0.99  --large_theory_mode                     true
% 3.48/0.99  --prolific_symb_bound                   200
% 3.48/0.99  --lt_threshold                          2000
% 3.48/0.99  --clause_weak_htbl                      true
% 3.48/0.99  --gc_record_bc_elim                     false
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing Options
% 3.48/0.99  
% 3.48/0.99  --preprocessing_flag                    true
% 3.48/0.99  --time_out_prep_mult                    0.1
% 3.48/0.99  --splitting_mode                        input
% 3.48/0.99  --splitting_grd                         true
% 3.48/0.99  --splitting_cvd                         false
% 3.48/0.99  --splitting_cvd_svl                     false
% 3.48/0.99  --splitting_nvd                         32
% 3.48/0.99  --sub_typing                            true
% 3.48/0.99  --prep_gs_sim                           true
% 3.48/0.99  --prep_unflatten                        true
% 3.48/0.99  --prep_res_sim                          true
% 3.48/0.99  --prep_upred                            true
% 3.48/0.99  --prep_sem_filter                       exhaustive
% 3.48/0.99  --prep_sem_filter_out                   false
% 3.48/0.99  --pred_elim                             true
% 3.48/0.99  --res_sim_input                         true
% 3.48/0.99  --eq_ax_congr_red                       true
% 3.48/0.99  --pure_diseq_elim                       true
% 3.48/0.99  --brand_transform                       false
% 3.48/0.99  --non_eq_to_eq                          false
% 3.48/0.99  --prep_def_merge                        true
% 3.48/0.99  --prep_def_merge_prop_impl              false
% 3.48/0.99  --prep_def_merge_mbd                    true
% 3.48/0.99  --prep_def_merge_tr_red                 false
% 3.48/0.99  --prep_def_merge_tr_cl                  false
% 3.48/0.99  --smt_preprocessing                     true
% 3.48/0.99  --smt_ac_axioms                         fast
% 3.48/0.99  --preprocessed_out                      false
% 3.48/0.99  --preprocessed_stats                    false
% 3.48/0.99  
% 3.48/0.99  ------ Abstraction refinement Options
% 3.48/0.99  
% 3.48/0.99  --abstr_ref                             []
% 3.48/0.99  --abstr_ref_prep                        false
% 3.48/0.99  --abstr_ref_until_sat                   false
% 3.48/0.99  --abstr_ref_sig_restrict                funpre
% 3.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/0.99  --abstr_ref_under                       []
% 3.48/0.99  
% 3.48/0.99  ------ SAT Options
% 3.48/0.99  
% 3.48/0.99  --sat_mode                              false
% 3.48/0.99  --sat_fm_restart_options                ""
% 3.48/0.99  --sat_gr_def                            false
% 3.48/0.99  --sat_epr_types                         true
% 3.48/0.99  --sat_non_cyclic_types                  false
% 3.48/0.99  --sat_finite_models                     false
% 3.48/0.99  --sat_fm_lemmas                         false
% 3.48/0.99  --sat_fm_prep                           false
% 3.48/0.99  --sat_fm_uc_incr                        true
% 3.48/0.99  --sat_out_model                         small
% 3.48/0.99  --sat_out_clauses                       false
% 3.48/0.99  
% 3.48/0.99  ------ QBF Options
% 3.48/0.99  
% 3.48/0.99  --qbf_mode                              false
% 3.48/0.99  --qbf_elim_univ                         false
% 3.48/0.99  --qbf_dom_inst                          none
% 3.48/0.99  --qbf_dom_pre_inst                      false
% 3.48/0.99  --qbf_sk_in                             false
% 3.48/0.99  --qbf_pred_elim                         true
% 3.48/0.99  --qbf_split                             512
% 3.48/0.99  
% 3.48/0.99  ------ BMC1 Options
% 3.48/0.99  
% 3.48/0.99  --bmc1_incremental                      false
% 3.48/0.99  --bmc1_axioms                           reachable_all
% 3.48/0.99  --bmc1_min_bound                        0
% 3.48/0.99  --bmc1_max_bound                        -1
% 3.48/0.99  --bmc1_max_bound_default                -1
% 3.48/0.99  --bmc1_symbol_reachability              true
% 3.48/0.99  --bmc1_property_lemmas                  false
% 3.48/0.99  --bmc1_k_induction                      false
% 3.48/0.99  --bmc1_non_equiv_states                 false
% 3.48/0.99  --bmc1_deadlock                         false
% 3.48/0.99  --bmc1_ucm                              false
% 3.48/0.99  --bmc1_add_unsat_core                   none
% 3.48/0.99  --bmc1_unsat_core_children              false
% 3.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/0.99  --bmc1_out_stat                         full
% 3.48/0.99  --bmc1_ground_init                      false
% 3.48/0.99  --bmc1_pre_inst_next_state              false
% 3.48/0.99  --bmc1_pre_inst_state                   false
% 3.48/0.99  --bmc1_pre_inst_reach_state             false
% 3.48/0.99  --bmc1_out_unsat_core                   false
% 3.48/0.99  --bmc1_aig_witness_out                  false
% 3.48/0.99  --bmc1_verbose                          false
% 3.48/0.99  --bmc1_dump_clauses_tptp                false
% 3.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.48/0.99  --bmc1_dump_file                        -
% 3.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.48/0.99  --bmc1_ucm_extend_mode                  1
% 3.48/0.99  --bmc1_ucm_init_mode                    2
% 3.48/0.99  --bmc1_ucm_cone_mode                    none
% 3.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.48/0.99  --bmc1_ucm_relax_model                  4
% 3.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/0.99  --bmc1_ucm_layered_model                none
% 3.48/0.99  --bmc1_ucm_max_lemma_size               10
% 3.48/0.99  
% 3.48/0.99  ------ AIG Options
% 3.48/0.99  
% 3.48/0.99  --aig_mode                              false
% 3.48/0.99  
% 3.48/0.99  ------ Instantiation Options
% 3.48/0.99  
% 3.48/0.99  --instantiation_flag                    true
% 3.48/0.99  --inst_sos_flag                         false
% 3.48/0.99  --inst_sos_phase                        true
% 3.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel_side                     none
% 3.48/0.99  --inst_solver_per_active                1400
% 3.48/0.99  --inst_solver_calls_frac                1.
% 3.48/0.99  --inst_passive_queue_type               priority_queues
% 3.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/0.99  --inst_passive_queues_freq              [25;2]
% 3.48/0.99  --inst_dismatching                      true
% 3.48/0.99  --inst_eager_unprocessed_to_passive     true
% 3.48/0.99  --inst_prop_sim_given                   true
% 3.48/0.99  --inst_prop_sim_new                     false
% 3.48/0.99  --inst_subs_new                         false
% 3.48/0.99  --inst_eq_res_simp                      false
% 3.48/0.99  --inst_subs_given                       false
% 3.48/0.99  --inst_orphan_elimination               true
% 3.48/0.99  --inst_learning_loop_flag               true
% 3.48/0.99  --inst_learning_start                   3000
% 3.48/0.99  --inst_learning_factor                  2
% 3.48/0.99  --inst_start_prop_sim_after_learn       3
% 3.48/0.99  --inst_sel_renew                        solver
% 3.48/0.99  --inst_lit_activity_flag                true
% 3.48/0.99  --inst_restr_to_given                   false
% 3.48/0.99  --inst_activity_threshold               500
% 3.48/0.99  --inst_out_proof                        true
% 3.48/0.99  
% 3.48/0.99  ------ Resolution Options
% 3.48/0.99  
% 3.48/0.99  --resolution_flag                       false
% 3.48/0.99  --res_lit_sel                           adaptive
% 3.48/0.99  --res_lit_sel_side                      none
% 3.48/0.99  --res_ordering                          kbo
% 3.48/0.99  --res_to_prop_solver                    active
% 3.48/0.99  --res_prop_simpl_new                    false
% 3.48/0.99  --res_prop_simpl_given                  true
% 3.48/0.99  --res_passive_queue_type                priority_queues
% 3.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/0.99  --res_passive_queues_freq               [15;5]
% 3.48/0.99  --res_forward_subs                      full
% 3.48/0.99  --res_backward_subs                     full
% 3.48/0.99  --res_forward_subs_resolution           true
% 3.48/0.99  --res_backward_subs_resolution          true
% 3.48/0.99  --res_orphan_elimination                true
% 3.48/0.99  --res_time_limit                        2.
% 3.48/0.99  --res_out_proof                         true
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Options
% 3.48/0.99  
% 3.48/0.99  --superposition_flag                    true
% 3.48/0.99  --sup_passive_queue_type                priority_queues
% 3.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.48/0.99  --demod_completeness_check              fast
% 3.48/0.99  --demod_use_ground                      true
% 3.48/0.99  --sup_to_prop_solver                    passive
% 3.48/0.99  --sup_prop_simpl_new                    true
% 3.48/0.99  --sup_prop_simpl_given                  true
% 3.48/0.99  --sup_fun_splitting                     false
% 3.48/0.99  --sup_smt_interval                      50000
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Simplification Setup
% 3.48/0.99  
% 3.48/0.99  --sup_indices_passive                   []
% 3.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_full_bw                           [BwDemod]
% 3.48/0.99  --sup_immed_triv                        [TrivRules]
% 3.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_immed_bw_main                     []
% 3.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  
% 3.48/0.99  ------ Combination Options
% 3.48/0.99  
% 3.48/0.99  --comb_res_mult                         3
% 3.48/0.99  --comb_sup_mult                         2
% 3.48/0.99  --comb_inst_mult                        10
% 3.48/0.99  
% 3.48/0.99  ------ Debug Options
% 3.48/0.99  
% 3.48/0.99  --dbg_backtrace                         false
% 3.48/0.99  --dbg_dump_prop_clauses                 false
% 3.48/0.99  --dbg_dump_prop_clauses_file            -
% 3.48/0.99  --dbg_out_stat                          false
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  % SZS status Theorem for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99   Resolution empty clause
% 3.48/0.99  
% 3.48/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  fof(f5,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f15,plain,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.48/0.99    inference(ennf_transformation,[],[f5])).
% 3.48/0.99  
% 3.48/0.99  fof(f30,plain,(
% 3.48/0.99    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f15])).
% 3.48/0.99  
% 3.48/0.99  fof(f7,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f22,plain,(
% 3.48/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.48/0.99    inference(nnf_transformation,[],[f7])).
% 3.48/0.99  
% 3.48/0.99  fof(f32,plain,(
% 3.48/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f22])).
% 3.48/0.99  
% 3.48/0.99  fof(f33,plain,(
% 3.48/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f22])).
% 3.48/0.99  
% 3.48/0.99  fof(f10,conjecture,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f11,negated_conjecture,(
% 3.48/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 3.48/0.99    inference(negated_conjecture,[],[f10])).
% 3.48/0.99  
% 3.48/0.99  fof(f20,plain,(
% 3.48/0.99    ? [X0,X1] : ((k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.48/0.99    inference(ennf_transformation,[],[f11])).
% 3.48/0.99  
% 3.48/0.99  fof(f21,plain,(
% 3.48/0.99    ? [X0,X1] : (k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.48/0.99    inference(flattening,[],[f20])).
% 3.48/0.99  
% 3.48/0.99  fof(f24,plain,(
% 3.48/0.99    ? [X0,X1] : (k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) != k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f25,plain,(
% 3.48/0.99    k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) != k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 3.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 3.48/0.99  
% 3.48/0.99  fof(f37,plain,(
% 3.48/0.99    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 3.48/0.99    inference(cnf_transformation,[],[f25])).
% 3.48/0.99  
% 3.48/0.99  fof(f8,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2)))))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f17,plain,(
% 3.48/0.99    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.48/0.99    inference(ennf_transformation,[],[f8])).
% 3.48/0.99  
% 3.48/0.99  fof(f23,plain,(
% 3.48/0.99    ! [X0,X1] : (! [X2] : (((r1_tarski(k7_setfam_1(X0,X1),X2) | ~r1_tarski(X1,k7_setfam_1(X0,X2))) & (r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.48/0.99    inference(nnf_transformation,[],[f17])).
% 3.48/0.99  
% 3.48/0.99  fof(f34,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f23])).
% 3.48/0.99  
% 3.48/0.99  fof(f35,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (r1_tarski(k7_setfam_1(X0,X1),X2) | ~r1_tarski(X1,k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f23])).
% 3.48/0.99  
% 3.48/0.99  fof(f9,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f18,plain,(
% 3.48/0.99    ! [X0,X1] : ((k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.48/0.99    inference(ennf_transformation,[],[f9])).
% 3.48/0.99  
% 3.48/0.99  fof(f19,plain,(
% 3.48/0.99    ! [X0,X1] : (k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.48/0.99    inference(flattening,[],[f18])).
% 3.48/0.99  
% 3.48/0.99  fof(f36,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f19])).
% 3.48/0.99  
% 3.48/0.99  fof(f6,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f16,plain,(
% 3.48/0.99    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.48/0.99    inference(ennf_transformation,[],[f6])).
% 3.48/0.99  
% 3.48/0.99  fof(f31,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f16])).
% 3.48/0.99  
% 3.48/0.99  fof(f4,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f14,plain,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.48/0.99    inference(ennf_transformation,[],[f4])).
% 3.48/0.99  
% 3.48/0.99  fof(f29,plain,(
% 3.48/0.99    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f14])).
% 3.48/0.99  
% 3.48/0.99  fof(f3,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f13,plain,(
% 3.48/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f3])).
% 3.48/0.99  
% 3.48/0.99  fof(f28,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f13])).
% 3.48/0.99  
% 3.48/0.99  fof(f38,plain,(
% 3.48/0.99    k1_xboole_0 != sK1),
% 3.48/0.99    inference(cnf_transformation,[],[f25])).
% 3.48/0.99  
% 3.48/0.99  fof(f2,axiom,(
% 3.48/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f12,plain,(
% 3.48/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.48/0.99    inference(ennf_transformation,[],[f2])).
% 3.48/0.99  
% 3.48/0.99  fof(f27,plain,(
% 3.48/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f12])).
% 3.48/0.99  
% 3.48/0.99  fof(f1,axiom,(
% 3.48/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f26,plain,(
% 3.48/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f1])).
% 3.48/0.99  
% 3.48/0.99  fof(f39,plain,(
% 3.48/0.99    k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) != k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 3.48/0.99    inference(cnf_transformation,[],[f25])).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.48/0.99      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 3.48/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_499,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_496,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.48/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1061,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_499,c_496]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_497,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.48/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_13,negated_conjecture,
% 3.48/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 3.48/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_492,plain,
% 3.48/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_9,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.48/0.99      | r1_tarski(X0,k7_setfam_1(X1,X2))
% 3.48/0.99      | ~ r1_tarski(k7_setfam_1(X1,X0),X2) ),
% 3.48/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_494,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.48/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.48/0.99      | r1_tarski(X0,k7_setfam_1(X1,X2)) = iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(X1,X0),X2) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_766,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(sK0,sK1),X0) != iProver_top
% 3.48/0.99      | r1_tarski(sK1,k7_setfam_1(sK0,X0)) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_492,c_494]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1134,plain,
% 3.48/0.99      ( r1_tarski(X0,k1_zfmisc_1(sK0)) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(sK0,sK1),X0) != iProver_top
% 3.48/0.99      | r1_tarski(sK1,k7_setfam_1(sK0,X0)) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_497,c_766]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3460,plain,
% 3.48/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 3.48/0.99      | r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)) != iProver_top
% 3.48/0.99      | r1_tarski(sK1,k7_setfam_1(sK0,k1_zfmisc_1(sK0))) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_1061,c_1134]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_14,plain,
% 3.48/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3868,plain,
% 3.48/0.99      ( r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)) != iProver_top
% 3.48/0.99      | r1_tarski(sK1,k7_setfam_1(sK0,k1_zfmisc_1(sK0))) = iProver_top ),
% 3.48/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3460,c_14]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.48/0.99      | ~ r1_tarski(X0,k7_setfam_1(X1,X2))
% 3.48/0.99      | r1_tarski(k7_setfam_1(X1,X0),X2) ),
% 3.48/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_495,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.48/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.48/0.99      | r1_tarski(X0,k7_setfam_1(X1,X2)) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(X1,X0),X2) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1497,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(sK0,sK1),X0) = iProver_top
% 3.48/0.99      | r1_tarski(sK1,k7_setfam_1(sK0,X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_492,c_495]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1717,plain,
% 3.48/0.99      ( r1_tarski(X0,k1_zfmisc_1(sK0)) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(sK0,sK1),X0) = iProver_top
% 3.48/0.99      | r1_tarski(sK1,k7_setfam_1(sK0,X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_497,c_1497]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3875,plain,
% 3.48/0.99      ( r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
% 3.48/0.99      | r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3868,c_1717]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_601,plain,
% 3.48/0.99      ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 3.48/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_602,plain,
% 3.48/0.99      ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top
% 3.48/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_999,plain,
% 3.48/0.99      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(X2))
% 3.48/0.99      | r1_tarski(k7_setfam_1(X0,X1),X2) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2279,plain,
% 3.48/0.99      ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(X0))
% 3.48/0.99      | r1_tarski(k7_setfam_1(sK0,sK1),X0) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_999]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3501,plain,
% 3.48/0.99      ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 3.48/0.99      | r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_2279]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3502,plain,
% 3.48/0.99      ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_3501]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3992,plain,
% 3.48/0.99      ( r1_tarski(k7_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
% 3.48/0.99      inference(global_propositional_subsumption,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_3875,c_14,c_602,c_3502]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_10,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.48/0.99      | k6_setfam_1(X1,k7_setfam_1(X1,X0)) = k3_subset_1(X1,k5_setfam_1(X1,X0))
% 3.48/0.99      | k1_xboole_0 = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_493,plain,
% 3.48/0.99      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
% 3.48/0.99      | k1_xboole_0 = X1
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1542,plain,
% 3.48/0.99      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
% 3.48/0.99      | k1_xboole_0 = X1
% 3.48/0.99      | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_497,c_493]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5209,plain,
% 3.48/0.99      ( k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
% 3.48/0.99      | k7_setfam_1(sK0,sK1) = k1_xboole_0 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3992,c_1542]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.48/0.99      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_498,plain,
% 3.48/0.99      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_883,plain,
% 3.48/0.99      ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_492,c_498]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5231,plain,
% 3.48/0.99      ( k7_setfam_1(sK0,sK1) = k1_xboole_0
% 3.48/0.99      | k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k6_setfam_1(sK0,sK1) ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_5209,c_883]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.48/0.99      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_500,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.48/0.99      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1030,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.48/0.99      | r1_tarski(k5_setfam_1(X1,X0),X1) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_500,c_496]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2599,plain,
% 3.48/0.99      ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.48/0.99      | r1_tarski(k5_setfam_1(X1,X0),X1) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_497,c_1030]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_105,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.48/0.99      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_106,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.48/0.99      inference(renaming,[status(thm)],[c_105]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_128,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.48/0.99      inference(bin_hyper_res,[status(thm)],[c_2,c_106]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_491,plain,
% 3.48/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.48/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_128]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2743,plain,
% 3.48/0.99      ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,X1))) = k5_setfam_1(X0,X1)
% 3.48/0.99      | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2599,c_491]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_16672,plain,
% 3.48/0.99      ( k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))) = k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3992,c_2743]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_17263,plain,
% 3.48/0.99      ( k7_setfam_1(sK0,sK1) = k1_xboole_0
% 3.48/0.99      | k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_5231,c_16672]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_12,negated_conjecture,
% 3.48/0.99      ( k1_xboole_0 != sK1 ),
% 3.48/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_43,plain,
% 3.48/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_0,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_46,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_45,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_47,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_45]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_587,plain,
% 3.48/0.99      ( ~ r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_588,plain,
% 3.48/0.99      ( k1_xboole_0 = sK1 | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_182,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.48/0.99      theory(equality) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1014,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1)
% 3.48/0.99      | r1_tarski(k7_setfam_1(X2,X3),X4)
% 3.48/0.99      | X4 != X1
% 3.48/0.99      | k7_setfam_1(X2,X3) != X0 ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_182]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2713,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1)
% 3.48/0.99      | r1_tarski(k7_setfam_1(sK0,sK1),X2)
% 3.48/0.99      | X2 != X1
% 3.48/0.99      | k7_setfam_1(sK0,sK1) != X0 ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_1014]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2714,plain,
% 3.48/0.99      ( X0 != X1
% 3.48/0.99      | k7_setfam_1(sK0,sK1) != X2
% 3.48/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(sK0,sK1),X0) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_2713]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2716,plain,
% 3.48/0.99      ( k7_setfam_1(sK0,sK1) != k1_xboole_0
% 3.48/0.99      | k1_xboole_0 != k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_setfam_1(sK0,sK1),k1_xboole_0) = iProver_top
% 3.48/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_2714]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_502,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_882,plain,
% 3.48/0.99      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 3.48/0.99      | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_497,c_498]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1647,plain,
% 3.48/0.99      ( k7_setfam_1(X0,k7_setfam_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_502,c_882]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1696,plain,
% 3.48/0.99      ( m1_subset_1(k7_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.48/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_1647,c_499]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_590,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.48/0.99      | ~ r1_tarski(X0,k1_zfmisc_1(X1)) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_648,plain,
% 3.48/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 3.48/0.99      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_590]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_650,plain,
% 3.48/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top
% 3.48/0.99      | r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_649,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_652,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3633,plain,
% 3.48/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 3.48/0.99      inference(global_propositional_subsumption,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_1696,c_650,c_652]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3645,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(X1,k1_xboole_0),X0) = iProver_top
% 3.48/0.99      | r1_tarski(k1_xboole_0,k7_setfam_1(X1,X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3633,c_495]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7642,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(X1,k1_xboole_0),X0) = iProver_top ),
% 3.48/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3645,c_502]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7646,plain,
% 3.48/0.99      ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.48/0.99      | r1_tarski(k7_setfam_1(X1,k1_xboole_0),X0) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_497,c_7642]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_501,plain,
% 3.48/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7680,plain,
% 3.48/0.99      ( k7_setfam_1(X0,k1_xboole_0) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_7646,c_501]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7918,plain,
% 3.48/0.99      ( k7_setfam_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.48/0.99      inference(global_propositional_subsumption,[status(thm)],[c_7680,c_652]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3648,plain,
% 3.48/0.99      ( r1_tarski(k7_setfam_1(sK0,sK1),k1_xboole_0) != iProver_top
% 3.48/0.99      | r1_tarski(sK1,k7_setfam_1(sK0,k1_xboole_0)) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3633,c_766]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7925,plain,
% 3.48/0.99      ( r1_tarski(k7_setfam_1(sK0,sK1),k1_xboole_0) != iProver_top
% 3.48/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_7918,c_3648]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_17373,plain,
% 3.48/0.99      ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
% 3.48/0.99      inference(global_propositional_subsumption,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_17263,c_12,c_43,c_46,c_47,c_588,c_2716,c_7925]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_11,negated_conjecture,
% 3.48/0.99      ( k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) != k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_17378,plain,
% 3.48/0.99      ( k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_17373,c_11]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_17379,plain,
% 3.48/0.99      ( $false ),
% 3.48/0.99      inference(equality_resolution_simp,[status(thm)],[c_17378]) ).
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  ------                               Statistics
% 3.48/0.99  
% 3.48/0.99  ------ General
% 3.48/0.99  
% 3.48/0.99  abstr_ref_over_cycles:                  0
% 3.48/0.99  abstr_ref_under_cycles:                 0
% 3.48/0.99  gc_basic_clause_elim:                   0
% 3.48/0.99  forced_gc_time:                         0
% 3.48/0.99  parsing_time:                           0.009
% 3.48/0.99  unif_index_cands_time:                  0.
% 3.48/0.99  unif_index_add_time:                    0.
% 3.48/0.99  orderings_time:                         0.
% 3.48/0.99  out_proof_time:                         0.01
% 3.48/0.99  total_time:                             0.434
% 3.48/0.99  num_of_symbols:                         41
% 3.48/0.99  num_of_terms:                           9123
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing
% 3.48/0.99  
% 3.48/0.99  num_of_splits:                          0
% 3.48/0.99  num_of_split_atoms:                     0
% 3.48/0.99  num_of_reused_defs:                     0
% 3.48/0.99  num_eq_ax_congr_red:                    0
% 3.48/0.99  num_of_sem_filtered_clauses:            1
% 3.48/0.99  num_of_subtypes:                        0
% 3.48/0.99  monotx_restored_types:                  0
% 3.48/0.99  sat_num_of_epr_types:                   0
% 3.48/0.99  sat_num_of_non_cyclic_types:            0
% 3.48/0.99  sat_guarded_non_collapsed_types:        0
% 3.48/0.99  num_pure_diseq_elim:                    0
% 3.48/0.99  simp_replaced_by:                       0
% 3.48/0.99  res_preprocessed:                       61
% 3.48/0.99  prep_upred:                             0
% 3.48/0.99  prep_unflattend:                        0
% 3.48/0.99  smt_new_axioms:                         0
% 3.48/0.99  pred_elim_cands:                        2
% 3.48/0.99  pred_elim:                              0
% 3.48/0.99  pred_elim_cl:                           0
% 3.48/0.99  pred_elim_cycles:                       1
% 3.48/0.99  merged_defs:                            6
% 3.48/0.99  merged_defs_ncl:                        0
% 3.48/0.99  bin_hyper_res:                          7
% 3.48/0.99  prep_cycles:                            3
% 3.48/0.99  pred_elim_time:                         0.
% 3.48/0.99  splitting_time:                         0.
% 3.48/0.99  sem_filter_time:                        0.
% 3.48/0.99  monotx_time:                            0.001
% 3.48/0.99  subtype_inf_time:                       0.
% 3.48/0.99  
% 3.48/0.99  ------ Problem properties
% 3.48/0.99  
% 3.48/0.99  clauses:                                14
% 3.48/0.99  conjectures:                            3
% 3.48/0.99  epr:                                    3
% 3.48/0.99  horn:                                   13
% 3.48/0.99  ground:                                 3
% 3.48/0.99  unary:                                  4
% 3.48/0.99  binary:                                 7
% 3.48/0.99  lits:                                   29
% 3.48/0.99  lits_eq:                                7
% 3.48/0.99  fd_pure:                                0
% 3.48/0.99  fd_pseudo:                              0
% 3.48/0.99  fd_cond:                                2
% 3.48/0.99  fd_pseudo_cond:                         0
% 3.48/0.99  ac_symbols:                             0
% 3.48/0.99  
% 3.48/0.99  ------ Propositional Solver
% 3.48/0.99  
% 3.48/0.99  prop_solver_calls:                      27
% 3.48/0.99  prop_fast_solver_calls:                 844
% 3.48/0.99  smt_solver_calls:                       0
% 3.48/0.99  smt_fast_solver_calls:                  0
% 3.48/0.99  prop_num_of_clauses:                    4980
% 3.48/0.99  prop_preprocess_simplified:             7860
% 3.48/0.99  prop_fo_subsumed:                       42
% 3.48/0.99  prop_solver_time:                       0.
% 3.48/0.99  smt_solver_time:                        0.
% 3.48/0.99  smt_fast_solver_time:                   0.
% 3.48/0.99  prop_fast_solver_time:                  0.
% 3.48/0.99  prop_unsat_core_time:                   0.
% 3.48/0.99  
% 3.48/0.99  ------ QBF
% 3.48/0.99  
% 3.48/0.99  qbf_q_res:                              0
% 3.48/0.99  qbf_num_tautologies:                    0
% 3.48/0.99  qbf_prep_cycles:                        0
% 3.48/0.99  
% 3.48/0.99  ------ BMC1
% 3.48/0.99  
% 3.48/0.99  bmc1_current_bound:                     -1
% 3.48/0.99  bmc1_last_solved_bound:                 -1
% 3.48/0.99  bmc1_unsat_core_size:                   -1
% 3.48/0.99  bmc1_unsat_core_parents_size:           -1
% 3.48/0.99  bmc1_merge_next_fun:                    0
% 3.48/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.48/0.99  
% 3.48/0.99  ------ Instantiation
% 3.48/0.99  
% 3.48/0.99  inst_num_of_clauses:                    1310
% 3.48/0.99  inst_num_in_passive:                    19
% 3.48/0.99  inst_num_in_active:                     796
% 3.48/0.99  inst_num_in_unprocessed:                496
% 3.48/0.99  inst_num_of_loops:                      870
% 3.48/0.99  inst_num_of_learning_restarts:          0
% 3.48/0.99  inst_num_moves_active_passive:          70
% 3.48/0.99  inst_lit_activity:                      0
% 3.48/0.99  inst_lit_activity_moves:                0
% 3.48/0.99  inst_num_tautologies:                   0
% 3.48/0.99  inst_num_prop_implied:                  0
% 3.48/0.99  inst_num_existing_simplified:           0
% 3.48/0.99  inst_num_eq_res_simplified:             0
% 3.48/0.99  inst_num_child_elim:                    0
% 3.48/0.99  inst_num_of_dismatching_blockings:      1359
% 3.48/0.99  inst_num_of_non_proper_insts:           2936
% 3.48/0.99  inst_num_of_duplicates:                 0
% 3.48/0.99  inst_inst_num_from_inst_to_res:         0
% 3.48/0.99  inst_dismatching_checking_time:         0.
% 3.48/0.99  
% 3.48/0.99  ------ Resolution
% 3.48/0.99  
% 3.48/0.99  res_num_of_clauses:                     0
% 3.48/0.99  res_num_in_passive:                     0
% 3.48/0.99  res_num_in_active:                      0
% 3.48/0.99  res_num_of_loops:                       64
% 3.48/0.99  res_forward_subset_subsumed:            118
% 3.48/0.99  res_backward_subset_subsumed:           8
% 3.48/0.99  res_forward_subsumed:                   0
% 3.48/0.99  res_backward_subsumed:                  0
% 3.48/0.99  res_forward_subsumption_resolution:     0
% 3.48/0.99  res_backward_subsumption_resolution:    0
% 3.48/0.99  res_clause_to_clause_subsumption:       2303
% 3.48/0.99  res_orphan_elimination:                 0
% 3.48/0.99  res_tautology_del:                      279
% 3.48/0.99  res_num_eq_res_simplified:              0
% 3.48/0.99  res_num_sel_changes:                    0
% 3.48/0.99  res_moves_from_active_to_pass:          0
% 3.48/0.99  
% 3.48/0.99  ------ Superposition
% 3.48/0.99  
% 3.48/0.99  sup_time_total:                         0.
% 3.48/0.99  sup_time_generating:                    0.
% 3.48/0.99  sup_time_sim_full:                      0.
% 3.48/0.99  sup_time_sim_immed:                     0.
% 3.48/0.99  
% 3.48/0.99  sup_num_of_clauses:                     313
% 3.48/0.99  sup_num_in_active:                      157
% 3.48/0.99  sup_num_in_passive:                     156
% 3.48/0.99  sup_num_of_loops:                       172
% 3.48/0.99  sup_fw_superposition:                   507
% 3.48/0.99  sup_bw_superposition:                   179
% 3.48/0.99  sup_immediate_simplified:               247
% 3.48/0.99  sup_given_eliminated:                   0
% 3.48/0.99  comparisons_done:                       0
% 3.48/0.99  comparisons_avoided:                    22
% 3.48/0.99  
% 3.48/0.99  ------ Simplifications
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  sim_fw_subset_subsumed:                 45
% 3.48/0.99  sim_bw_subset_subsumed:                 3
% 3.48/0.99  sim_fw_subsumed:                        97
% 3.48/0.99  sim_bw_subsumed:                        0
% 3.48/0.99  sim_fw_subsumption_res:                 2
% 3.48/0.99  sim_bw_subsumption_res:                 0
% 3.48/0.99  sim_tautology_del:                      77
% 3.48/0.99  sim_eq_tautology_del:                   32
% 3.48/0.99  sim_eq_res_simp:                        0
% 3.48/0.99  sim_fw_demodulated:                     66
% 3.48/0.99  sim_bw_demodulated:                     12
% 3.48/0.99  sim_light_normalised:                   90
% 3.48/0.99  sim_joinable_taut:                      0
% 3.48/0.99  sim_joinable_simp:                      0
% 3.48/0.99  sim_ac_normalised:                      0
% 3.48/0.99  sim_smt_subsumption:                    0
% 3.48/0.99  
%------------------------------------------------------------------------------
