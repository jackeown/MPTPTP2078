%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:11 EST 2020

% Result     : Theorem 44.08s
% Output     : CNFRefutation 44.08s
% Verified   : 
% Statistics : Number of formulae       :  490 (7088784 expanded)
%              Number of clauses        :  441 (1969570 expanded)
%              Number of leaves         :   16 (2024581 expanded)
%              Depth                    :   59
%              Number of atoms          :  537 (8991904 expanded)
%              Number of equality atoms :  497 (7028787 expanded)
%              Maximal formula depth    :    7 (   1 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f31,f32])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f27,f31,f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f39,f31])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f50,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    k3_subset_1(sK0,k1_xboole_0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f43,f44])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_206,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_211,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1826,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_206,c_211])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_210,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2097,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1826,c_210])).

cnf(c_13,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2437,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2097,c_13])).

cnf(c_2441,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2437,c_211])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_209,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1236,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_206,c_209])).

cnf(c_2091,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1826,c_1236])).

cnf(c_2451,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2441,c_2091])).

cnf(c_4,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_424,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_213,plain,
    ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_3,c_4])).

cnf(c_563,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_424,c_213])).

cnf(c_682,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_563,c_4])).

cnf(c_688,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_682,c_4])).

cnf(c_907,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(superposition,[status(thm)],[c_688,c_213])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_422,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_501,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_422,c_4])).

cnf(c_562,plain,
    ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_501,c_213])).

cnf(c_908,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_907,c_562])).

cnf(c_2464,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_2451,c_908])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k4_xboole_0(X2,X0)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_208,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_215,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_208,c_4])).

cnf(c_1112,plain,
    ( k3_tarski(k1_enumset1(k3_subset_1(X0,X1),k3_subset_1(X0,X1),X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_210,c_215])).

cnf(c_1743,plain,
    ( k3_tarski(k1_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),X0)) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_206,c_1112])).

cnf(c_2100,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1743,c_1826])).

cnf(c_2106,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_206,c_2100])).

cnf(c_2237,plain,
    ( k4_xboole_0(X0,k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_2106,c_213])).

cnf(c_5,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_493,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_210])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1225,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_14])).

cnf(c_1114,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,X0)) = k4_subset_1(sK0,sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_206,c_215])).

cnf(c_1404,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k4_subset_1(sK0,sK1,sK0) ),
    inference(superposition,[status(thm)],[c_1225,c_1114])).

cnf(c_1497,plain,
    ( k4_xboole_0(X0,k4_subset_1(sK0,sK1,sK0)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1404,c_562])).

cnf(c_2235,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_2106,c_501])).

cnf(c_2240,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_subset_1(sK0,sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_2235,c_688,c_1404])).

cnf(c_2244,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK1) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_2237,c_1497,c_2240])).

cnf(c_2466,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_2464,c_2244])).

cnf(c_561,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_422,c_213])).

cnf(c_569,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_561,c_4,c_213])).

cnf(c_1827,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1225,c_211])).

cnf(c_207,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1235,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_207,c_209])).

cnf(c_1238,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1235,c_5])).

cnf(c_1828,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1827,c_1238])).

cnf(c_46758,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1828,c_908])).

cnf(c_47508,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_46758,c_1828])).

cnf(c_1231,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_215])).

cnf(c_3434,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_206,c_1231])).

cnf(c_3770,plain,
    ( k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_3434,c_213])).

cnf(c_669,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(superposition,[status(thm)],[c_569,c_0])).

cnf(c_3869,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1))) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(superposition,[status(thm)],[c_3770,c_669])).

cnf(c_46831,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X0))) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k1_xboole_0,sK1),X0)) ),
    inference(superposition,[status(thm)],[c_1828,c_3869])).

cnf(c_4284,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_2451,c_2244])).

cnf(c_4334,plain,
    ( k4_xboole_0(k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4284,c_1828])).

cnf(c_47376,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X0))) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_46831,c_4334])).

cnf(c_47518,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X0))) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_47508,c_47376])).

cnf(c_1825,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_207,c_211])).

cnf(c_1829,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1825,c_5])).

cnf(c_1043,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_908,c_1])).

cnf(c_1859,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1829,c_1043])).

cnf(c_1860,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1859,c_1829])).

cnf(c_1861,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1860,c_1,c_1828])).

cnf(c_47580,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X0))) = k4_subset_1(sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_47518,c_4,c_1861])).

cnf(c_53776,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_subset_1(sK0,sK0,sK1))) = k4_subset_1(sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_47580,c_4])).

cnf(c_54160,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,X1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_53776,c_213])).

cnf(c_54200,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,X1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_54160,c_3770])).

cnf(c_54368,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK0,X2))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_54200,c_908])).

cnf(c_3374,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK1,sK0)),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_subset_1(sK0,sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1497,c_908])).

cnf(c_3376,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_subset_1(sK0,sK1,sK0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(superposition,[status(thm)],[c_1497,c_569])).

cnf(c_3400,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(demodulation,[status(thm)],[c_3374,c_1497,c_3376])).

cnf(c_54641,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK0,X2))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(light_normalisation,[status(thm)],[c_54368,c_3400,c_3770])).

cnf(c_56503,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) ),
    inference(superposition,[status(thm)],[c_54641,c_908])).

cnf(c_3870,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(superposition,[status(thm)],[c_3770,c_569])).

cnf(c_4455,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3870,c_908])).

cnf(c_4481,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_4455,c_3870])).

cnf(c_4482,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_4481,c_3770])).

cnf(c_56774,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_56503,c_3770,c_4482])).

cnf(c_2849,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X1),X2)) ),
    inference(superposition,[status(thm)],[c_908,c_669])).

cnf(c_685,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))),X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(superposition,[status(thm)],[c_563,c_213])).

cnf(c_686,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_685,c_562])).

cnf(c_687,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_686,c_563])).

cnf(c_865,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_569,c_687])).

cnf(c_1030,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X3) = k4_xboole_0(k4_xboole_0(X0,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
    inference(superposition,[status(thm)],[c_865,c_908])).

cnf(c_906,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(superposition,[status(thm)],[c_688,c_562])).

cnf(c_909,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_906,c_562])).

cnf(c_1063,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
    inference(demodulation,[status(thm)],[c_1030,c_909])).

cnf(c_2859,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X0,X2)),X1)) = k5_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X1),X2)) ),
    inference(demodulation,[status(thm)],[c_2849,c_4,c_1063])).

cnf(c_60462,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X1,k4_xboole_0(sK0,X2))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK0),sK1),k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X3,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X1,k4_xboole_0(sK0,X2)))) ),
    inference(superposition,[status(thm)],[c_56774,c_2859])).

cnf(c_681,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_569,c_563])).

cnf(c_2832,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X1),X3),X2)) ),
    inference(superposition,[status(thm)],[c_681,c_669])).

cnf(c_665,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_569,c_4])).

cnf(c_1019,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X1) ),
    inference(superposition,[status(thm)],[c_687,c_908])).

cnf(c_1048,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X1),X2) ),
    inference(superposition,[status(thm)],[c_908,c_569])).

cnf(c_1073,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X1),X2) ),
    inference(demodulation,[status(thm)],[c_1019,c_1048])).

cnf(c_2782,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X0),X3))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X3)) ),
    inference(superposition,[status(thm)],[c_865,c_665])).

cnf(c_764,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)) ),
    inference(superposition,[status(thm)],[c_681,c_4])).

cnf(c_784,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_764,c_4])).

cnf(c_2786,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X3)) ),
    inference(demodulation,[status(thm)],[c_2782,c_784])).

cnf(c_2870,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k3_tarski(k1_enumset1(X3,X3,k4_xboole_0(k4_xboole_0(X0,X2),X1))) ),
    inference(demodulation,[status(thm)],[c_2832,c_4,c_665,c_1073,c_2786])).

cnf(c_13875,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X1,X2),X3)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X3),X2)),X4) ),
    inference(superposition,[status(thm)],[c_2870,c_562])).

cnf(c_13882,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X4) = k4_xboole_0(k4_xboole_0(X0,X4),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
    inference(demodulation,[status(thm)],[c_13875,c_4,c_562])).

cnf(c_14748,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)),X2)),X3) = k4_xboole_0(k4_xboole_0(X0,X3),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_3770,c_13882])).

cnf(c_15184,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),sK0),sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),X3)),X1) ),
    inference(demodulation,[status(thm)],[c_14748,c_3770])).

cnf(c_56599,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_54641,c_15184])).

cnf(c_56605,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(light_normalisation,[status(thm)],[c_56599,c_3400,c_3770])).

cnf(c_8936,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),sK1) ),
    inference(superposition,[status(thm)],[c_4482,c_681])).

cnf(c_1029,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X3),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X1),X3)),X1) ),
    inference(superposition,[status(thm)],[c_681,c_908])).

cnf(c_1064,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X2) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X3)),X2) ),
    inference(demodulation,[status(thm)],[c_1029,c_908])).

cnf(c_1021,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X1),X3),X1) ),
    inference(superposition,[status(thm)],[c_865,c_908])).

cnf(c_1071,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X2),X1) ),
    inference(demodulation,[status(thm)],[c_1021,c_1048])).

cnf(c_4431,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK0),sK1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2451,c_3870])).

cnf(c_4299,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_2244,c_687])).

cnf(c_4320,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_4299,c_2244])).

cnf(c_4499,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK0),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4431,c_1828,c_3770,c_4320,c_4334])).

cnf(c_3860,plain,
    ( k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1)) = k5_xboole_0(X0,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),X0)) ),
    inference(superposition,[status(thm)],[c_3770,c_0])).

cnf(c_4888,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4499,c_3860])).

cnf(c_4908,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)) = k4_subset_1(sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4888,c_4,c_1861])).

cnf(c_5009,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k4_subset_1(sK0,sK0,sK1))) = k4_subset_1(sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4,c_4908])).

cnf(c_5012,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_5009,c_213])).

cnf(c_5013,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_5012,c_3770])).

cnf(c_5149,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_5013,c_908])).

cnf(c_5172,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(light_normalisation,[status(thm)],[c_5149,c_3400,c_3770])).

cnf(c_5390,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_5172,c_908])).

cnf(c_5416,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_5390,c_3770,c_4482])).

cnf(c_8545,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5416,c_3770])).

cnf(c_8754,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),sK1),sK0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),sK0) ),
    inference(superposition,[status(thm)],[c_8545,c_681])).

cnf(c_3863,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),X1) ),
    inference(superposition,[status(thm)],[c_3770,c_865])).

cnf(c_3902,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(demodulation,[status(thm)],[c_3863,c_3770,c_3870])).

cnf(c_8514,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_5416,c_3902])).

cnf(c_8523,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_5416,c_563])).

cnf(c_8571,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_8523,c_5416])).

cnf(c_8580,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_8514,c_8545,c_8571])).

cnf(c_4446,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3870,c_681])).

cnf(c_4457,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
    inference(superposition,[status(thm)],[c_3870,c_569])).

cnf(c_4484,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
    inference(demodulation,[status(thm)],[c_4446,c_4457])).

cnf(c_5400,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(superposition,[status(thm)],[c_5172,c_3770])).

cnf(c_5806,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),sK0),X2),sK1) ),
    inference(superposition,[status(thm)],[c_5400,c_681])).

cnf(c_5814,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),sK0),X2),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
    inference(superposition,[status(thm)],[c_5400,c_569])).

cnf(c_5838,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
    inference(demodulation,[status(thm)],[c_5806,c_5814])).

cnf(c_6853,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),sK0),sK1),X1) ),
    inference(superposition,[status(thm)],[c_569,c_3902])).

cnf(c_8581,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),sK0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_8580,c_4484,c_5838,c_6853])).

cnf(c_8799,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),sK1),sK0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_8754,c_8581])).

cnf(c_2773,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)) ),
    inference(superposition,[status(thm)],[c_908,c_665])).

cnf(c_2791,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_2773,c_4])).

cnf(c_3616,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X3) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X3,X3,k4_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_2791,c_562])).

cnf(c_3623,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X3) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_3616,c_562])).

cnf(c_8800,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),sK1),sK0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_8799,c_3623])).

cnf(c_8990,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_8936,c_1063,c_1064,c_1071,c_8800])).

cnf(c_16774,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) ),
    inference(superposition,[status(thm)],[c_15184,c_3870])).

cnf(c_16857,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_16774,c_3770,c_4482])).

cnf(c_56606,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(sK0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(demodulation,[status(thm)],[c_56605,c_4482,c_8990,c_16857])).

cnf(c_60510,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_60462,c_3770,c_56606])).

cnf(c_60511,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_60510,c_3770,c_3870])).

cnf(c_82133,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),X2),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_569,c_60511])).

cnf(c_60371,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) ),
    inference(superposition,[status(thm)],[c_56774,c_681])).

cnf(c_56585,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK0,X2))),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(superposition,[status(thm)],[c_54641,c_3770])).

cnf(c_57579,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) ),
    inference(superposition,[status(thm)],[c_56585,c_16857])).

cnf(c_57617,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_57579,c_4482])).

cnf(c_60658,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_60371,c_3770,c_57617])).

cnf(c_63373,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)),k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_3770,c_60658])).

cnf(c_64189,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_63373,c_3400])).

cnf(c_64190,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(demodulation,[status(thm)],[c_64189,c_3400,c_3770])).

cnf(c_60407,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3))),k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_56774,c_669])).

cnf(c_60604,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3))),k4_xboole_0(k4_xboole_0(X0,sK0),sK1))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_60407,c_3770])).

cnf(c_82735,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2))),k4_xboole_0(sK0,X3))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X4,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2))),k4_xboole_0(sK0,X3))),k4_xboole_0(k4_xboole_0(X4,sK0),sK1))) ),
    inference(superposition,[status(thm)],[c_64190,c_60604])).

cnf(c_63410,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),k4_subset_1(sK0,sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_54200,c_60658])).

cnf(c_64116,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),k4_subset_1(sK0,sK0,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_63410,c_3400])).

cnf(c_56596,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X3)) ),
    inference(superposition,[status(thm)],[c_54641,c_13882])).

cnf(c_56610,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X3)) ),
    inference(light_normalisation,[status(thm)],[c_56596,c_3770])).

cnf(c_3846,plain,
    ( k3_tarski(k1_enumset1(k4_subset_1(sK0,sK0,sK1),k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1))) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(superposition,[status(thm)],[c_3770,c_665])).

cnf(c_567,plain,
    ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) = k5_xboole_0(X2,k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_213,c_0])).

cnf(c_6344,plain,
    ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) = k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_422,c_567])).

cnf(c_6384,plain,
    ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) = k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(X1,X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_6344,c_4])).

cnf(c_13148,plain,
    ( k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)),k4_xboole_0(k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_subset_1(sK0,sK0,sK1))))) ),
    inference(superposition,[status(thm)],[c_3846,c_6384])).

cnf(c_13194,plain,
    ( k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_subset_1(sK0,sK0,sK1))))) ),
    inference(demodulation,[status(thm)],[c_13148,c_3770])).

cnf(c_27540,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK0),sK1),k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X3),k3_tarski(k1_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_subset_1(sK0,sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_13194,c_213])).

cnf(c_975,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X3) = k4_xboole_0(k4_xboole_0(X0,X3),k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(superposition,[status(thm)],[c_213,c_865])).

cnf(c_976,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X3),X1) ),
    inference(superposition,[status(thm)],[c_569,c_865])).

cnf(c_1006,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_tarski(k1_enumset1(X2,X2,X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X1),X2) ),
    inference(demodulation,[status(thm)],[c_975,c_976])).

cnf(c_27555,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK0),sK1),k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X3),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_27540,c_1006,c_3770])).

cnf(c_58891,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),sK0),sK1),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,sK0),sK1),k4_xboole_0(X1,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X4),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),X3)) ),
    inference(superposition,[status(thm)],[c_56610,c_27555])).

cnf(c_58940,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(sK0,X2)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,sK0),sK1),k4_xboole_0(X1,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X4),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),X3)) ),
    inference(demodulation,[status(thm)],[c_58891,c_8990])).

cnf(c_46768,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_1828,c_13882])).

cnf(c_47471,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_46768,c_1829])).

cnf(c_47472,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X2),X3)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_47471,c_909])).

cnf(c_47473,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_47472,c_1828])).

cnf(c_46896,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k1_xboole_0,sK1),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_1828,c_4482])).

cnf(c_47279,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(sK0,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k1_xboole_0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_46896,c_4334])).

cnf(c_47478,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(sK0,X1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_47473,c_47279])).

cnf(c_58941,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK0,X3)),X4)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,X4)) ),
    inference(demodulation,[status(thm)],[c_58940,c_27555,c_47478])).

cnf(c_64117,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(demodulation,[status(thm)],[c_64116,c_3400,c_3770,c_56610,c_58941])).

cnf(c_68727,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2))),k4_xboole_0(sK0,X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(superposition,[status(thm)],[c_569,c_64117])).

cnf(c_82764,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,sK0),sK1))) ),
    inference(light_normalisation,[status(thm)],[c_82735,c_68727])).

cnf(c_6881,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_3902,c_908])).

cnf(c_6893,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
    inference(superposition,[status(thm)],[c_3902,c_569])).

cnf(c_6920,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
    inference(demodulation,[status(thm)],[c_6881,c_6893])).

cnf(c_5803,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),sK0),X2),sK1) ),
    inference(superposition,[status(thm)],[c_5400,c_908])).

cnf(c_5841,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
    inference(demodulation,[status(thm)],[c_5803,c_5814])).

cnf(c_6921,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,sK0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
    inference(demodulation,[status(thm)],[c_6920,c_3770,c_5841])).

cnf(c_7450,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,X3),sK0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,sK0),X3)) ),
    inference(superposition,[status(thm)],[c_681,c_6921])).

cnf(c_7530,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,sK0),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_7450,c_6921])).

cnf(c_13845,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = k3_tarski(k1_enumset1(X3,X3,k4_xboole_0(k4_xboole_0(X0,X2),X1))) ),
    inference(superposition,[status(thm)],[c_2870,c_4])).

cnf(c_2834,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X3),k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_908,c_669])).

cnf(c_2868,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k3_tarski(k1_enumset1(X3,X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(demodulation,[status(thm)],[c_2834,c_4,c_665,c_1048])).

cnf(c_25552,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X3,X4),X5))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X5),X4),k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_13845,c_2868])).

cnf(c_25357,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2)) = k3_tarski(k1_enumset1(X2,X2,k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),X1))) ),
    inference(superposition,[status(thm)],[c_3770,c_13845])).

cnf(c_25747,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2)) = k3_tarski(k1_enumset1(X2,X2,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1))) ),
    inference(light_normalisation,[status(thm)],[c_25357,c_3770])).

cnf(c_26633,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1))) ),
    inference(superposition,[status(thm)],[c_25747,c_2868])).

cnf(c_82274,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X4)))) ),
    inference(superposition,[status(thm)],[c_60511,c_60511])).

cnf(c_82275,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = sP0_iProver_split(X0,X1,X2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_82274])).

cnf(c_82277,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) = sP0_iProver_split(X2,X0,X1) ),
    inference(demodulation,[status(thm)],[c_82275,c_60511])).

cnf(c_82765,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2),k4_xboole_0(X0,sK1))) = sP0_iProver_split(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_82764,c_4482,c_7530,c_25552,c_26633,c_82277])).

cnf(c_14660,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)),sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,sK0),sK1)),X1) ),
    inference(superposition,[status(thm)],[c_5013,c_13882])).

cnf(c_15274,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,sK1),sK0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,sK0),sK1)),X1) ),
    inference(demodulation,[status(thm)],[c_14660,c_865,c_3770])).

cnf(c_15914,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(X2,sK1),sK0)),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,sK0),sK1)),sK0),sK1),X1) ),
    inference(superposition,[status(thm)],[c_15274,c_5400])).

cnf(c_5783,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,sK1)),sK0),sK1),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,sK1)),X1),sK0),sK1) ),
    inference(superposition,[status(thm)],[c_865,c_5400])).

cnf(c_5863,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,sK1)),X1),sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_5783,c_5400])).

cnf(c_5361,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,sK1)),sK0),sK1),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,sK1)),X1),k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_865,c_5172])).

cnf(c_5392,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
    inference(superposition,[status(thm)],[c_5172,c_569])).

cnf(c_5442,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X2),X1) ),
    inference(demodulation,[status(thm)],[c_5361,c_5392,c_5400])).

cnf(c_5864,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),X2),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_5863,c_5442])).

cnf(c_15984,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK0)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X2),k4_xboole_0(X1,sK1)) ),
    inference(demodulation,[status(thm)],[c_15914,c_909,c_5400,c_5864])).

cnf(c_3857,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3770,c_563])).

cnf(c_3903,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_3857,c_3770,c_3870])).

cnf(c_4730,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK0),sK1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_3903,c_908])).

cnf(c_4741,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK0),sK1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(light_normalisation,[status(thm)],[c_4730,c_3400,c_3770])).

cnf(c_7135,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(superposition,[status(thm)],[c_4741,c_5172])).

cnf(c_15985,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_15984,c_7135])).

cnf(c_82766,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),X2)) = sP0_iProver_split(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_82765,c_15985])).

cnf(c_82192,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK0),k4_xboole_0(X1,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,sK1),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1828,c_60511])).

cnf(c_46906,plain,
    ( k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1828,c_3770])).

cnf(c_48936,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),X0),sK1) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_46906,c_569])).

cnf(c_49373,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),X0),sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_48936,c_47508])).

cnf(c_41406,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X2),k4_subset_1(sK0,sK0,sK1)),X1)) ),
    inference(superposition,[status(thm)],[c_3903,c_2859])).

cnf(c_3856,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3770,c_681])).

cnf(c_3904,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(demodulation,[status(thm)],[c_3856,c_3870])).

cnf(c_7095,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,sK1))) ),
    inference(superposition,[status(thm)],[c_5400,c_4741])).

cnf(c_3617,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[status(thm)],[c_2791,c_213])).

cnf(c_3622,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
    inference(demodulation,[status(thm)],[c_3617,c_562])).

cnf(c_5369,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK1),X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,X2),sK1)) ),
    inference(superposition,[status(thm)],[c_865,c_5172])).

cnf(c_4292,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),X1),sK1) ),
    inference(superposition,[status(thm)],[c_2244,c_908])).

cnf(c_4304,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),X1),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(superposition,[status(thm)],[c_2244,c_569])).

cnf(c_4326,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(demodulation,[status(thm)],[c_4292,c_4304])).

cnf(c_5435,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK1),X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_5369,c_3870,c_4326])).

cnf(c_7174,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(X1,X2)),sK1) ),
    inference(demodulation,[status(thm)],[c_7095,c_3622,c_5435])).

cnf(c_41958,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),k4_xboole_0(X0,X1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X2),X1)) ),
    inference(demodulation,[status(thm)],[c_41406,c_665,c_3770,c_3904,c_7174])).

cnf(c_49068,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),k4_xboole_0(X0,X1)),sK1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)),X1)) ),
    inference(superposition,[status(thm)],[c_46906,c_41958])).

cnf(c_41665,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X2)),X1)) = k5_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2)) ),
    inference(superposition,[status(thm)],[c_3770,c_2859])).

cnf(c_44509,plain,
    ( k5_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)),X1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)),k4_subset_1(sK0,sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_3903,c_41665])).

cnf(c_44948,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),k4_xboole_0(X0,X1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK0),sK1),X1)) ),
    inference(demodulation,[status(thm)],[c_44509,c_665,c_3770,c_4484,c_7174])).

cnf(c_4439,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3870,c_3870])).

cnf(c_4493,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK0),sK1),sK1),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_4439,c_4457])).

cnf(c_4494,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK0),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),X1) ),
    inference(demodulation,[status(thm)],[c_4493,c_976,c_1071])).

cnf(c_4495,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(demodulation,[status(thm)],[c_4494,c_687])).

cnf(c_5126,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK1),sK0),sK1) ),
    inference(superposition,[status(thm)],[c_865,c_5013])).

cnf(c_5151,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(superposition,[status(thm)],[c_5013,c_569])).

cnf(c_5199,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK1),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(demodulation,[status(thm)],[c_5126,c_5151])).

cnf(c_44949,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),k4_xboole_0(X0,X1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK0),sK1),X1)) ),
    inference(demodulation,[status(thm)],[c_44948,c_4495,c_5199])).

cnf(c_44950,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),k4_xboole_0(X0,X1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(demodulation,[status(thm)],[c_44949,c_563])).

cnf(c_46944,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),X1),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)),X1)) ),
    inference(superposition,[status(thm)],[c_1828,c_41665])).

cnf(c_47188,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(light_normalisation,[status(thm)],[c_46944,c_3770,c_3903])).

cnf(c_1847,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1829,c_0])).

cnf(c_13853,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(superposition,[status(thm)],[c_2870,c_1847])).

cnf(c_12025,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_2868,c_1847])).

cnf(c_1839,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1829,c_4])).

cnf(c_568,plain,
    ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X0),X1)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_213,c_1])).

cnf(c_7954,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0)) = k3_tarski(k1_enumset1(X0,X0,X0)) ),
    inference(superposition,[status(thm)],[c_424,c_568])).

cnf(c_7988,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7954,c_424,c_1828,c_1847])).

cnf(c_12062,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_12025,c_1839,c_7988])).

cnf(c_13895,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_13853,c_12062])).

cnf(c_44648,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),X1),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK0),sK1),X1)) ),
    inference(superposition,[status(thm)],[c_5013,c_41665])).

cnf(c_44675,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK0),sK1),X1)) ),
    inference(light_normalisation,[status(thm)],[c_44648,c_3770])).

cnf(c_44676,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(demodulation,[status(thm)],[c_44675,c_563,c_3770,c_3870])).

cnf(c_47189,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) ),
    inference(demodulation,[status(thm)],[c_47188,c_3870,c_13895,c_44676])).

cnf(c_47261,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) ),
    inference(demodulation,[status(thm)],[c_46906,c_47189])).

cnf(c_49155,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),k4_xboole_0(X0,X1)),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) ),
    inference(light_normalisation,[status(thm)],[c_49068,c_3903,c_44950,c_47261])).

cnf(c_49378,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) ),
    inference(demodulation,[status(thm)],[c_49373,c_49155])).

cnf(c_54263,plain,
    ( k4_xboole_0(sK1,k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_2451,c_54200])).

cnf(c_54769,plain,
    ( k4_xboole_0(sK1,k4_subset_1(sK0,sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_54263,c_1828,c_3770,c_4334])).

cnf(c_13876,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X1,X2),X3)))) = k4_xboole_0(k4_xboole_0(X0,X4),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
    inference(superposition,[status(thm)],[c_2870,c_213])).

cnf(c_13881,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X4),X3)) ),
    inference(demodulation,[status(thm)],[c_13876,c_4,c_562])).

cnf(c_14183,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_3770,c_13881])).

cnf(c_15349,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),sK0),sK1)) ),
    inference(demodulation,[status(thm)],[c_14183,c_3770])).

cnf(c_55163,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(superposition,[status(thm)],[c_54769,c_15349])).

cnf(c_55365,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(demodulation,[status(thm)],[c_55163,c_54769])).

cnf(c_18438,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_4499,c_15349])).

cnf(c_8875,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(superposition,[status(thm)],[c_4499,c_4482])).

cnf(c_9057,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_8875,c_4499])).

cnf(c_19019,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_18438,c_4499,c_9057])).

cnf(c_49035,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(superposition,[status(thm)],[c_46906,c_4482])).

cnf(c_49205,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_49035,c_46906])).

cnf(c_49206,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_49205,c_47508])).

cnf(c_55366,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_55365,c_19019,c_49206])).

cnf(c_83334,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK0),k4_xboole_0(X1,k4_xboole_0(sK0,X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) ),
    inference(light_normalisation,[status(thm)],[c_82192,c_4334,c_49378,c_55366])).

cnf(c_83335,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) = sP0_iProver_split(sK0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_83334,c_82275])).

cnf(c_82138,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(k4_xboole_0(X2,sK1),k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),X2),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,sK1)))) ),
    inference(superposition,[status(thm)],[c_908,c_60511])).

cnf(c_83483,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(k4_xboole_0(X2,sK1),k4_xboole_0(sK0,X3)))) = k5_xboole_0(sP0_iProver_split(sK0,X1,X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,sK1)))) ),
    inference(demodulation,[status(thm)],[c_82138,c_82766,c_83335])).

cnf(c_8546,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,sK1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5416,c_3870])).

cnf(c_83484,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(k4_xboole_0(X2,sK1),k4_xboole_0(sK0,X3)))) = k5_xboole_0(sP0_iProver_split(sK0,X1,X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_83483,c_8546])).

cnf(c_83485,plain,
    ( k5_xboole_0(sP0_iProver_split(sK0,X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) = sP0_iProver_split(X2,X0,k4_xboole_0(X1,sK1)) ),
    inference(demodulation,[status(thm)],[c_83484,c_82275])).

cnf(c_83503,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = sP0_iProver_split(X0,X1,k4_xboole_0(X2,sK1)) ),
    inference(demodulation,[status(thm)],[c_82133,c_82766,c_83335,c_83485])).

cnf(c_83504,plain,
    ( sP0_iProver_split(X0,X1,k4_xboole_0(X2,sK1)) = sP0_iProver_split(X0,X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_83503,c_82275])).

cnf(c_82215,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK0),sK1),X0),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,X1)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK0),sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_2451,c_60511])).

cnf(c_2465,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2451,c_569])).

cnf(c_77806,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),X1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_2465,c_569])).

cnf(c_83282,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK1),sK0)) = sP0_iProver_split(X0,sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_82215,c_865,c_77806,c_82275])).

cnf(c_41601,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1))),X1)) = k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),sK0),sK1),X1)) ),
    inference(superposition,[status(thm)],[c_3870,c_2859])).

cnf(c_41744,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,sK0),sK1)),X1)) = k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),sK0),sK1),X1)) ),
    inference(light_normalisation,[status(thm)],[c_41601,c_3770,c_3870])).

cnf(c_42880,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,sK0),sK1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_5013,c_41744])).

cnf(c_42993,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,sK0),sK1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK0),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_42880,c_3903])).

cnf(c_42994,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),X0),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(demodulation,[status(thm)],[c_42993,c_665,c_865,c_3770,c_4741])).

cnf(c_43497,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),X0),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK1),sK0)) ),
    inference(superposition,[status(thm)],[c_865,c_42994])).

cnf(c_4675,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),X0),sK1) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_4499,c_569])).

cnf(c_41453,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_subset_1(sK0,sK0,sK1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(superposition,[status(thm)],[c_5172,c_2859])).

cnf(c_41904,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_subset_1(sK0,sK0,sK1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(light_normalisation,[status(thm)],[c_41453,c_3770])).

cnf(c_8540,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1)))) = k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_5416,c_784])).

cnf(c_8556,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1)))) = k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(X2,sK0),sK1))) ),
    inference(demodulation,[status(thm)],[c_8540,c_3770])).

cnf(c_8541,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5416,c_665])).

cnf(c_8555,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(X2,sK0),sK1))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_8541,c_3770])).

cnf(c_24266,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_8556,c_8555,c_8556])).

cnf(c_24382,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_3903,c_24266])).

cnf(c_5388,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X1,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X1,sK1)) ),
    inference(superposition,[status(thm)],[c_5172,c_681])).

cnf(c_5417,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X1,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(light_normalisation,[status(thm)],[c_5388,c_3770,c_4326])).

cnf(c_6078,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3903,c_5417])).

cnf(c_6172,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_6078,c_3903])).

cnf(c_24515,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1))) ),
    inference(light_normalisation,[status(thm)],[c_24382,c_3903,c_6172])).

cnf(c_7119,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_4741,c_681])).

cnf(c_7153,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
    inference(light_normalisation,[status(thm)],[c_7119,c_3400,c_3770])).

cnf(c_7641,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) ),
    inference(superposition,[status(thm)],[c_7153,c_4])).

cnf(c_5396,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)))) = k5_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) ),
    inference(superposition,[status(thm)],[c_5172,c_665])).

cnf(c_1033,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X2,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_908,c_4])).

cnf(c_5410,plain,
    ( k5_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),X0),sK1)) = k5_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) ),
    inference(demodulation,[status(thm)],[c_5396,c_1033,c_3770])).

cnf(c_9149,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK1),X1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),k4_xboole_0(k4_xboole_0(X0,sK1),X1)),sK1)) ),
    inference(superposition,[status(thm)],[c_687,c_5410])).

cnf(c_5368,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),sK1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK1),X2)) ),
    inference(superposition,[status(thm)],[c_681,c_5172])).

cnf(c_5436,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK1),X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_5368,c_5172])).

cnf(c_9245,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_xboole_0(k4_xboole_0(X2,sK0),sK1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_9149,c_665,c_687,c_5436])).

cnf(c_7121,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,sK0),sK1))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) ),
    inference(superposition,[status(thm)],[c_4741,c_908])).

cnf(c_7152,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,sK0),sK1))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_7121,c_3770,c_4482])).

cnf(c_10338,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X2,X3)))) = k5_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X3,sK0),sK1))),X0),k4_subset_1(sK0,sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_7152,c_1033])).

cnf(c_10344,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,sK0),sK1))),X3),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_7152,c_569])).

cnf(c_10383,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X2,X3)))) = k5_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X2,X3)),X0)) ),
    inference(demodulation,[status(thm)],[c_10338,c_10344])).

cnf(c_10384,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X2,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X2,X3)),X0)) ),
    inference(light_normalisation,[status(thm)],[c_10383,c_3770])).

cnf(c_13874,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X1),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X2),X1))) ),
    inference(superposition,[status(thm)],[c_2870,c_501])).

cnf(c_24516,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X0,sK0))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) ),
    inference(demodulation,[status(thm)],[c_24515,c_3400,c_7641,c_9245,c_10384,c_13874])).

cnf(c_24517,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) ),
    inference(demodulation,[status(thm)],[c_24516,c_7135])).

cnf(c_41905,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),sK1),sK0)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(demodulation,[status(thm)],[c_41904,c_865,c_1071,c_3770,c_3870,c_24517])).

cnf(c_42360,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),sK1),X0)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK1),sK0)) ),
    inference(superposition,[status(thm)],[c_1829,c_41905])).

cnf(c_4671,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK0),sK1) = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_4499,c_687])).

cnf(c_4683,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4671,c_4499])).

cnf(c_42618,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,sK1),sK0)) ),
    inference(light_normalisation,[status(thm)],[c_42360,c_4334,c_4683])).

cnf(c_42619,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_42618,c_13895])).

cnf(c_43591,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,sK1),sK0)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_43497,c_4499,c_4675,c_42619])).

cnf(c_83283,plain,
    ( sP0_iProver_split(X0,sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_83282,c_4499,c_43591])).

cnf(c_83505,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK0),sK1) = sP0_iProver_split(X0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_83504,c_83283])).

cnf(c_82136,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(sK0,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK0))) ),
    inference(superposition,[status(thm)],[c_681,c_60511])).

cnf(c_83491,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(sK0,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(light_normalisation,[status(thm)],[c_82136,c_7135])).

cnf(c_83492,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,X0,sK0) ),
    inference(demodulation,[status(thm)],[c_83491,c_24517,c_82275])).

cnf(c_82137,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(sK1,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK1))) ),
    inference(superposition,[status(thm)],[c_865,c_60511])).

cnf(c_83486,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(sK1,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(light_normalisation,[status(thm)],[c_82137,c_4326])).

cnf(c_83487,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,X0,sK1) ),
    inference(demodulation,[status(thm)],[c_83486,c_24517,c_82275])).

cnf(c_83493,plain,
    ( sP0_iProver_split(X0,X1,sK0) = sP0_iProver_split(X0,X1,sK1) ),
    inference(demodulation,[status(thm)],[c_83492,c_83487])).

cnf(c_82213,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(superposition,[status(thm)],[c_1829,c_60511])).

cnf(c_83288,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_82213,c_1829,c_82275])).

cnf(c_82220,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X3)))) ),
    inference(superposition,[status(thm)],[c_3870,c_60511])).

cnf(c_83257,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),sK0),sK1),X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2))) ),
    inference(light_normalisation,[status(thm)],[c_82220,c_3902])).

cnf(c_83258,plain,
    ( sP0_iProver_split(X0,k4_xboole_0(X1,X2),k4_subset_1(sK0,sK0,sK1)) = sP0_iProver_split(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_83257,c_4482,c_26633,c_82275,c_82277])).

cnf(c_82225,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),sK1),X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1))) ),
    inference(superposition,[status(thm)],[c_5013,c_60511])).

cnf(c_83242,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),sK1),X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
    inference(light_normalisation,[status(thm)],[c_82225,c_3400])).

cnf(c_83243,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,k4_xboole_0(X0,sK1),k4_subset_1(sK0,sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_83242,c_3902,c_82275])).

cnf(c_83244,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,k4_xboole_0(X0,sK1),k4_subset_1(sK0,sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_83243,c_865,c_24517])).

cnf(c_83259,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,X0,sK1) ),
    inference(demodulation,[status(thm)],[c_83258,c_83244])).

cnf(c_83291,plain,
    ( sP0_iProver_split(X0,X1,k1_xboole_0) = sP0_iProver_split(X0,X1,sK1) ),
    inference(demodulation,[status(thm)],[c_83288,c_83259])).

cnf(c_83494,plain,
    ( sP0_iProver_split(X0,X1,sK0) = sP0_iProver_split(X0,X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_83493,c_83291])).

cnf(c_83507,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK0),sK1) = sP0_iProver_split(X0,sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_83505,c_83494])).

cnf(c_83698,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1)) = sP0_iProver_split(X0,sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2466,c_2466,c_83507])).

cnf(c_83858,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(sK0,sP0_iProver_split(X0,sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_83698,c_665])).

cnf(c_83885,plain,
    ( sP0_iProver_split(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK0) ),
    inference(superposition,[status(thm)],[c_83698,c_687])).

cnf(c_83886,plain,
    ( sP0_iProver_split(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_83698,c_681])).

cnf(c_84127,plain,
    ( sP0_iProver_split(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK0,k1_xboole_0) = sP0_iProver_split(X0,sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_83886,c_83698])).

cnf(c_84129,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK0) = sP0_iProver_split(X0,sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_83885,c_84127])).

cnf(c_46622,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X1),X2)) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) ),
    inference(superposition,[status(thm)],[c_1828,c_2859])).

cnf(c_46712,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1828,c_569])).

cnf(c_47658,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_46712,c_47508])).

cnf(c_46662,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1828,c_1033])).

cnf(c_46815,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),X1)) = k3_tarski(k1_enumset1(X1,X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,sK1),X0))) ),
    inference(superposition,[status(thm)],[c_1828,c_25747])).

cnf(c_47401,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),X1)) = k3_tarski(k1_enumset1(X1,X1,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_46815,c_4334])).

cnf(c_47516,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),X1)) = k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_47508,c_47401])).

cnf(c_46855,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X0),X1))) = k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1828,c_2791])).

cnf(c_14808,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4)))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X2,X4),X3))) ),
    inference(superposition,[status(thm)],[c_13882,c_4])).

cnf(c_47015,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X0),X2)))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1828,c_14808])).

cnf(c_47062,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X0),X2)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_47015,c_1861])).

cnf(c_3601,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3),X2))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3))) ),
    inference(superposition,[status(thm)],[c_687,c_2791])).

cnf(c_3602,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3),X2))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X0)))) ),
    inference(superposition,[status(thm)],[c_681,c_2791])).

cnf(c_3633,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3),X2))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X3),X2))) ),
    inference(demodulation,[status(thm)],[c_3602,c_2791])).

cnf(c_3634,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X3),X2))) ),
    inference(demodulation,[status(thm)],[c_3601,c_3633])).

cnf(c_14414,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X0),X4)))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4)))) ),
    inference(superposition,[status(thm)],[c_13881,c_2791])).

cnf(c_47063,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_47062,c_908,c_3634,c_14414])).

cnf(c_47345,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_46855,c_47063])).

cnf(c_47582,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_47516,c_47345])).

cnf(c_47671,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,sK1),k4_xboole_0(k1_xboole_0,sK1),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_47658,c_47582])).

cnf(c_46722,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),X2)) = k3_tarski(k1_enumset1(X2,X2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1828,c_13845])).

cnf(c_47646,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),X2)) = X2 ),
    inference(demodulation,[status(thm)],[c_46722,c_47345])).

cnf(c_47647,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,X0),X1),k4_xboole_0(k4_xboole_0(X0,X0),X1),X2)) = X2 ),
    inference(demodulation,[status(thm)],[c_47646,c_909])).

cnf(c_47648,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0),X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_47647,c_1828])).

cnf(c_47680,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_47671,c_47508,c_47648])).

cnf(c_47741,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_46662,c_1828,c_47680])).

cnf(c_47742,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_47741,c_563])).

cnf(c_47776,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_46622,c_47508,c_47658,c_47742])).

cnf(c_47777,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_47776,c_1861])).

cnf(c_84130,plain,
    ( sP0_iProver_split(X0,sK0,k1_xboole_0) = k4_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_84129,c_47777])).

cnf(c_84957,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(sK0,k4_xboole_0(X0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_83858,c_84130])).

cnf(c_84958,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) = k3_tarski(k1_enumset1(sK0,sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_84957,c_4])).

cnf(c_87575,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_2451,c_84958])).

cnf(c_87638,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK0)) = k4_subset_1(sK0,sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_87575,c_3434])).

cnf(c_87639,plain,
    ( k4_subset_1(sK0,sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_87638,c_424])).

cnf(c_1493,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k4_subset_1(sK0,sK1,sK0) ),
    inference(superposition,[status(thm)],[c_501,c_1404])).

cnf(c_3768,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k4_subset_1(sK0,sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_3434,c_1493])).

cnf(c_1401,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,X0))) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_210,c_1114])).

cnf(c_1585,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_206,c_1401])).

cnf(c_2090,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_1826,c_1585])).

cnf(c_2093,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_2090,c_688,c_1404])).

cnf(c_11,negated_conjecture,
    ( k3_subset_1(sK0,k1_xboole_0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_212,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != sK0 ),
    inference(demodulation,[status(thm)],[c_11,c_5])).

cnf(c_2092,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) != sK0 ),
    inference(demodulation,[status(thm)],[c_1826,c_212])).

cnf(c_2094,plain,
    ( k4_subset_1(sK0,sK1,sK0) != sK0 ),
    inference(demodulation,[status(thm)],[c_2093,c_2092])).

cnf(c_3778,plain,
    ( k4_subset_1(sK0,sK0,sK1) != sK0 ),
    inference(demodulation,[status(thm)],[c_3768,c_2094])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_87639,c_3778])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 44.08/5.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.08/5.99  
% 44.08/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 44.08/5.99  
% 44.08/5.99  ------  iProver source info
% 44.08/5.99  
% 44.08/5.99  git: date: 2020-06-30 10:37:57 +0100
% 44.08/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 44.08/5.99  git: non_committed_changes: false
% 44.08/5.99  git: last_make_outside_of_git: false
% 44.08/5.99  
% 44.08/5.99  ------ 
% 44.08/5.99  
% 44.08/5.99  ------ Input Options
% 44.08/5.99  
% 44.08/5.99  --out_options                           all
% 44.08/5.99  --tptp_safe_out                         true
% 44.08/5.99  --problem_path                          ""
% 44.08/5.99  --include_path                          ""
% 44.08/5.99  --clausifier                            res/vclausify_rel
% 44.08/5.99  --clausifier_options                    ""
% 44.08/5.99  --stdin                                 false
% 44.08/5.99  --stats_out                             all
% 44.08/5.99  
% 44.08/5.99  ------ General Options
% 44.08/5.99  
% 44.08/5.99  --fof                                   false
% 44.08/5.99  --time_out_real                         305.
% 44.08/5.99  --time_out_virtual                      -1.
% 44.08/5.99  --symbol_type_check                     false
% 44.08/5.99  --clausify_out                          false
% 44.08/5.99  --sig_cnt_out                           false
% 44.08/5.99  --trig_cnt_out                          false
% 44.08/5.99  --trig_cnt_out_tolerance                1.
% 44.08/5.99  --trig_cnt_out_sk_spl                   false
% 44.08/5.99  --abstr_cl_out                          false
% 44.08/5.99  
% 44.08/5.99  ------ Global Options
% 44.08/5.99  
% 44.08/5.99  --schedule                              default
% 44.08/5.99  --add_important_lit                     false
% 44.08/5.99  --prop_solver_per_cl                    1000
% 44.08/5.99  --min_unsat_core                        false
% 44.08/5.99  --soft_assumptions                      false
% 44.08/5.99  --soft_lemma_size                       3
% 44.08/5.99  --prop_impl_unit_size                   0
% 44.08/5.99  --prop_impl_unit                        []
% 44.08/5.99  --share_sel_clauses                     true
% 44.08/5.99  --reset_solvers                         false
% 44.08/5.99  --bc_imp_inh                            [conj_cone]
% 44.08/5.99  --conj_cone_tolerance                   3.
% 44.08/5.99  --extra_neg_conj                        none
% 44.08/5.99  --large_theory_mode                     true
% 44.08/5.99  --prolific_symb_bound                   200
% 44.08/5.99  --lt_threshold                          2000
% 44.08/5.99  --clause_weak_htbl                      true
% 44.08/5.99  --gc_record_bc_elim                     false
% 44.08/5.99  
% 44.08/5.99  ------ Preprocessing Options
% 44.08/5.99  
% 44.08/5.99  --preprocessing_flag                    true
% 44.08/5.99  --time_out_prep_mult                    0.1
% 44.08/5.99  --splitting_mode                        input
% 44.08/5.99  --splitting_grd                         true
% 44.08/5.99  --splitting_cvd                         false
% 44.08/5.99  --splitting_cvd_svl                     false
% 44.08/5.99  --splitting_nvd                         32
% 44.08/5.99  --sub_typing                            true
% 44.08/5.99  --prep_gs_sim                           true
% 44.08/5.99  --prep_unflatten                        true
% 44.08/5.99  --prep_res_sim                          true
% 44.08/5.99  --prep_upred                            true
% 44.08/5.99  --prep_sem_filter                       exhaustive
% 44.08/5.99  --prep_sem_filter_out                   false
% 44.08/5.99  --pred_elim                             true
% 44.08/5.99  --res_sim_input                         true
% 44.08/5.99  --eq_ax_congr_red                       true
% 44.08/5.99  --pure_diseq_elim                       true
% 44.08/5.99  --brand_transform                       false
% 44.08/5.99  --non_eq_to_eq                          false
% 44.08/5.99  --prep_def_merge                        true
% 44.08/5.99  --prep_def_merge_prop_impl              false
% 44.08/5.99  --prep_def_merge_mbd                    true
% 44.08/5.99  --prep_def_merge_tr_red                 false
% 44.08/5.99  --prep_def_merge_tr_cl                  false
% 44.08/5.99  --smt_preprocessing                     true
% 44.08/5.99  --smt_ac_axioms                         fast
% 44.08/5.99  --preprocessed_out                      false
% 44.08/5.99  --preprocessed_stats                    false
% 44.08/5.99  
% 44.08/5.99  ------ Abstraction refinement Options
% 44.08/5.99  
% 44.08/5.99  --abstr_ref                             []
% 44.08/5.99  --abstr_ref_prep                        false
% 44.08/5.99  --abstr_ref_until_sat                   false
% 44.08/5.99  --abstr_ref_sig_restrict                funpre
% 44.08/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 44.08/5.99  --abstr_ref_under                       []
% 44.08/5.99  
% 44.08/5.99  ------ SAT Options
% 44.08/5.99  
% 44.08/5.99  --sat_mode                              false
% 44.08/5.99  --sat_fm_restart_options                ""
% 44.08/5.99  --sat_gr_def                            false
% 44.08/5.99  --sat_epr_types                         true
% 44.08/5.99  --sat_non_cyclic_types                  false
% 44.08/5.99  --sat_finite_models                     false
% 44.08/5.99  --sat_fm_lemmas                         false
% 44.08/5.99  --sat_fm_prep                           false
% 44.08/5.99  --sat_fm_uc_incr                        true
% 44.08/5.99  --sat_out_model                         small
% 44.08/5.99  --sat_out_clauses                       false
% 44.08/5.99  
% 44.08/5.99  ------ QBF Options
% 44.08/5.99  
% 44.08/5.99  --qbf_mode                              false
% 44.08/5.99  --qbf_elim_univ                         false
% 44.08/5.99  --qbf_dom_inst                          none
% 44.08/5.99  --qbf_dom_pre_inst                      false
% 44.08/5.99  --qbf_sk_in                             false
% 44.08/5.99  --qbf_pred_elim                         true
% 44.08/5.99  --qbf_split                             512
% 44.08/5.99  
% 44.08/5.99  ------ BMC1 Options
% 44.08/5.99  
% 44.08/5.99  --bmc1_incremental                      false
% 44.08/5.99  --bmc1_axioms                           reachable_all
% 44.08/5.99  --bmc1_min_bound                        0
% 44.08/5.99  --bmc1_max_bound                        -1
% 44.08/5.99  --bmc1_max_bound_default                -1
% 44.08/5.99  --bmc1_symbol_reachability              true
% 44.08/5.99  --bmc1_property_lemmas                  false
% 44.08/5.99  --bmc1_k_induction                      false
% 44.08/5.99  --bmc1_non_equiv_states                 false
% 44.08/5.99  --bmc1_deadlock                         false
% 44.08/5.99  --bmc1_ucm                              false
% 44.08/5.99  --bmc1_add_unsat_core                   none
% 44.08/5.99  --bmc1_unsat_core_children              false
% 44.08/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 44.08/5.99  --bmc1_out_stat                         full
% 44.08/5.99  --bmc1_ground_init                      false
% 44.08/5.99  --bmc1_pre_inst_next_state              false
% 44.08/5.99  --bmc1_pre_inst_state                   false
% 44.08/5.99  --bmc1_pre_inst_reach_state             false
% 44.08/5.99  --bmc1_out_unsat_core                   false
% 44.08/5.99  --bmc1_aig_witness_out                  false
% 44.08/5.99  --bmc1_verbose                          false
% 44.08/5.99  --bmc1_dump_clauses_tptp                false
% 44.08/5.99  --bmc1_dump_unsat_core_tptp             false
% 44.08/5.99  --bmc1_dump_file                        -
% 44.08/5.99  --bmc1_ucm_expand_uc_limit              128
% 44.08/5.99  --bmc1_ucm_n_expand_iterations          6
% 44.08/5.99  --bmc1_ucm_extend_mode                  1
% 44.08/5.99  --bmc1_ucm_init_mode                    2
% 44.08/5.99  --bmc1_ucm_cone_mode                    none
% 44.08/5.99  --bmc1_ucm_reduced_relation_type        0
% 44.08/5.99  --bmc1_ucm_relax_model                  4
% 44.08/5.99  --bmc1_ucm_full_tr_after_sat            true
% 44.08/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 44.08/5.99  --bmc1_ucm_layered_model                none
% 44.08/5.99  --bmc1_ucm_max_lemma_size               10
% 44.08/5.99  
% 44.08/5.99  ------ AIG Options
% 44.08/5.99  
% 44.08/5.99  --aig_mode                              false
% 44.08/5.99  
% 44.08/5.99  ------ Instantiation Options
% 44.08/5.99  
% 44.08/5.99  --instantiation_flag                    true
% 44.08/5.99  --inst_sos_flag                         true
% 44.08/5.99  --inst_sos_phase                        true
% 44.08/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 44.08/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 44.08/5.99  --inst_lit_sel_side                     num_symb
% 44.08/5.99  --inst_solver_per_active                1400
% 44.08/5.99  --inst_solver_calls_frac                1.
% 44.08/5.99  --inst_passive_queue_type               priority_queues
% 44.08/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 44.08/5.99  --inst_passive_queues_freq              [25;2]
% 44.08/5.99  --inst_dismatching                      true
% 44.08/5.99  --inst_eager_unprocessed_to_passive     true
% 44.08/5.99  --inst_prop_sim_given                   true
% 44.08/5.99  --inst_prop_sim_new                     false
% 44.08/5.99  --inst_subs_new                         false
% 44.08/5.99  --inst_eq_res_simp                      false
% 44.08/5.99  --inst_subs_given                       false
% 44.08/5.99  --inst_orphan_elimination               true
% 44.08/5.99  --inst_learning_loop_flag               true
% 44.08/5.99  --inst_learning_start                   3000
% 44.08/5.99  --inst_learning_factor                  2
% 44.08/5.99  --inst_start_prop_sim_after_learn       3
% 44.08/5.99  --inst_sel_renew                        solver
% 44.08/5.99  --inst_lit_activity_flag                true
% 44.08/5.99  --inst_restr_to_given                   false
% 44.08/5.99  --inst_activity_threshold               500
% 44.08/5.99  --inst_out_proof                        true
% 44.08/5.99  
% 44.08/5.99  ------ Resolution Options
% 44.08/5.99  
% 44.08/5.99  --resolution_flag                       true
% 44.08/5.99  --res_lit_sel                           adaptive
% 44.08/5.99  --res_lit_sel_side                      none
% 44.08/5.99  --res_ordering                          kbo
% 44.08/5.99  --res_to_prop_solver                    active
% 44.08/5.99  --res_prop_simpl_new                    false
% 44.08/5.99  --res_prop_simpl_given                  true
% 44.08/5.99  --res_passive_queue_type                priority_queues
% 44.08/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 44.08/5.99  --res_passive_queues_freq               [15;5]
% 44.08/5.99  --res_forward_subs                      full
% 44.08/5.99  --res_backward_subs                     full
% 44.08/5.99  --res_forward_subs_resolution           true
% 44.08/5.99  --res_backward_subs_resolution          true
% 44.08/5.99  --res_orphan_elimination                true
% 44.08/5.99  --res_time_limit                        2.
% 44.08/5.99  --res_out_proof                         true
% 44.08/5.99  
% 44.08/5.99  ------ Superposition Options
% 44.08/5.99  
% 44.08/5.99  --superposition_flag                    true
% 44.08/5.99  --sup_passive_queue_type                priority_queues
% 44.08/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 44.08/5.99  --sup_passive_queues_freq               [8;1;4]
% 44.08/5.99  --demod_completeness_check              fast
% 44.08/5.99  --demod_use_ground                      true
% 44.08/5.99  --sup_to_prop_solver                    passive
% 44.08/5.99  --sup_prop_simpl_new                    true
% 44.08/5.99  --sup_prop_simpl_given                  true
% 44.08/5.99  --sup_fun_splitting                     true
% 44.08/5.99  --sup_smt_interval                      50000
% 44.08/5.99  
% 44.08/5.99  ------ Superposition Simplification Setup
% 44.08/5.99  
% 44.08/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 44.08/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 44.08/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 44.08/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 44.08/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 44.08/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 44.08/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 44.08/5.99  --sup_immed_triv                        [TrivRules]
% 44.08/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 44.08/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 44.08/5.99  --sup_immed_bw_main                     []
% 44.08/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 44.08/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 44.08/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 44.08/5.99  --sup_input_bw                          []
% 44.08/5.99  
% 44.08/5.99  ------ Combination Options
% 44.08/5.99  
% 44.08/5.99  --comb_res_mult                         3
% 44.08/5.99  --comb_sup_mult                         2
% 44.08/5.99  --comb_inst_mult                        10
% 44.08/5.99  
% 44.08/5.99  ------ Debug Options
% 44.08/5.99  
% 44.08/5.99  --dbg_backtrace                         false
% 44.08/5.99  --dbg_dump_prop_clauses                 false
% 44.08/5.99  --dbg_dump_prop_clauses_file            -
% 44.08/5.99  --dbg_out_stat                          false
% 44.08/5.99  ------ Parsing...
% 44.08/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 44.08/5.99  
% 44.08/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 44.08/5.99  
% 44.08/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 44.08/5.99  
% 44.08/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 44.08/5.99  ------ Proving...
% 44.08/5.99  ------ Problem Properties 
% 44.08/5.99  
% 44.08/5.99  
% 44.08/5.99  clauses                                 13
% 44.08/5.99  conjectures                             2
% 44.08/5.99  EPR                                     0
% 44.08/5.99  Horn                                    13
% 44.08/5.99  unary                                   9
% 44.08/5.99  binary                                  3
% 44.08/5.99  lits                                    18
% 44.08/5.99  lits eq                                 10
% 44.08/5.99  fd_pure                                 0
% 44.08/5.99  fd_pseudo                               0
% 44.08/5.99  fd_cond                                 0
% 44.08/5.99  fd_pseudo_cond                          0
% 44.08/5.99  AC symbols                              0
% 44.08/5.99  
% 44.08/5.99  ------ Schedule dynamic 5 is on 
% 44.08/5.99  
% 44.08/5.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 44.08/5.99  
% 44.08/5.99  
% 44.08/5.99  ------ 
% 44.08/5.99  Current options:
% 44.08/5.99  ------ 
% 44.08/5.99  
% 44.08/5.99  ------ Input Options
% 44.08/5.99  
% 44.08/5.99  --out_options                           all
% 44.08/5.99  --tptp_safe_out                         true
% 44.08/5.99  --problem_path                          ""
% 44.08/5.99  --include_path                          ""
% 44.08/5.99  --clausifier                            res/vclausify_rel
% 44.08/5.99  --clausifier_options                    ""
% 44.08/5.99  --stdin                                 false
% 44.08/5.99  --stats_out                             all
% 44.08/5.99  
% 44.08/5.99  ------ General Options
% 44.08/5.99  
% 44.08/5.99  --fof                                   false
% 44.08/5.99  --time_out_real                         305.
% 44.08/5.99  --time_out_virtual                      -1.
% 44.08/5.99  --symbol_type_check                     false
% 44.08/5.99  --clausify_out                          false
% 44.08/5.99  --sig_cnt_out                           false
% 44.08/5.99  --trig_cnt_out                          false
% 44.08/5.99  --trig_cnt_out_tolerance                1.
% 44.08/5.99  --trig_cnt_out_sk_spl                   false
% 44.08/5.99  --abstr_cl_out                          false
% 44.08/5.99  
% 44.08/5.99  ------ Global Options
% 44.08/5.99  
% 44.08/5.99  --schedule                              default
% 44.08/5.99  --add_important_lit                     false
% 44.08/5.99  --prop_solver_per_cl                    1000
% 44.08/5.99  --min_unsat_core                        false
% 44.08/5.99  --soft_assumptions                      false
% 44.08/5.99  --soft_lemma_size                       3
% 44.08/5.99  --prop_impl_unit_size                   0
% 44.08/5.99  --prop_impl_unit                        []
% 44.08/5.99  --share_sel_clauses                     true
% 44.08/5.99  --reset_solvers                         false
% 44.08/5.99  --bc_imp_inh                            [conj_cone]
% 44.08/5.99  --conj_cone_tolerance                   3.
% 44.08/5.99  --extra_neg_conj                        none
% 44.08/5.99  --large_theory_mode                     true
% 44.08/5.99  --prolific_symb_bound                   200
% 44.08/5.99  --lt_threshold                          2000
% 44.08/5.99  --clause_weak_htbl                      true
% 44.08/5.99  --gc_record_bc_elim                     false
% 44.08/5.99  
% 44.08/5.99  ------ Preprocessing Options
% 44.08/5.99  
% 44.08/5.99  --preprocessing_flag                    true
% 44.08/5.99  --time_out_prep_mult                    0.1
% 44.08/5.99  --splitting_mode                        input
% 44.08/5.99  --splitting_grd                         true
% 44.08/5.99  --splitting_cvd                         false
% 44.08/5.99  --splitting_cvd_svl                     false
% 44.08/5.99  --splitting_nvd                         32
% 44.08/5.99  --sub_typing                            true
% 44.08/5.99  --prep_gs_sim                           true
% 44.08/5.99  --prep_unflatten                        true
% 44.08/5.99  --prep_res_sim                          true
% 44.08/5.99  --prep_upred                            true
% 44.08/5.99  --prep_sem_filter                       exhaustive
% 44.08/5.99  --prep_sem_filter_out                   false
% 44.08/5.99  --pred_elim                             true
% 44.08/5.99  --res_sim_input                         true
% 44.08/5.99  --eq_ax_congr_red                       true
% 44.08/5.99  --pure_diseq_elim                       true
% 44.08/5.99  --brand_transform                       false
% 44.08/5.99  --non_eq_to_eq                          false
% 44.08/5.99  --prep_def_merge                        true
% 44.08/5.99  --prep_def_merge_prop_impl              false
% 44.08/5.99  --prep_def_merge_mbd                    true
% 44.08/5.99  --prep_def_merge_tr_red                 false
% 44.08/5.99  --prep_def_merge_tr_cl                  false
% 44.08/5.99  --smt_preprocessing                     true
% 44.08/5.99  --smt_ac_axioms                         fast
% 44.08/5.99  --preprocessed_out                      false
% 44.08/5.99  --preprocessed_stats                    false
% 44.08/5.99  
% 44.08/5.99  ------ Abstraction refinement Options
% 44.08/5.99  
% 44.08/5.99  --abstr_ref                             []
% 44.08/5.99  --abstr_ref_prep                        false
% 44.08/5.99  --abstr_ref_until_sat                   false
% 44.08/5.99  --abstr_ref_sig_restrict                funpre
% 44.08/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 44.08/5.99  --abstr_ref_under                       []
% 44.08/5.99  
% 44.08/5.99  ------ SAT Options
% 44.08/5.99  
% 44.08/5.99  --sat_mode                              false
% 44.08/5.99  --sat_fm_restart_options                ""
% 44.08/5.99  --sat_gr_def                            false
% 44.08/5.99  --sat_epr_types                         true
% 44.08/5.99  --sat_non_cyclic_types                  false
% 44.08/5.99  --sat_finite_models                     false
% 44.08/5.99  --sat_fm_lemmas                         false
% 44.08/5.99  --sat_fm_prep                           false
% 44.08/5.99  --sat_fm_uc_incr                        true
% 44.08/5.99  --sat_out_model                         small
% 44.08/5.99  --sat_out_clauses                       false
% 44.08/5.99  
% 44.08/5.99  ------ QBF Options
% 44.08/5.99  
% 44.08/5.99  --qbf_mode                              false
% 44.08/5.99  --qbf_elim_univ                         false
% 44.08/5.99  --qbf_dom_inst                          none
% 44.08/5.99  --qbf_dom_pre_inst                      false
% 44.08/5.99  --qbf_sk_in                             false
% 44.08/5.99  --qbf_pred_elim                         true
% 44.08/5.99  --qbf_split                             512
% 44.08/5.99  
% 44.08/5.99  ------ BMC1 Options
% 44.08/5.99  
% 44.08/5.99  --bmc1_incremental                      false
% 44.08/5.99  --bmc1_axioms                           reachable_all
% 44.08/5.99  --bmc1_min_bound                        0
% 44.08/5.99  --bmc1_max_bound                        -1
% 44.08/5.99  --bmc1_max_bound_default                -1
% 44.08/5.99  --bmc1_symbol_reachability              true
% 44.08/5.99  --bmc1_property_lemmas                  false
% 44.08/5.99  --bmc1_k_induction                      false
% 44.08/5.99  --bmc1_non_equiv_states                 false
% 44.08/5.99  --bmc1_deadlock                         false
% 44.08/5.99  --bmc1_ucm                              false
% 44.08/5.99  --bmc1_add_unsat_core                   none
% 44.08/5.99  --bmc1_unsat_core_children              false
% 44.08/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 44.08/5.99  --bmc1_out_stat                         full
% 44.08/5.99  --bmc1_ground_init                      false
% 44.08/5.99  --bmc1_pre_inst_next_state              false
% 44.08/5.99  --bmc1_pre_inst_state                   false
% 44.08/5.99  --bmc1_pre_inst_reach_state             false
% 44.08/5.99  --bmc1_out_unsat_core                   false
% 44.08/5.99  --bmc1_aig_witness_out                  false
% 44.08/5.99  --bmc1_verbose                          false
% 44.08/5.99  --bmc1_dump_clauses_tptp                false
% 44.08/5.99  --bmc1_dump_unsat_core_tptp             false
% 44.08/5.99  --bmc1_dump_file                        -
% 44.08/5.99  --bmc1_ucm_expand_uc_limit              128
% 44.08/5.99  --bmc1_ucm_n_expand_iterations          6
% 44.08/5.99  --bmc1_ucm_extend_mode                  1
% 44.08/5.99  --bmc1_ucm_init_mode                    2
% 44.08/5.99  --bmc1_ucm_cone_mode                    none
% 44.08/5.99  --bmc1_ucm_reduced_relation_type        0
% 44.08/5.99  --bmc1_ucm_relax_model                  4
% 44.08/5.99  --bmc1_ucm_full_tr_after_sat            true
% 44.08/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 44.08/5.99  --bmc1_ucm_layered_model                none
% 44.08/5.99  --bmc1_ucm_max_lemma_size               10
% 44.08/5.99  
% 44.08/5.99  ------ AIG Options
% 44.08/5.99  
% 44.08/5.99  --aig_mode                              false
% 44.08/5.99  
% 44.08/5.99  ------ Instantiation Options
% 44.08/5.99  
% 44.08/5.99  --instantiation_flag                    true
% 44.08/5.99  --inst_sos_flag                         true
% 44.08/5.99  --inst_sos_phase                        true
% 44.08/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 44.08/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 44.08/5.99  --inst_lit_sel_side                     none
% 44.08/5.99  --inst_solver_per_active                1400
% 44.08/5.99  --inst_solver_calls_frac                1.
% 44.08/5.99  --inst_passive_queue_type               priority_queues
% 44.08/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 44.08/5.99  --inst_passive_queues_freq              [25;2]
% 44.08/5.99  --inst_dismatching                      true
% 44.08/5.99  --inst_eager_unprocessed_to_passive     true
% 44.08/5.99  --inst_prop_sim_given                   true
% 44.08/5.99  --inst_prop_sim_new                     false
% 44.08/5.99  --inst_subs_new                         false
% 44.08/5.99  --inst_eq_res_simp                      false
% 44.08/5.99  --inst_subs_given                       false
% 44.08/5.99  --inst_orphan_elimination               true
% 44.08/5.99  --inst_learning_loop_flag               true
% 44.08/5.99  --inst_learning_start                   3000
% 44.08/5.99  --inst_learning_factor                  2
% 44.08/5.99  --inst_start_prop_sim_after_learn       3
% 44.08/5.99  --inst_sel_renew                        solver
% 44.08/5.99  --inst_lit_activity_flag                true
% 44.08/5.99  --inst_restr_to_given                   false
% 44.08/5.99  --inst_activity_threshold               500
% 44.08/5.99  --inst_out_proof                        true
% 44.08/5.99  
% 44.08/5.99  ------ Resolution Options
% 44.08/5.99  
% 44.08/5.99  --resolution_flag                       false
% 44.08/5.99  --res_lit_sel                           adaptive
% 44.08/5.99  --res_lit_sel_side                      none
% 44.08/5.99  --res_ordering                          kbo
% 44.08/5.99  --res_to_prop_solver                    active
% 44.08/5.99  --res_prop_simpl_new                    false
% 44.08/5.99  --res_prop_simpl_given                  true
% 44.08/5.99  --res_passive_queue_type                priority_queues
% 44.08/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 44.08/5.99  --res_passive_queues_freq               [15;5]
% 44.08/5.99  --res_forward_subs                      full
% 44.08/5.99  --res_backward_subs                     full
% 44.08/5.99  --res_forward_subs_resolution           true
% 44.08/5.99  --res_backward_subs_resolution          true
% 44.08/5.99  --res_orphan_elimination                true
% 44.08/5.99  --res_time_limit                        2.
% 44.08/5.99  --res_out_proof                         true
% 44.08/5.99  
% 44.08/5.99  ------ Superposition Options
% 44.08/5.99  
% 44.08/5.99  --superposition_flag                    true
% 44.08/5.99  --sup_passive_queue_type                priority_queues
% 44.08/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 44.08/5.99  --sup_passive_queues_freq               [8;1;4]
% 44.08/5.99  --demod_completeness_check              fast
% 44.08/5.99  --demod_use_ground                      true
% 44.08/5.99  --sup_to_prop_solver                    passive
% 44.08/5.99  --sup_prop_simpl_new                    true
% 44.08/5.99  --sup_prop_simpl_given                  true
% 44.08/5.99  --sup_fun_splitting                     true
% 44.08/5.99  --sup_smt_interval                      50000
% 44.08/5.99  
% 44.08/5.99  ------ Superposition Simplification Setup
% 44.08/5.99  
% 44.08/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 44.08/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 44.08/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 44.08/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 44.08/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 44.08/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 44.08/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 44.08/5.99  --sup_immed_triv                        [TrivRules]
% 44.08/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 44.08/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 44.08/5.99  --sup_immed_bw_main                     []
% 44.08/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 44.08/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 44.08/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 44.08/5.99  --sup_input_bw                          []
% 44.08/5.99  
% 44.08/5.99  ------ Combination Options
% 44.08/5.99  
% 44.08/5.99  --comb_res_mult                         3
% 44.08/5.99  --comb_sup_mult                         2
% 44.08/5.99  --comb_inst_mult                        10
% 44.08/5.99  
% 44.08/5.99  ------ Debug Options
% 44.08/5.99  
% 44.08/5.99  --dbg_backtrace                         false
% 44.08/5.99  --dbg_dump_prop_clauses                 false
% 44.08/5.99  --dbg_dump_prop_clauses_file            -
% 44.08/5.99  --dbg_out_stat                          false
% 44.08/5.99  
% 44.08/5.99  
% 44.08/5.99  
% 44.08/5.99  
% 44.08/5.99  ------ Proving...
% 44.08/5.99  
% 44.08/5.99  
% 44.08/5.99  % SZS status Theorem for theBenchmark.p
% 44.08/5.99  
% 44.08/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 44.08/5.99  
% 44.08/5.99  fof(f16,conjecture,(
% 44.08/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f17,negated_conjecture,(
% 44.08/5.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 44.08/5.99    inference(negated_conjecture,[],[f16])).
% 44.08/5.99  
% 44.08/5.99  fof(f24,plain,(
% 44.08/5.99    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 44.08/5.99    inference(ennf_transformation,[],[f17])).
% 44.08/5.99  
% 44.08/5.99  fof(f25,plain,(
% 44.08/5.99    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 44.08/5.99    introduced(choice_axiom,[])).
% 44.08/5.99  
% 44.08/5.99  fof(f26,plain,(
% 44.08/5.99    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 44.08/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 44.08/5.99  
% 44.08/5.99  fof(f42,plain,(
% 44.08/5.99    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 44.08/5.99    inference(cnf_transformation,[],[f26])).
% 44.08/5.99  
% 44.08/5.99  fof(f10,axiom,(
% 44.08/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f19,plain,(
% 44.08/5.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 44.08/5.99    inference(ennf_transformation,[],[f10])).
% 44.08/5.99  
% 44.08/5.99  fof(f36,plain,(
% 44.08/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 44.08/5.99    inference(cnf_transformation,[],[f19])).
% 44.08/5.99  
% 44.08/5.99  fof(f11,axiom,(
% 44.08/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f20,plain,(
% 44.08/5.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 44.08/5.99    inference(ennf_transformation,[],[f11])).
% 44.08/5.99  
% 44.08/5.99  fof(f37,plain,(
% 44.08/5.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 44.08/5.99    inference(cnf_transformation,[],[f20])).
% 44.08/5.99  
% 44.08/5.99  fof(f12,axiom,(
% 44.08/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f21,plain,(
% 44.08/5.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 44.08/5.99    inference(ennf_transformation,[],[f12])).
% 44.08/5.99  
% 44.08/5.99  fof(f38,plain,(
% 44.08/5.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 44.08/5.99    inference(cnf_transformation,[],[f21])).
% 44.08/5.99  
% 44.08/5.99  fof(f7,axiom,(
% 44.08/5.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f33,plain,(
% 44.08/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 44.08/5.99    inference(cnf_transformation,[],[f7])).
% 44.08/5.99  
% 44.08/5.99  fof(f5,axiom,(
% 44.08/5.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f31,plain,(
% 44.08/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 44.08/5.99    inference(cnf_transformation,[],[f5])).
% 44.08/5.99  
% 44.08/5.99  fof(f6,axiom,(
% 44.08/5.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f32,plain,(
% 44.08/5.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 44.08/5.99    inference(cnf_transformation,[],[f6])).
% 44.08/5.99  
% 44.08/5.99  fof(f49,plain,(
% 44.08/5.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 44.08/5.99    inference(definition_unfolding,[],[f33,f31,f32])).
% 44.08/5.99  
% 44.08/5.99  fof(f2,axiom,(
% 44.08/5.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f18,plain,(
% 44.08/5.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 44.08/5.99    inference(rectify,[],[f2])).
% 44.08/5.99  
% 44.08/5.99  fof(f28,plain,(
% 44.08/5.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 44.08/5.99    inference(cnf_transformation,[],[f18])).
% 44.08/5.99  
% 44.08/5.99  fof(f46,plain,(
% 44.08/5.99    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 44.08/5.99    inference(definition_unfolding,[],[f28,f31])).
% 44.08/5.99  
% 44.08/5.99  fof(f4,axiom,(
% 44.08/5.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f30,plain,(
% 44.08/5.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 44.08/5.99    inference(cnf_transformation,[],[f4])).
% 44.08/5.99  
% 44.08/5.99  fof(f48,plain,(
% 44.08/5.99    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 44.08/5.99    inference(definition_unfolding,[],[f30,f31])).
% 44.08/5.99  
% 44.08/5.99  fof(f1,axiom,(
% 44.08/5.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f27,plain,(
% 44.08/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 44.08/5.99    inference(cnf_transformation,[],[f1])).
% 44.08/5.99  
% 44.08/5.99  fof(f45,plain,(
% 44.08/5.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 44.08/5.99    inference(definition_unfolding,[],[f27,f31,f31])).
% 44.08/5.99  
% 44.08/5.99  fof(f13,axiom,(
% 44.08/5.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f22,plain,(
% 44.08/5.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 44.08/5.99    inference(ennf_transformation,[],[f13])).
% 44.08/5.99  
% 44.08/5.99  fof(f23,plain,(
% 44.08/5.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 44.08/5.99    inference(flattening,[],[f22])).
% 44.08/5.99  
% 44.08/5.99  fof(f39,plain,(
% 44.08/5.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 44.08/5.99    inference(cnf_transformation,[],[f23])).
% 44.08/5.99  
% 44.08/5.99  fof(f51,plain,(
% 44.08/5.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 44.08/5.99    inference(definition_unfolding,[],[f39,f31])).
% 44.08/5.99  
% 44.08/5.99  fof(f9,axiom,(
% 44.08/5.99    ! [X0] : k2_subset_1(X0) = X0),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f35,plain,(
% 44.08/5.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 44.08/5.99    inference(cnf_transformation,[],[f9])).
% 44.08/5.99  
% 44.08/5.99  fof(f14,axiom,(
% 44.08/5.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f40,plain,(
% 44.08/5.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 44.08/5.99    inference(cnf_transformation,[],[f14])).
% 44.08/5.99  
% 44.08/5.99  fof(f8,axiom,(
% 44.08/5.99    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f34,plain,(
% 44.08/5.99    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 44.08/5.99    inference(cnf_transformation,[],[f8])).
% 44.08/5.99  
% 44.08/5.99  fof(f44,plain,(
% 44.08/5.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 44.08/5.99    inference(definition_unfolding,[],[f40,f34])).
% 44.08/5.99  
% 44.08/5.99  fof(f50,plain,(
% 44.08/5.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 44.08/5.99    inference(definition_unfolding,[],[f35,f44])).
% 44.08/5.99  
% 44.08/5.99  fof(f15,axiom,(
% 44.08/5.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 44.08/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 44.08/5.99  
% 44.08/5.99  fof(f41,plain,(
% 44.08/5.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 44.08/5.99    inference(cnf_transformation,[],[f15])).
% 44.08/5.99  
% 44.08/5.99  fof(f43,plain,(
% 44.08/5.99    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 44.08/5.99    inference(cnf_transformation,[],[f26])).
% 44.08/5.99  
% 44.08/5.99  fof(f52,plain,(
% 44.08/5.99    k3_subset_1(sK0,k1_xboole_0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 44.08/5.99    inference(definition_unfolding,[],[f43,f44])).
% 44.08/5.99  
% 44.08/5.99  cnf(c_12,negated_conjecture,
% 44.08/5.99      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 44.08/5.99      inference(cnf_transformation,[],[f42]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_206,plain,
% 44.08/5.99      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 44.08/5.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_6,plain,
% 44.08/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 44.08/5.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 44.08/5.99      inference(cnf_transformation,[],[f36]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_211,plain,
% 44.08/5.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 44.08/5.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 44.08/5.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1826,plain,
% 44.08/5.99      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_206,c_211]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_7,plain,
% 44.08/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 44.08/5.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 44.08/5.99      inference(cnf_transformation,[],[f37]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_210,plain,
% 44.08/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 44.08/5.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 44.08/5.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2097,plain,
% 44.08/5.99      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
% 44.08/5.99      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_1826,c_210]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_13,plain,
% 44.08/5.99      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 44.08/5.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2437,plain,
% 44.08/5.99      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
% 44.08/5.99      inference(global_propositional_subsumption,
% 44.08/5.99                [status(thm)],
% 44.08/5.99                [c_2097,c_13]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2441,plain,
% 44.08/5.99      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_2437,c_211]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_8,plain,
% 44.08/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 44.08/5.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 44.08/5.99      inference(cnf_transformation,[],[f38]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_209,plain,
% 44.08/5.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 44.08/5.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 44.08/5.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1236,plain,
% 44.08/5.99      ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_206,c_209]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2091,plain,
% 44.08/5.99      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_1826,c_1236]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2451,plain,
% 44.08/5.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_2441,c_2091]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 44.08/5.99      inference(cnf_transformation,[],[f49]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1,plain,
% 44.08/5.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 44.08/5.99      inference(cnf_transformation,[],[f46]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_424,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_3,plain,
% 44.08/5.99      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 44.08/5.99      inference(cnf_transformation,[],[f48]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_213,plain,
% 44.08/5.99      ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_3,c_4]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_563,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_424,c_213]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_682,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_563,c_4]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_688,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_682,c_4]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_907,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_688,c_213]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_0,plain,
% 44.08/5.99      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 44.08/5.99      inference(cnf_transformation,[],[f45]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_422,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_501,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_422,c_4]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_562,plain,
% 44.08/5.99      ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_501,c_213]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_908,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_907,c_562]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2464,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_2451,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_9,plain,
% 44.08/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 44.08/5.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 44.08/5.99      | k5_xboole_0(X0,k4_xboole_0(X2,X0)) = k4_subset_1(X1,X0,X2) ),
% 44.08/5.99      inference(cnf_transformation,[],[f51]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_208,plain,
% 44.08/5.99      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 44.08/5.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 44.08/5.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 44.08/5.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_215,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 44.08/5.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 44.08/5.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_208,c_4]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1112,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(k3_subset_1(X0,X1),k3_subset_1(X0,X1),X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
% 44.08/5.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 44.08/5.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_210,c_215]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1743,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),X0)) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),X0)
% 44.08/5.99      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_206,c_1112]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2100,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),X0)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),X0)
% 44.08/5.99      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_1743,c_1826]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2106,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_206,c_2100]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2237,plain,
% 44.08/5.99      ( k4_xboole_0(X0,k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_2106,c_213]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_5,plain,
% 44.08/5.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 44.08/5.99      inference(cnf_transformation,[],[f50]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_493,plain,
% 44.08/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 44.08/5.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_5,c_210]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_10,plain,
% 44.08/5.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 44.08/5.99      inference(cnf_transformation,[],[f41]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_14,plain,
% 44.08/5.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 44.08/5.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1225,plain,
% 44.08/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 44.08/5.99      inference(global_propositional_subsumption,
% 44.08/5.99                [status(thm)],
% 44.08/5.99                [c_493,c_14]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1114,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(sK1,sK1,X0)) = k4_subset_1(sK0,sK1,X0)
% 44.08/5.99      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_206,c_215]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1404,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k4_subset_1(sK0,sK1,sK0) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_1225,c_1114]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1497,plain,
% 44.08/5.99      ( k4_xboole_0(X0,k4_subset_1(sK0,sK1,sK0)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_1404,c_562]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2235,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_2106,c_501]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2240,plain,
% 44.08/5.99      ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK1) = k4_subset_1(sK0,sK1,sK0) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_2235,c_688,c_1404]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2244,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK1) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_2237,c_1497,c_2240]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2466,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_2464,c_2244]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_561,plain,
% 44.08/5.99      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_422,c_213]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_569,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_561,c_4,c_213]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1827,plain,
% 44.08/5.99      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_1225,c_211]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_207,plain,
% 44.08/5.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 44.08/5.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1235,plain,
% 44.08/5.99      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_207,c_209]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1238,plain,
% 44.08/5.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_1235,c_5]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1828,plain,
% 44.08/5.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_1827,c_1238]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_46758,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_1828,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_47508,plain,
% 44.08/5.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_46758,c_1828]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1231,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X0,X0,X1)
% 44.08/5.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_1225,c_215]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_3434,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_206,c_1231]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_3770,plain,
% 44.08/5.99      ( k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_3434,c_213]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_669,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_569,c_0]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_3869,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1))) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_3770,c_669]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_46831,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X0))) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k1_xboole_0,sK1),X0)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_1828,c_3869]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4284,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) = k4_xboole_0(sK1,sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_2451,c_2244]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4334,plain,
% 44.08/5.99      ( k4_xboole_0(k1_xboole_0,sK1) = k1_xboole_0 ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_4284,c_1828]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_47376,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X0))) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k1_xboole_0,X0)) ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_46831,c_4334]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_47518,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X0))) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k1_xboole_0) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_47508,c_47376]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1825,plain,
% 44.08/5.99      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_207,c_211]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1829,plain,
% 44.08/5.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_1825,c_5]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1043,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_908,c_1]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1859,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_1829,c_1043]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1860,plain,
% 44.08/5.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_1859,c_1829]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1861,plain,
% 44.08/5.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_1860,c_1,c_1828]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_47580,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X0))) = k4_subset_1(sK0,sK0,sK1) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_47518,c_4,c_1861]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_53776,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_subset_1(sK0,sK0,sK1))) = k4_subset_1(sK0,sK0,sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_47580,c_4]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_54160,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,X1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_53776,c_213]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_54200,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,X1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_54160,c_3770]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_54368,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK0,X2))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_54200,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_3374,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK1,sK0)),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_subset_1(sK0,sK1,sK0)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_1497,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_3376,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_subset_1(sK0,sK1,sK0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_1497,c_569]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_3400,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_3374,c_1497,c_3376]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_54641,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK0,X2))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/5.99      inference(light_normalisation,
% 44.08/5.99                [status(thm)],
% 44.08/5.99                [c_54368,c_3400,c_3770]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_56503,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_54641,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_3870,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_3770,c_569]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4455,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_3870,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4481,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_4455,c_3870]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4482,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_4481,c_3770]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_56774,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/5.99      inference(light_normalisation,
% 44.08/5.99                [status(thm)],
% 44.08/5.99                [c_56503,c_3770,c_4482]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2849,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X1),X2)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_908,c_669]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_685,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))),X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_563,c_213]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_686,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 44.08/5.99      inference(light_normalisation,[status(thm)],[c_685,c_562]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_687,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_686,c_563]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_865,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_569,c_687]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1030,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X3) = k4_xboole_0(k4_xboole_0(X0,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_865,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_906,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_688,c_562]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_909,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_906,c_562]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1063,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_1030,c_909]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2859,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X0,X2)),X1)) = k5_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X1),X2)) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_2849,c_4,c_1063]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_60462,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X1,k4_xboole_0(sK0,X2))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK0),sK1),k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X3,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X1,k4_xboole_0(sK0,X2)))) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_56774,c_2859]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_681,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_569,c_563]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2832,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X1),X3),X2)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_681,c_669]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_665,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_569,c_4]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1019,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_687,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1048,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X1),X2) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_908,c_569]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1073,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X1),X2) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_1019,c_1048]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2782,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X0),X3))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X3)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_865,c_665]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_764,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_681,c_4]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_784,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_764,c_4]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2786,plain,
% 44.08/5.99      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X3)) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_2782,c_784]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_2870,plain,
% 44.08/5.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k3_tarski(k1_enumset1(X3,X3,k4_xboole_0(k4_xboole_0(X0,X2),X1))) ),
% 44.08/5.99      inference(demodulation,
% 44.08/5.99                [status(thm)],
% 44.08/5.99                [c_2832,c_4,c_665,c_1073,c_2786]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_13875,plain,
% 44.08/5.99      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X1,X2),X3)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X3),X2)),X4) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_2870,c_562]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_13882,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X4) = k4_xboole_0(k4_xboole_0(X0,X4),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_13875,c_4,c_562]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_14748,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)),X2)),X3) = k4_xboole_0(k4_xboole_0(X0,X3),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),sK0),sK1)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_3770,c_13882]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_15184,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),sK0),sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),X3)),X1) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_14748,c_3770]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_56599,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_54641,c_15184]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_56605,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/5.99      inference(light_normalisation,
% 44.08/5.99                [status(thm)],
% 44.08/5.99                [c_56599,c_3400,c_3770]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_8936,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_4482,c_681]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1029,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X3),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X1),X3)),X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_681,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1064,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3)),X2) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X3)),X2) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_1029,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1021,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X1),X3),X1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_865,c_908]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_1071,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X2),X1) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_1021,c_1048]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4431,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK0),sK1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_2451,c_3870]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4299,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK1) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_2244,c_687]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4320,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/5.99      inference(demodulation,[status(thm)],[c_4299,c_2244]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4499,plain,
% 44.08/5.99      ( k4_xboole_0(k4_xboole_0(sK1,sK0),sK1) = k1_xboole_0 ),
% 44.08/5.99      inference(demodulation,
% 44.08/5.99                [status(thm)],
% 44.08/5.99                [c_4431,c_1828,c_3770,c_4320,c_4334]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_3860,plain,
% 44.08/5.99      ( k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1)) = k5_xboole_0(X0,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),X0)) ),
% 44.08/5.99      inference(superposition,[status(thm)],[c_3770,c_0]) ).
% 44.08/5.99  
% 44.08/5.99  cnf(c_4888,plain,
% 44.08/5.99      ( k5_xboole_0(sK1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k1_xboole_0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_4499,c_3860]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4908,plain,
% 44.08/6.00      ( k5_xboole_0(sK1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)) = k4_subset_1(sK0,sK0,sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_4888,c_4,c_1861]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5009,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(sK1,sK1,k4_subset_1(sK0,sK0,sK1))) = k4_subset_1(sK0,sK0,sK1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_4,c_4908]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5012,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5009,c_213]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5013,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_5012,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5149,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5013,c_908]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5172,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_5149,c_3400,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5390,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5172,c_908]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5416,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_5390,c_3770,c_4482]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8545,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5416,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8754,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),sK1),sK0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),sK0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_8545,c_681]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3863,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3770,c_865]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3902,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_3863,c_3770,c_3870]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8514,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5416,c_3902]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8523,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5416,c_563]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8571,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_8523,c_5416]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8580,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_8514,c_8545,c_8571]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4446,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3870,c_681]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4457,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3870,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4484,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_4446,c_4457]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5400,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5172,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5806,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),sK0),X2),sK1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5400,c_681]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5814,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),sK0),X2),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5400,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5838,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_5806,c_5814]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_6853,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),sK0),sK1),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_569,c_3902]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8581,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),sK0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_8580,c_4484,c_5838,c_6853]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8799,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK1))),sK1),sK0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_8754,c_8581]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_2773,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_908,c_665]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_2791,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_2773,c_4]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3616,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X3) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X3,X3,k4_xboole_0(X1,X2)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2791,c_562]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3623,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X3) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_3616,c_562]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8800,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),sK1),sK0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_8799,c_3623]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8990,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_8936,c_1063,c_1064,c_1071,c_8800]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_16774,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_15184,c_3870]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_16857,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_16774,c_3770,c_4482]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_56606,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(sK0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_56605,c_4482,c_8990,c_16857]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_60510,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_60462,c_3770,c_56606]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_60511,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_60510,c_3770,c_3870]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82133,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),X2),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_569,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_60371,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_56774,c_681]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_56585,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK0,X2))),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_54641,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_57579,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_56585,c_16857]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_57617,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_57579,c_4482]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_60658,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_60371,c_3770,c_57617]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_63373,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)),k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3770,c_60658]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_64189,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1))) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_63373,c_3400]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_64190,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_64189,c_3400,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_60407,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3))),k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_56774,c_669]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_60604,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3))),k4_xboole_0(k4_xboole_0(X0,sK0),sK1))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X3))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_60407,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82735,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2))),k4_xboole_0(sK0,X3))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X4,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2))),k4_xboole_0(sK0,X3))),k4_xboole_0(k4_xboole_0(X4,sK0),sK1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_64190,c_60604]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_63410,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),k4_subset_1(sK0,sK0,sK1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_54200,c_60658]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_64116,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),k4_subset_1(sK0,sK0,sK1))) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_63410,c_3400]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_56596,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X3)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_54641,c_13882]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_56610,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X3)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_56596,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3846,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_subset_1(sK0,sK0,sK1),k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1))) = k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3770,c_665]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_567,plain,
% 44.08/6.00      ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) = k5_xboole_0(X2,k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_213,c_0]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_6344,plain,
% 44.08/6.00      ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) = k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_422,c_567]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_6384,plain,
% 44.08/6.00      ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) = k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(X1,X1,X0)))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_6344,c_4]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_13148,plain,
% 44.08/6.00      ( k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)),k4_xboole_0(k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_subset_1(sK0,sK0,sK1))))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3846,c_6384]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_13194,plain,
% 44.08/6.00      ( k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_subset_1(sK0,sK0,sK1))))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_13148,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_27540,plain,
% 44.08/6.00      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK0),sK1),k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X3),k3_tarski(k1_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_subset_1(sK0,sK0,sK1)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_13194,c_213]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_975,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X3) = k4_xboole_0(k4_xboole_0(X0,X3),k3_tarski(k1_enumset1(X1,X1,X2))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_213,c_865]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_976,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X3),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_569,c_865]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_1006,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_tarski(k1_enumset1(X2,X2,X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X3),X1),X2) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_975,c_976]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_27555,plain,
% 44.08/6.00      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK0),sK1),k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X3),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_27540,c_1006,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_58891,plain,
% 44.08/6.00      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),sK0),sK1),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,sK0),sK1),k4_xboole_0(X1,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X4),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),X3)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_56610,c_27555]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_58940,plain,
% 44.08/6.00      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(sK0,X2)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,sK0),sK1),k4_xboole_0(X1,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X4),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),X3)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_58891,c_8990]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_46768,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_13882]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47471,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)) = k4_xboole_0(X0,X1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_46768,c_1829]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47472,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X2),X3)) = k4_xboole_0(X0,X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_47471,c_909]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47473,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X0,X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_47472,c_1828]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_46896,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k1_xboole_0,sK1),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(sK0,X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_4482]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47279,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(sK0,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k1_xboole_0,X1)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_46896,c_4334]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47478,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(sK0,X1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_47473,c_47279]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_58941,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK0,X3)),X4)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,X4)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_58940,c_27555,c_47478]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_64117,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK0,X2)),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_64116,c_3400,c_3770,c_56610,c_58941]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_68727,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2))),k4_xboole_0(sK0,X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_569,c_64117]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82764,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,sK0),sK1))) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_82735,c_68727]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_6881,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3902,c_908]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_6893,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3902,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_6920,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_6881,c_6893]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5803,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),sK0),X2),sK1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5400,c_908]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5841,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_5803,c_5814]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_6921,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,sK0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_6920,c_3770,c_5841]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7450,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,X3),sK0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,sK0),X3)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_681,c_6921]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7530,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,sK0),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,X3)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_7450,c_6921]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_13845,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = k3_tarski(k1_enumset1(X3,X3,k4_xboole_0(k4_xboole_0(X0,X2),X1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2870,c_4]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_2834,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X3),k4_xboole_0(X1,X2))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_908,c_669]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_2868,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k3_tarski(k1_enumset1(X3,X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_2834,c_4,c_665,c_1048]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_25552,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X3,X4),X5))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X5),X4),k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_13845,c_2868]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_25357,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2)) = k3_tarski(k1_enumset1(X2,X2,k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),X1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3770,c_13845]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_25747,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2)) = k3_tarski(k1_enumset1(X2,X2,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1))) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_25357,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_26633,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_25747,c_2868]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82274,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X4)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_60511,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82275,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = sP0_iProver_split(X0,X1,X2) ),
% 44.08/6.00      inference(splitting,
% 44.08/6.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 44.08/6.00                [c_82274]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82277,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) = sP0_iProver_split(X2,X0,X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_82275,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82765,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2),k4_xboole_0(X0,sK1))) = sP0_iProver_split(X0,X1,X2) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_82764,c_4482,c_7530,c_25552,c_26633,c_82277]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_14660,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)),sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,sK0),sK1)),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5013,c_13882]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_15274,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,sK1),sK0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,sK0),sK1)),X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_14660,c_865,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_15914,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(X2,sK1),sK0)),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,sK0),sK1)),sK0),sK1),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_15274,c_5400]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5783,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,sK1)),sK0),sK1),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,sK1)),X1),sK0),sK1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_865,c_5400]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5863,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,sK1)),X1),sK0),sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_5783,c_5400]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5361,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,sK1)),sK0),sK1),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,sK1)),X1),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_865,c_5172]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5392,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),X2),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5172,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5442,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X2),X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_5361,c_5392,c_5400]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5864,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),X2),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_5863,c_5442]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_15984,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK0)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X2),k4_xboole_0(X1,sK1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_15914,c_909,c_5400,c_5864]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3857,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3770,c_563]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3903,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_3857,c_3770,c_3870]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4730,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK0),sK1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3903,c_908]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4741,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK0),sK1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_4730,c_3400,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7135,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK0)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_4741,c_5172]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_15985,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X2,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X2),X1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_15984,c_7135]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82766,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),X2)) = sP0_iProver_split(X0,X1,X2) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_82765,c_15985]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82192,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK0),k4_xboole_0(X1,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,sK1),k4_xboole_0(X0,X1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_46906,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1) = k1_xboole_0 ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_48936,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),X0),sK1) = k4_xboole_0(k1_xboole_0,X0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_46906,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_49373,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),X0),sK1) = k1_xboole_0 ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_48936,c_47508]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_41406,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X2),k4_subset_1(sK0,sK0,sK1)),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3903,c_2859]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3856,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3770,c_681]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3904,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_3856,c_3870]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7095,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,sK1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5400,c_4741]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3617,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,k4_xboole_0(X2,X3)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2791,c_213]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3622,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_3617,c_562]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5369,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK1),X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,X2),sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_865,c_5172]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4292,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),X1),sK1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2244,c_908]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4304,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),X1),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2244,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4326,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_4292,c_4304]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5435,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK1),X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_5369,c_3870,c_4326]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7174,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(X1,X2)),sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_7095,c_3622,c_5435]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_41958,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),k4_xboole_0(X0,X1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X2),X1)) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_41406,c_665,c_3770,c_3904,c_7174]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_49068,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),k4_xboole_0(X0,X1)),sK1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_46906,c_41958]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_41665,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X2)),X1)) = k5_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3770,c_2859]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_44509,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)),X1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)),k4_subset_1(sK0,sK0,sK1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3903,c_41665]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_44948,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),k4_xboole_0(X0,X1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK0),sK1),X1)) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_44509,c_665,c_3770,c_4484,c_7174]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4439,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3870,c_3870]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4493,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK0),sK1),sK1),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),sK0),sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_4439,c_4457]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4494,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK0),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_4493,c_976,c_1071]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4495,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_4494,c_687]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5126,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK1),sK0),sK1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_865,c_5013]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5151,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5013,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5199,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK1),sK0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_5126,c_5151]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_44949,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),k4_xboole_0(X0,X1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK0),sK1),X1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_44948,c_4495,c_5199]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_44950,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),k4_xboole_0(X0,X1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_44949,c_563]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_46944,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),X1),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_41665]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47188,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_46944,c_3770,c_3903]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_1847,plain,
% 44.08/6.00      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1829,c_0]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_13853,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2870,c_1847]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_12025,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2868,c_1847]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_1839,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1829,c_4]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_568,plain,
% 44.08/6.00      ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X0),X1)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_213,c_1]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7954,plain,
% 44.08/6.00      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0)) = k3_tarski(k1_enumset1(X0,X0,X0)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_424,c_568]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7988,plain,
% 44.08/6.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_7954,c_424,c_1828,c_1847]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_12062,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_12025,c_1839,c_7988]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_13895,plain,
% 44.08/6.00      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_13853,c_12062]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_44648,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),X1),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK0),sK1),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5013,c_41665]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_44675,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(X0,X1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK0),sK1),X1)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_44648,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_44676,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_44675,c_563,c_3770,c_3870]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47189,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_47188,c_3870,c_13895,c_44676]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47261,plain,
% 44.08/6.00      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_46906,c_47189]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_49155,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),k4_xboole_0(X0,X1)),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_49068,c_3903,c_44950,c_47261]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_49378,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_49373,c_49155]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_54263,plain,
% 44.08/6.00      ( k4_xboole_0(sK1,k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2451,c_54200]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_54769,plain,
% 44.08/6.00      ( k4_xboole_0(sK1,k4_subset_1(sK0,sK0,sK1)) = k1_xboole_0 ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_54263,c_1828,c_3770,c_4334]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_13876,plain,
% 44.08/6.00      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X1,X2),X3)))) = k4_xboole_0(k4_xboole_0(X0,X4),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2870,c_213]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_13881,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X4),X3)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_13876,c_4,c_562]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_14183,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),sK0),sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3770,c_13881]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_15349,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),sK0),sK1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_14183,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_55163,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(sK1,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_54769,c_15349]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_55365,plain,
% 44.08/6.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_55163,c_54769]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_18438,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_4499,c_15349]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8875,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_4499,c_4482]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_9057,plain,
% 44.08/6.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_8875,c_4499]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_19019,plain,
% 44.08/6.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_18438,c_4499,c_9057]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_49035,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK0),sK1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_46906,c_4482]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_49205,plain,
% 44.08/6.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_49035,c_46906]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_49206,plain,
% 44.08/6.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) = k1_xboole_0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_49205,c_47508]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_55366,plain,
% 44.08/6.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_55365,c_19019,c_49206]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83334,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK0),k4_xboole_0(X1,k4_xboole_0(sK0,X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_82192,c_4334,c_49378,c_55366]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83335,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),X1),sK1) = sP0_iProver_split(sK0,X0,X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83334,c_82275]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82138,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(k4_xboole_0(X2,sK1),k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),X2),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,sK1)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_908,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83483,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(k4_xboole_0(X2,sK1),k4_xboole_0(sK0,X3)))) = k5_xboole_0(sP0_iProver_split(sK0,X1,X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,sK1)))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_82138,c_82766,c_83335]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8546,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,k4_xboole_0(X2,sK1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5416,c_3870]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83484,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(k4_xboole_0(X2,sK1),k4_xboole_0(sK0,X3)))) = k5_xboole_0(sP0_iProver_split(sK0,X1,X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2))) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_83483,c_8546]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83485,plain,
% 44.08/6.00      ( k5_xboole_0(sP0_iProver_split(sK0,X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) = sP0_iProver_split(X2,X0,k4_xboole_0(X1,sK1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83484,c_82275]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83503,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(X2,k4_xboole_0(sK0,X3)))) = sP0_iProver_split(X0,X1,k4_xboole_0(X2,sK1)) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_82133,c_82766,c_83335,c_83485]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83504,plain,
% 44.08/6.00      ( sP0_iProver_split(X0,X1,k4_xboole_0(X2,sK1)) = sP0_iProver_split(X0,X1,X2) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_83503,c_82275]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82215,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK0),sK1),X0),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,X1)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK0),sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2451,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_2465,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,X0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2451,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_77806,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),X1),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK1,X0),X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2465,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83282,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK1),sK0)) = sP0_iProver_split(X0,sK0,k4_xboole_0(sK0,sK1)) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_82215,c_865,c_77806,c_82275]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_41601,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1))),X1)) = k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),sK0),sK1),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3870,c_2859]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_41744,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,sK0),sK1)),X1)) = k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),sK0),sK1),X1)) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_41601,c_3770,c_3870]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_42880,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,sK0),sK1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK0),sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5013,c_41744]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_42993,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,sK0),sK1)),k4_subset_1(sK0,sK0,sK1))) = k5_xboole_0(k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK0),sK1)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_42880,c_3903]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_42994,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),X0),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_42993,c_665,c_865,c_3770,c_4741]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_43497,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),X0),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK1),sK0)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_865,c_42994]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4675,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),X0),sK1) = k4_xboole_0(k1_xboole_0,X0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_4499,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_41453,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_subset_1(sK0,sK0,sK1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5172,c_2859]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_41904,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_subset_1(sK0,sK0,sK1)),sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_41453,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8540,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1)))) = k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5416,c_784]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8556,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1)))) = k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(X2,sK0),sK1))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_8540,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8541,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X2,k4_subset_1(sK0,sK0,sK1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5416,c_665]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_8555,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(X2,sK0),sK1))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_8541,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_24266,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_8556,c_8555,c_8556]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_24382,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3903,c_24266]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5388,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X1,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X1,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5172,c_681]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5417,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(X1,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_5388,c_3770,c_4326]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_6078,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3903,c_5417]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_6172,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_6078,c_3903]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_24515,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1))) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_24382,c_3903,c_6172]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7119,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_4741,c_681]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7153,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_7119,c_3400,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7641,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_7153,c_4]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5396,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_subset_1(sK0,sK0,sK1)))) = k5_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5172,c_665]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_1033,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X2,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_908,c_4]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5410,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),X0),sK1)) = k5_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_5396,c_1033,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_9149,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK1),X1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),k4_xboole_0(k4_xboole_0(X0,sK1),X1)),sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_687,c_5410]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5368,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),sK1)),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK1),X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_681,c_5172]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_5436,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK1),X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_5368,c_5172]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_9245,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_xboole_0(k4_xboole_0(X2,sK0),sK1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(X0,X1))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_9149,c_665,c_687,c_5436]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7121,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,sK0),sK1))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_4741,c_908]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_7152,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,sK0),sK1))),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_7121,c_3770,c_4482]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_10338,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X2,X3)))) = k5_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X3,sK0),sK1))),X0),k4_subset_1(sK0,sK0,sK1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_7152,c_1033]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_10344,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,sK0),sK1))),X3),k4_subset_1(sK0,sK0,sK1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,X2)),X3) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_7152,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_10383,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X2,X3)))) = k5_xboole_0(k4_xboole_0(X0,k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X2,X3)),X0)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_10338,c_10344]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_10384,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X2,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X2,X3)),X0)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_10383,c_3770]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_13874,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X1),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X2),X1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2870,c_501]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_24516,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(X0,sK0))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_24515,c_3400,c_7641,c_9245,c_10384,c_13874]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_24517,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_24516,c_7135]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_41905,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),sK1),sK0)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_41904,c_865,c_1071,c_3770,c_3870,c_24517]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_42360,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),sK1),X0)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),sK1),k4_xboole_0(k4_xboole_0(X0,sK1),sK0)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1829,c_41905]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4671,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(sK1,sK0),sK1) = k4_xboole_0(k1_xboole_0,sK0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_4499,c_687]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_4683,plain,
% 44.08/6.00      ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_4671,c_4499]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_42618,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,sK1),sK0)) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_42360,c_4334,c_4683]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_42619,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_42618,c_13895]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_43591,plain,
% 44.08/6.00      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,sK1),sK0)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_43497,c_4499,c_4675,c_42619]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83283,plain,
% 44.08/6.00      ( sP0_iProver_split(X0,sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK0),sK1) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_83282,c_4499,c_43591]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83505,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,sK0),sK1) = sP0_iProver_split(X0,sK0,sK0) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83504,c_83283]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82136,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(sK0,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK0))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_681,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83491,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(sK0,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_82136,c_7135]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83492,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,X0,sK0) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83491,c_24517,c_82275]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82137,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(sK1,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(X1,sK1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_865,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83486,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(sK1,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_82137,c_4326]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83487,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),sK0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,X0,sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83486,c_24517,c_82275]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83493,plain,
% 44.08/6.00      ( sP0_iProver_split(X0,X1,sK0) = sP0_iProver_split(X0,X1,sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83492,c_83487]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82213,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1829,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83288,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,X0,k1_xboole_0) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_82213,c_1829,c_82275]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82220,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sK0),sK1),X2),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X3)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_3870,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83257,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),sK0),sK1),X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X3)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X2))) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_82220,c_3902]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83258,plain,
% 44.08/6.00      ( sP0_iProver_split(X0,k4_xboole_0(X1,X2),k4_subset_1(sK0,sK0,sK1)) = sP0_iProver_split(X0,X1,X2) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_83257,c_4482,c_26633,c_82275,c_82277]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_82225,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),sK1),X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(X1,sK0),sK1))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_5013,c_60511]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83242,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),sK1),X0),k4_xboole_0(k4_subset_1(sK0,sK0,sK1),k4_xboole_0(sK0,X2)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK1),sK0),sK1),k4_subset_1(sK0,sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),X1)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_82225,c_3400]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83243,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,k4_xboole_0(X0,sK1),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83242,c_3902,c_82275]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83244,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,k4_xboole_0(X0,sK1),k4_subset_1(sK0,sK0,sK1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83243,c_865,c_24517]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83259,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,sK0),sK1),X0)) = sP0_iProver_split(X1,X0,sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83258,c_83244]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83291,plain,
% 44.08/6.00      ( sP0_iProver_split(X0,X1,k1_xboole_0) = sP0_iProver_split(X0,X1,sK1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83288,c_83259]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83494,plain,
% 44.08/6.00      ( sP0_iProver_split(X0,X1,sK0) = sP0_iProver_split(X0,X1,k1_xboole_0) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83493,c_83291]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83507,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,sK0),sK1) = sP0_iProver_split(X0,sK0,k1_xboole_0) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83505,c_83494]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83698,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1)) = sP0_iProver_split(X0,sK0,k1_xboole_0) ),
% 44.08/6.00      inference(light_normalisation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_2466,c_2466,c_83507]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83858,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(sK0,sP0_iProver_split(X0,sK0,k1_xboole_0)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_83698,c_665]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83885,plain,
% 44.08/6.00      ( sP0_iProver_split(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_83698,c_687]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_83886,plain,
% 44.08/6.00      ( sP0_iProver_split(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_83698,c_681]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_84127,plain,
% 44.08/6.00      ( sP0_iProver_split(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK0,k1_xboole_0) = sP0_iProver_split(X0,sK0,k1_xboole_0) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83886,c_83698]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_84129,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK0) = sP0_iProver_split(X0,sK0,k1_xboole_0) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_83885,c_84127]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_46622,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X1),X2)) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_2859]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_46712,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k1_xboole_0,X1) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_569]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47658,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_46712,c_47508]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_46662,plain,
% 44.08/6.00      ( k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k4_xboole_0(X1,X0))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_1033]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_46815,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),X1)) = k3_tarski(k1_enumset1(X1,X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,sK1),X0))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_25747]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47401,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),X1)) = k3_tarski(k1_enumset1(X1,X1,k4_xboole_0(k1_xboole_0,X0))) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_46815,c_4334]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47516,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),X1)) = k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_47508,c_47401]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_46855,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X0),X1))) = k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_2791]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_14808,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4)))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X2,X4),X3))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_13882,c_4]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47015,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X0),X2)))) = k5_xboole_0(X0,k1_xboole_0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_14808]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47062,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X0),X2)))) = X0 ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_47015,c_1861]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3601,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3),X2))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_687,c_2791]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3602,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3),X2))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X0)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_681,c_2791]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3633,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3),X2))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X3),X2))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_3602,c_2791]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3634,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X3),X2))) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_3601,c_3633]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_14414,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X0),X4)))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4)))) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_13881,c_2791]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47063,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(k4_xboole_0(X1,X2),X1))) = X0 ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_47062,c_908,c_3634,c_14414]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47345,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_46855,c_47063]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47582,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),sK1),X1)) = X1 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_47516,c_47345]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47671,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,sK1),k4_xboole_0(k1_xboole_0,sK1),X0)) = X0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_47658,c_47582]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_46722,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),X2)) = k3_tarski(k1_enumset1(X2,X2,k1_xboole_0)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_1828,c_13845]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47646,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),X2)) = X2 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_46722,c_47345]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47647,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k4_xboole_0(X0,X0),X1),k4_xboole_0(k4_xboole_0(X0,X0),X1),X2)) = X2 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_47646,c_909]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47648,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0),X1)) = X1 ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_47647,c_1828]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47680,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_47671,c_47508,c_47648]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47741,plain,
% 44.08/6.00      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_46662,c_1828,c_47680]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47742,plain,
% 44.08/6.00      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_47741,c_563]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47776,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 44.08/6.00      inference(demodulation,
% 44.08/6.00                [status(thm)],
% 44.08/6.00                [c_46622,c_47508,c_47658,c_47742]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_47777,plain,
% 44.08/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_47776,c_1861]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_84130,plain,
% 44.08/6.00      ( sP0_iProver_split(X0,sK0,k1_xboole_0) = k4_xboole_0(X0,sK0) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_84129,c_47777]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_84957,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(sK0,k4_xboole_0(X0,sK0)) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_83858,c_84130]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_84958,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) = k3_tarski(k1_enumset1(sK0,sK0,X0)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_84957,c_4]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_87575,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK0)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_2451,c_84958]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_87638,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(sK0,sK0,sK0)) = k4_subset_1(sK0,sK0,sK1) ),
% 44.08/6.00      inference(light_normalisation,[status(thm)],[c_87575,c_3434]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_87639,plain,
% 44.08/6.00      ( k4_subset_1(sK0,sK0,sK1) = sK0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_87638,c_424]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_1493,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k4_subset_1(sK0,sK1,sK0) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_501,c_1404]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3768,plain,
% 44.08/6.00      ( k4_subset_1(sK0,sK0,sK1) = k4_subset_1(sK0,sK1,sK0) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_3434,c_1493]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_1401,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,X0))) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,X0))
% 44.08/6.00      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_210,c_1114]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_1585,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
% 44.08/6.00      inference(superposition,[status(thm)],[c_206,c_1401]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_2090,plain,
% 44.08/6.00      ( k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_1826,c_1585]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_2093,plain,
% 44.08/6.00      ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_subset_1(sK0,sK1,sK0) ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_2090,c_688,c_1404]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_11,negated_conjecture,
% 44.08/6.00      ( k3_subset_1(sK0,k1_xboole_0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
% 44.08/6.00      inference(cnf_transformation,[],[f52]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_212,plain,
% 44.08/6.00      ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != sK0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_11,c_5]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_2092,plain,
% 44.08/6.00      ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) != sK0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_1826,c_212]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_2094,plain,
% 44.08/6.00      ( k4_subset_1(sK0,sK1,sK0) != sK0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_2093,c_2092]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(c_3778,plain,
% 44.08/6.00      ( k4_subset_1(sK0,sK0,sK1) != sK0 ),
% 44.08/6.00      inference(demodulation,[status(thm)],[c_3768,c_2094]) ).
% 44.08/6.00  
% 44.08/6.00  cnf(contradiction,plain,
% 44.08/6.00      ( $false ),
% 44.08/6.00      inference(minisat,[status(thm)],[c_87639,c_3778]) ).
% 44.08/6.00  
% 44.08/6.00  
% 44.08/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 44.08/6.00  
% 44.08/6.00  ------                               Statistics
% 44.08/6.00  
% 44.08/6.00  ------ General
% 44.08/6.00  
% 44.08/6.00  abstr_ref_over_cycles:                  0
% 44.08/6.00  abstr_ref_under_cycles:                 0
% 44.08/6.00  gc_basic_clause_elim:                   0
% 44.08/6.00  forced_gc_time:                         0
% 44.08/6.00  parsing_time:                           0.01
% 44.08/6.00  unif_index_cands_time:                  0.
% 44.08/6.00  unif_index_add_time:                    0.
% 44.08/6.00  orderings_time:                         0.
% 44.08/6.00  out_proof_time:                         0.026
% 44.08/6.00  total_time:                             5.481
% 44.08/6.00  num_of_symbols:                         43
% 44.08/6.00  num_of_terms:                           257129
% 44.08/6.00  
% 44.08/6.00  ------ Preprocessing
% 44.08/6.00  
% 44.08/6.00  num_of_splits:                          0
% 44.08/6.00  num_of_split_atoms:                     1
% 44.08/6.00  num_of_reused_defs:                     0
% 44.08/6.00  num_eq_ax_congr_red:                    8
% 44.08/6.00  num_of_sem_filtered_clauses:            1
% 44.08/6.00  num_of_subtypes:                        0
% 44.08/6.00  monotx_restored_types:                  0
% 44.08/6.00  sat_num_of_epr_types:                   0
% 44.08/6.00  sat_num_of_non_cyclic_types:            0
% 44.08/6.00  sat_guarded_non_collapsed_types:        0
% 44.08/6.00  num_pure_diseq_elim:                    0
% 44.08/6.00  simp_replaced_by:                       0
% 44.08/6.00  res_preprocessed:                       58
% 44.08/6.00  prep_upred:                             0
% 44.08/6.00  prep_unflattend:                        0
% 44.08/6.00  smt_new_axioms:                         0
% 44.08/6.00  pred_elim_cands:                        1
% 44.08/6.00  pred_elim:                              0
% 44.08/6.00  pred_elim_cl:                           0
% 44.08/6.00  pred_elim_cycles:                       1
% 44.08/6.00  merged_defs:                            0
% 44.08/6.00  merged_defs_ncl:                        0
% 44.08/6.00  bin_hyper_res:                          0
% 44.08/6.00  prep_cycles:                            3
% 44.08/6.00  pred_elim_time:                         0.
% 44.08/6.00  splitting_time:                         0.
% 44.08/6.00  sem_filter_time:                        0.
% 44.08/6.00  monotx_time:                            0.
% 44.08/6.00  subtype_inf_time:                       0.
% 44.08/6.00  
% 44.08/6.00  ------ Problem properties
% 44.08/6.00  
% 44.08/6.00  clauses:                                13
% 44.08/6.00  conjectures:                            2
% 44.08/6.00  epr:                                    0
% 44.08/6.00  horn:                                   13
% 44.08/6.00  ground:                                 2
% 44.08/6.00  unary:                                  9
% 44.08/6.00  binary:                                 3
% 44.08/6.00  lits:                                   18
% 44.08/6.00  lits_eq:                                10
% 44.08/6.00  fd_pure:                                0
% 44.08/6.00  fd_pseudo:                              0
% 44.08/6.00  fd_cond:                                0
% 44.08/6.00  fd_pseudo_cond:                         0
% 44.08/6.00  ac_symbols:                             0
% 44.08/6.00  
% 44.08/6.00  ------ Propositional Solver
% 44.08/6.00  
% 44.08/6.00  prop_solver_calls:                      30
% 44.08/6.00  prop_fast_solver_calls:                 540
% 44.08/6.00  smt_solver_calls:                       0
% 44.08/6.00  smt_fast_solver_calls:                  0
% 44.08/6.00  prop_num_of_clauses:                    21448
% 44.08/6.00  prop_preprocess_simplified:             14290
% 44.08/6.00  prop_fo_subsumed:                       2
% 44.08/6.00  prop_solver_time:                       0.
% 44.08/6.00  smt_solver_time:                        0.
% 44.08/6.00  smt_fast_solver_time:                   0.
% 44.08/6.00  prop_fast_solver_time:                  0.
% 44.08/6.00  prop_unsat_core_time:                   0.002
% 44.08/6.00  
% 44.08/6.00  ------ QBF
% 44.08/6.00  
% 44.08/6.00  qbf_q_res:                              0
% 44.08/6.00  qbf_num_tautologies:                    0
% 44.08/6.00  qbf_prep_cycles:                        0
% 44.08/6.00  
% 44.08/6.00  ------ BMC1
% 44.08/6.00  
% 44.08/6.00  bmc1_current_bound:                     -1
% 44.08/6.00  bmc1_last_solved_bound:                 -1
% 44.08/6.00  bmc1_unsat_core_size:                   -1
% 44.08/6.00  bmc1_unsat_core_parents_size:           -1
% 44.08/6.00  bmc1_merge_next_fun:                    0
% 44.08/6.00  bmc1_unsat_core_clauses_time:           0.
% 44.08/6.00  
% 44.08/6.00  ------ Instantiation
% 44.08/6.00  
% 44.08/6.00  inst_num_of_clauses:                    3801
% 44.08/6.00  inst_num_in_passive:                    1979
% 44.08/6.00  inst_num_in_active:                     1137
% 44.08/6.00  inst_num_in_unprocessed:                685
% 44.08/6.00  inst_num_of_loops:                      1260
% 44.08/6.00  inst_num_of_learning_restarts:          0
% 44.08/6.00  inst_num_moves_active_passive:          118
% 44.08/6.00  inst_lit_activity:                      0
% 44.08/6.00  inst_lit_activity_moves:                0
% 44.08/6.00  inst_num_tautologies:                   0
% 44.08/6.00  inst_num_prop_implied:                  0
% 44.08/6.00  inst_num_existing_simplified:           0
% 44.08/6.00  inst_num_eq_res_simplified:             0
% 44.08/6.00  inst_num_child_elim:                    0
% 44.08/6.00  inst_num_of_dismatching_blockings:      750
% 44.08/6.00  inst_num_of_non_proper_insts:           4303
% 44.08/6.00  inst_num_of_duplicates:                 0
% 44.08/6.00  inst_inst_num_from_inst_to_res:         0
% 44.08/6.00  inst_dismatching_checking_time:         0.
% 44.08/6.00  
% 44.08/6.00  ------ Resolution
% 44.08/6.00  
% 44.08/6.00  res_num_of_clauses:                     0
% 44.08/6.00  res_num_in_passive:                     0
% 44.08/6.00  res_num_in_active:                      0
% 44.08/6.00  res_num_of_loops:                       61
% 44.08/6.00  res_forward_subset_subsumed:            922
% 44.08/6.00  res_backward_subset_subsumed:           4
% 44.08/6.00  res_forward_subsumed:                   0
% 44.08/6.00  res_backward_subsumed:                  0
% 44.08/6.00  res_forward_subsumption_resolution:     0
% 44.08/6.00  res_backward_subsumption_resolution:    0
% 44.08/6.00  res_clause_to_clause_subsumption:       151171
% 44.08/6.00  res_orphan_elimination:                 0
% 44.08/6.00  res_tautology_del:                      397
% 44.08/6.00  res_num_eq_res_simplified:              0
% 44.08/6.00  res_num_sel_changes:                    0
% 44.08/6.00  res_moves_from_active_to_pass:          0
% 44.08/6.00  
% 44.08/6.00  ------ Superposition
% 44.08/6.00  
% 44.08/6.00  sup_time_total:                         0.
% 44.08/6.00  sup_time_generating:                    0.
% 44.08/6.00  sup_time_sim_full:                      0.
% 44.08/6.00  sup_time_sim_immed:                     0.
% 44.08/6.00  
% 44.08/6.00  sup_num_of_clauses:                     8539
% 44.08/6.00  sup_num_in_active:                      226
% 44.08/6.00  sup_num_in_passive:                     8313
% 44.08/6.00  sup_num_of_loops:                       251
% 44.08/6.00  sup_fw_superposition:                   18144
% 44.08/6.00  sup_bw_superposition:                   10290
% 44.08/6.00  sup_immediate_simplified:               22997
% 44.08/6.00  sup_given_eliminated:                   7
% 44.08/6.00  comparisons_done:                       0
% 44.08/6.00  comparisons_avoided:                    0
% 44.08/6.00  
% 44.08/6.00  ------ Simplifications
% 44.08/6.00  
% 44.08/6.00  
% 44.08/6.00  sim_fw_subset_subsumed:                 3
% 44.08/6.00  sim_bw_subset_subsumed:                 0
% 44.08/6.00  sim_fw_subsumed:                        2134
% 44.08/6.00  sim_bw_subsumed:                        370
% 44.08/6.00  sim_fw_subsumption_res:                 0
% 44.08/6.00  sim_bw_subsumption_res:                 0
% 44.08/6.00  sim_tautology_del:                      0
% 44.08/6.00  sim_eq_tautology_del:                   3844
% 44.08/6.00  sim_eq_res_simp:                        0
% 44.08/6.00  sim_fw_demodulated:                     26586
% 44.08/6.00  sim_bw_demodulated:                     1043
% 44.08/6.00  sim_light_normalised:                   10430
% 44.08/6.00  sim_joinable_taut:                      0
% 44.08/6.00  sim_joinable_simp:                      0
% 44.08/6.00  sim_ac_normalised:                      0
% 44.08/6.00  sim_smt_subsumption:                    0
% 44.08/6.00  
%------------------------------------------------------------------------------
