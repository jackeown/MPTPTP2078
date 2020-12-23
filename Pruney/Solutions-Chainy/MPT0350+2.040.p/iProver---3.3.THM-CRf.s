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
% DateTime   : Thu Dec  3 11:39:12 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 432 expanded)
%              Number of clauses        :   60 ( 107 expanded)
%              Number of leaves         :   19 ( 117 expanded)
%              Depth                    :   18
%              Number of atoms          :  179 ( 653 expanded)
%              Number of equality atoms :  141 ( 457 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f43])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f48,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f45,f45])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f26,f45,f45])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f30,f45])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f27,f45])).

fof(f42,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_192,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_196,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4530,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_192,c_196])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_195,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4720,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4530,c_195])).

cnf(c_13,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7045,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4720,c_13])).

cnf(c_7050,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_7045,c_196])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_194,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4516,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_192,c_194])).

cnf(c_4660,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4530,c_4516])).

cnf(c_7065,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_7050,c_4660])).

cnf(c_2,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7965,plain,
    ( k3_tarski(k3_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) = k3_tarski(k3_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_7065,c_2])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_193,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1337,plain,
    ( k3_tarski(k3_enumset1(k3_subset_1(X0,X1),k3_subset_1(X0,X1),k3_subset_1(X0,X1),k3_subset_1(X0,X1),X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_195,c_193])).

cnf(c_3038,plain,
    ( k3_tarski(k3_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),X0)) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_192,c_1337])).

cnf(c_3575,plain,
    ( k3_tarski(k3_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),sK1)) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_192,c_3038])).

cnf(c_0,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3680,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_3575,c_0])).

cnf(c_492,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0)) = k4_subset_1(sK0,sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_192,c_193])).

cnf(c_1338,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_subset_1(sK0,X0))) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_195,c_492])).

cnf(c_1912,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_192,c_1338])).

cnf(c_3685,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_3680,c_1912])).

cnf(c_3687,plain,
    ( k3_tarski(k3_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),sK1)) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_3685,c_3575])).

cnf(c_4663,plain,
    ( k3_tarski(k3_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_4530,c_3687])).

cnf(c_8020,plain,
    ( k3_tarski(k3_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_7965,c_4663])).

cnf(c_16786,plain,
    ( k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_8020,c_0])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_402,plain,
    ( k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_964,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_402,c_4])).

cnf(c_1119,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_964,c_2])).

cnf(c_1,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1131,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1119,c_1])).

cnf(c_16803,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_16786,c_1131])).

cnf(c_84,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3725,plain,
    ( X0 != X1
    | X0 = k4_subset_1(X2,sK1,k4_xboole_0(sK0,sK1))
    | k4_subset_1(X2,sK1,k4_xboole_0(sK0,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_3726,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) != sK0
    | sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3725])).

cnf(c_321,plain,
    ( X0 != X1
    | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != X1
    | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = X0 ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_1356,plain,
    ( X0 != k4_subset_1(X1,sK1,k4_xboole_0(sK0,sK1))
    | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = X0
    | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k4_subset_1(X1,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_1357,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = sK0
    | sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_92,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k4_subset_1(X0,X4,X2) = k4_subset_1(X1,X5,X3) ),
    theory(equality)).

cnf(c_323,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k4_subset_1(X0,X1,X2)
    | k3_subset_1(sK0,sK1) != X2
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_486,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k4_subset_1(X0,sK1,X1)
    | k3_subset_1(sK0,sK1) != X1
    | sK1 != sK1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_1073,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1))
    | k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | sK1 != sK1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_1074,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_83,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_308,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_251,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_11,negated_conjecture,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_205,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != sK0 ),
    inference(demodulation,[status(thm)],[c_11,c_6])).

cnf(c_102,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16803,c_3726,c_1357,c_1074,c_308,c_251,c_205,c_102,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:40:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.62/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.98  
% 3.62/0.98  ------  iProver source info
% 3.62/0.98  
% 3.62/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.98  git: non_committed_changes: false
% 3.62/0.98  git: last_make_outside_of_git: false
% 3.62/0.98  
% 3.62/0.98  ------ 
% 3.62/0.98  
% 3.62/0.98  ------ Input Options
% 3.62/0.98  
% 3.62/0.98  --out_options                           all
% 3.62/0.98  --tptp_safe_out                         true
% 3.62/0.98  --problem_path                          ""
% 3.62/0.98  --include_path                          ""
% 3.62/0.98  --clausifier                            res/vclausify_rel
% 3.62/0.98  --clausifier_options                    --mode clausify
% 3.62/0.98  --stdin                                 false
% 3.62/0.98  --stats_out                             all
% 3.62/0.98  
% 3.62/0.98  ------ General Options
% 3.62/0.98  
% 3.62/0.98  --fof                                   false
% 3.62/0.98  --time_out_real                         305.
% 3.62/0.98  --time_out_virtual                      -1.
% 3.62/0.98  --symbol_type_check                     false
% 3.62/0.98  --clausify_out                          false
% 3.62/0.98  --sig_cnt_out                           false
% 3.62/0.98  --trig_cnt_out                          false
% 3.62/0.98  --trig_cnt_out_tolerance                1.
% 3.62/0.98  --trig_cnt_out_sk_spl                   false
% 3.62/0.98  --abstr_cl_out                          false
% 3.62/0.98  
% 3.62/0.98  ------ Global Options
% 3.62/0.98  
% 3.62/0.98  --schedule                              default
% 3.62/0.98  --add_important_lit                     false
% 3.62/0.98  --prop_solver_per_cl                    1000
% 3.62/0.98  --min_unsat_core                        false
% 3.62/0.98  --soft_assumptions                      false
% 3.62/0.98  --soft_lemma_size                       3
% 3.62/0.98  --prop_impl_unit_size                   0
% 3.62/0.98  --prop_impl_unit                        []
% 3.62/0.98  --share_sel_clauses                     true
% 3.62/0.98  --reset_solvers                         false
% 3.62/0.98  --bc_imp_inh                            [conj_cone]
% 3.62/0.98  --conj_cone_tolerance                   3.
% 3.62/0.98  --extra_neg_conj                        none
% 3.62/0.98  --large_theory_mode                     true
% 3.62/0.98  --prolific_symb_bound                   200
% 3.62/0.98  --lt_threshold                          2000
% 3.62/0.98  --clause_weak_htbl                      true
% 3.62/0.98  --gc_record_bc_elim                     false
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing Options
% 3.62/0.98  
% 3.62/0.98  --preprocessing_flag                    true
% 3.62/0.98  --time_out_prep_mult                    0.1
% 3.62/0.98  --splitting_mode                        input
% 3.62/0.98  --splitting_grd                         true
% 3.62/0.98  --splitting_cvd                         false
% 3.62/0.98  --splitting_cvd_svl                     false
% 3.62/0.98  --splitting_nvd                         32
% 3.62/0.98  --sub_typing                            true
% 3.62/0.98  --prep_gs_sim                           true
% 3.62/0.98  --prep_unflatten                        true
% 3.62/0.98  --prep_res_sim                          true
% 3.62/0.98  --prep_upred                            true
% 3.62/0.98  --prep_sem_filter                       exhaustive
% 3.62/0.98  --prep_sem_filter_out                   false
% 3.62/0.98  --pred_elim                             true
% 3.62/0.98  --res_sim_input                         true
% 3.62/0.98  --eq_ax_congr_red                       true
% 3.62/0.98  --pure_diseq_elim                       true
% 3.62/0.98  --brand_transform                       false
% 3.62/0.98  --non_eq_to_eq                          false
% 3.62/0.98  --prep_def_merge                        true
% 3.62/0.98  --prep_def_merge_prop_impl              false
% 3.62/0.98  --prep_def_merge_mbd                    true
% 3.62/0.98  --prep_def_merge_tr_red                 false
% 3.62/0.98  --prep_def_merge_tr_cl                  false
% 3.62/0.98  --smt_preprocessing                     true
% 3.62/0.98  --smt_ac_axioms                         fast
% 3.62/0.98  --preprocessed_out                      false
% 3.62/0.98  --preprocessed_stats                    false
% 3.62/0.98  
% 3.62/0.98  ------ Abstraction refinement Options
% 3.62/0.98  
% 3.62/0.98  --abstr_ref                             []
% 3.62/0.98  --abstr_ref_prep                        false
% 3.62/0.98  --abstr_ref_until_sat                   false
% 3.62/0.98  --abstr_ref_sig_restrict                funpre
% 3.62/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/0.98  --abstr_ref_under                       []
% 3.62/0.98  
% 3.62/0.98  ------ SAT Options
% 3.62/0.98  
% 3.62/0.98  --sat_mode                              false
% 3.62/0.98  --sat_fm_restart_options                ""
% 3.62/0.98  --sat_gr_def                            false
% 3.62/0.98  --sat_epr_types                         true
% 3.62/0.98  --sat_non_cyclic_types                  false
% 3.62/0.98  --sat_finite_models                     false
% 3.62/0.98  --sat_fm_lemmas                         false
% 3.62/0.98  --sat_fm_prep                           false
% 3.62/0.98  --sat_fm_uc_incr                        true
% 3.62/0.98  --sat_out_model                         small
% 3.62/0.98  --sat_out_clauses                       false
% 3.62/0.98  
% 3.62/0.98  ------ QBF Options
% 3.62/0.98  
% 3.62/0.98  --qbf_mode                              false
% 3.62/0.98  --qbf_elim_univ                         false
% 3.62/0.98  --qbf_dom_inst                          none
% 3.62/0.98  --qbf_dom_pre_inst                      false
% 3.62/0.98  --qbf_sk_in                             false
% 3.62/0.98  --qbf_pred_elim                         true
% 3.62/0.98  --qbf_split                             512
% 3.62/0.98  
% 3.62/0.98  ------ BMC1 Options
% 3.62/0.98  
% 3.62/0.98  --bmc1_incremental                      false
% 3.62/0.98  --bmc1_axioms                           reachable_all
% 3.62/0.98  --bmc1_min_bound                        0
% 3.62/0.98  --bmc1_max_bound                        -1
% 3.62/0.98  --bmc1_max_bound_default                -1
% 3.62/0.98  --bmc1_symbol_reachability              true
% 3.62/0.98  --bmc1_property_lemmas                  false
% 3.62/0.98  --bmc1_k_induction                      false
% 3.62/0.98  --bmc1_non_equiv_states                 false
% 3.62/0.98  --bmc1_deadlock                         false
% 3.62/0.98  --bmc1_ucm                              false
% 3.62/0.98  --bmc1_add_unsat_core                   none
% 3.62/0.98  --bmc1_unsat_core_children              false
% 3.62/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/0.98  --bmc1_out_stat                         full
% 3.62/0.98  --bmc1_ground_init                      false
% 3.62/0.98  --bmc1_pre_inst_next_state              false
% 3.62/0.98  --bmc1_pre_inst_state                   false
% 3.62/0.98  --bmc1_pre_inst_reach_state             false
% 3.62/0.98  --bmc1_out_unsat_core                   false
% 3.62/0.98  --bmc1_aig_witness_out                  false
% 3.62/0.98  --bmc1_verbose                          false
% 3.62/0.98  --bmc1_dump_clauses_tptp                false
% 3.62/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.62/0.98  --bmc1_dump_file                        -
% 3.62/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.62/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.62/0.98  --bmc1_ucm_extend_mode                  1
% 3.62/0.98  --bmc1_ucm_init_mode                    2
% 3.62/0.98  --bmc1_ucm_cone_mode                    none
% 3.62/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.62/0.98  --bmc1_ucm_relax_model                  4
% 3.62/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.62/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/0.98  --bmc1_ucm_layered_model                none
% 3.62/0.98  --bmc1_ucm_max_lemma_size               10
% 3.62/0.98  
% 3.62/0.98  ------ AIG Options
% 3.62/0.98  
% 3.62/0.98  --aig_mode                              false
% 3.62/0.98  
% 3.62/0.98  ------ Instantiation Options
% 3.62/0.98  
% 3.62/0.98  --instantiation_flag                    true
% 3.62/0.98  --inst_sos_flag                         false
% 3.62/0.98  --inst_sos_phase                        true
% 3.62/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/0.98  --inst_lit_sel_side                     num_symb
% 3.62/0.98  --inst_solver_per_active                1400
% 3.62/0.98  --inst_solver_calls_frac                1.
% 3.62/0.98  --inst_passive_queue_type               priority_queues
% 3.62/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/0.98  --inst_passive_queues_freq              [25;2]
% 3.62/0.98  --inst_dismatching                      true
% 3.62/0.98  --inst_eager_unprocessed_to_passive     true
% 3.62/0.98  --inst_prop_sim_given                   true
% 3.62/0.98  --inst_prop_sim_new                     false
% 3.62/0.98  --inst_subs_new                         false
% 3.62/0.98  --inst_eq_res_simp                      false
% 3.62/0.98  --inst_subs_given                       false
% 3.62/0.98  --inst_orphan_elimination               true
% 3.62/0.98  --inst_learning_loop_flag               true
% 3.62/0.98  --inst_learning_start                   3000
% 3.62/0.98  --inst_learning_factor                  2
% 3.62/0.98  --inst_start_prop_sim_after_learn       3
% 3.62/0.98  --inst_sel_renew                        solver
% 3.62/0.98  --inst_lit_activity_flag                true
% 3.62/0.98  --inst_restr_to_given                   false
% 3.62/0.98  --inst_activity_threshold               500
% 3.62/0.98  --inst_out_proof                        true
% 3.62/0.98  
% 3.62/0.98  ------ Resolution Options
% 3.62/0.98  
% 3.62/0.98  --resolution_flag                       true
% 3.62/0.98  --res_lit_sel                           adaptive
% 3.62/0.98  --res_lit_sel_side                      none
% 3.62/0.98  --res_ordering                          kbo
% 3.62/0.98  --res_to_prop_solver                    active
% 3.62/0.98  --res_prop_simpl_new                    false
% 3.62/0.98  --res_prop_simpl_given                  true
% 3.62/0.98  --res_passive_queue_type                priority_queues
% 3.62/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/0.98  --res_passive_queues_freq               [15;5]
% 3.62/0.98  --res_forward_subs                      full
% 3.62/0.98  --res_backward_subs                     full
% 3.62/0.98  --res_forward_subs_resolution           true
% 3.62/0.98  --res_backward_subs_resolution          true
% 3.62/0.98  --res_orphan_elimination                true
% 3.62/0.98  --res_time_limit                        2.
% 3.62/0.98  --res_out_proof                         true
% 3.62/0.98  
% 3.62/0.98  ------ Superposition Options
% 3.62/0.98  
% 3.62/0.98  --superposition_flag                    true
% 3.62/0.98  --sup_passive_queue_type                priority_queues
% 3.62/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.62/0.98  --demod_completeness_check              fast
% 3.62/0.98  --demod_use_ground                      true
% 3.62/0.98  --sup_to_prop_solver                    passive
% 3.62/0.98  --sup_prop_simpl_new                    true
% 3.62/0.98  --sup_prop_simpl_given                  true
% 3.62/0.98  --sup_fun_splitting                     false
% 3.62/0.98  --sup_smt_interval                      50000
% 3.62/0.98  
% 3.62/0.98  ------ Superposition Simplification Setup
% 3.62/0.98  
% 3.62/0.98  --sup_indices_passive                   []
% 3.62/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_full_bw                           [BwDemod]
% 3.62/0.98  --sup_immed_triv                        [TrivRules]
% 3.62/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_immed_bw_main                     []
% 3.62/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.98  
% 3.62/0.98  ------ Combination Options
% 3.62/0.98  
% 3.62/0.98  --comb_res_mult                         3
% 3.62/0.98  --comb_sup_mult                         2
% 3.62/0.98  --comb_inst_mult                        10
% 3.62/0.98  
% 3.62/0.98  ------ Debug Options
% 3.62/0.98  
% 3.62/0.98  --dbg_backtrace                         false
% 3.62/0.98  --dbg_dump_prop_clauses                 false
% 3.62/0.98  --dbg_dump_prop_clauses_file            -
% 3.62/0.98  --dbg_out_stat                          false
% 3.62/0.98  ------ Parsing...
% 3.62/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.98  ------ Proving...
% 3.62/0.98  ------ Problem Properties 
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  clauses                                 13
% 3.62/0.98  conjectures                             2
% 3.62/0.98  EPR                                     0
% 3.62/0.98  Horn                                    13
% 3.62/0.98  unary                                   9
% 3.62/0.98  binary                                  3
% 3.62/0.98  lits                                    18
% 3.62/0.98  lits eq                                 11
% 3.62/0.98  fd_pure                                 0
% 3.62/0.98  fd_pseudo                               0
% 3.62/0.98  fd_cond                                 0
% 3.62/0.98  fd_pseudo_cond                          0
% 3.62/0.98  AC symbols                              0
% 3.62/0.98  
% 3.62/0.98  ------ Schedule dynamic 5 is on 
% 3.62/0.98  
% 3.62/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ 
% 3.62/0.98  Current options:
% 3.62/0.98  ------ 
% 3.62/0.98  
% 3.62/0.98  ------ Input Options
% 3.62/0.98  
% 3.62/0.98  --out_options                           all
% 3.62/0.98  --tptp_safe_out                         true
% 3.62/0.98  --problem_path                          ""
% 3.62/0.98  --include_path                          ""
% 3.62/0.98  --clausifier                            res/vclausify_rel
% 3.62/0.98  --clausifier_options                    --mode clausify
% 3.62/0.98  --stdin                                 false
% 3.62/0.98  --stats_out                             all
% 3.62/0.98  
% 3.62/0.98  ------ General Options
% 3.62/0.98  
% 3.62/0.98  --fof                                   false
% 3.62/0.98  --time_out_real                         305.
% 3.62/0.98  --time_out_virtual                      -1.
% 3.62/0.98  --symbol_type_check                     false
% 3.62/0.98  --clausify_out                          false
% 3.62/0.98  --sig_cnt_out                           false
% 3.62/0.98  --trig_cnt_out                          false
% 3.62/0.98  --trig_cnt_out_tolerance                1.
% 3.62/0.98  --trig_cnt_out_sk_spl                   false
% 3.62/0.98  --abstr_cl_out                          false
% 3.62/0.98  
% 3.62/0.98  ------ Global Options
% 3.62/0.98  
% 3.62/0.98  --schedule                              default
% 3.62/0.98  --add_important_lit                     false
% 3.62/0.98  --prop_solver_per_cl                    1000
% 3.62/0.98  --min_unsat_core                        false
% 3.62/0.98  --soft_assumptions                      false
% 3.62/0.98  --soft_lemma_size                       3
% 3.62/0.98  --prop_impl_unit_size                   0
% 3.62/0.98  --prop_impl_unit                        []
% 3.62/0.98  --share_sel_clauses                     true
% 3.62/0.98  --reset_solvers                         false
% 3.62/0.98  --bc_imp_inh                            [conj_cone]
% 3.62/0.98  --conj_cone_tolerance                   3.
% 3.62/0.98  --extra_neg_conj                        none
% 3.62/0.98  --large_theory_mode                     true
% 3.62/0.98  --prolific_symb_bound                   200
% 3.62/0.98  --lt_threshold                          2000
% 3.62/0.98  --clause_weak_htbl                      true
% 3.62/0.98  --gc_record_bc_elim                     false
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing Options
% 3.62/0.98  
% 3.62/0.98  --preprocessing_flag                    true
% 3.62/0.98  --time_out_prep_mult                    0.1
% 3.62/0.98  --splitting_mode                        input
% 3.62/0.98  --splitting_grd                         true
% 3.62/0.98  --splitting_cvd                         false
% 3.62/0.98  --splitting_cvd_svl                     false
% 3.62/0.98  --splitting_nvd                         32
% 3.62/0.98  --sub_typing                            true
% 3.62/0.98  --prep_gs_sim                           true
% 3.62/0.98  --prep_unflatten                        true
% 3.62/0.98  --prep_res_sim                          true
% 3.62/0.98  --prep_upred                            true
% 3.62/0.98  --prep_sem_filter                       exhaustive
% 3.62/0.98  --prep_sem_filter_out                   false
% 3.62/0.98  --pred_elim                             true
% 3.62/0.98  --res_sim_input                         true
% 3.62/0.98  --eq_ax_congr_red                       true
% 3.62/0.98  --pure_diseq_elim                       true
% 3.62/0.98  --brand_transform                       false
% 3.62/0.98  --non_eq_to_eq                          false
% 3.62/0.98  --prep_def_merge                        true
% 3.62/0.98  --prep_def_merge_prop_impl              false
% 3.62/0.98  --prep_def_merge_mbd                    true
% 3.62/0.98  --prep_def_merge_tr_red                 false
% 3.62/0.98  --prep_def_merge_tr_cl                  false
% 3.62/0.98  --smt_preprocessing                     true
% 3.62/0.98  --smt_ac_axioms                         fast
% 3.62/0.98  --preprocessed_out                      false
% 3.62/0.98  --preprocessed_stats                    false
% 3.62/0.98  
% 3.62/0.98  ------ Abstraction refinement Options
% 3.62/0.98  
% 3.62/0.98  --abstr_ref                             []
% 3.62/0.98  --abstr_ref_prep                        false
% 3.62/0.98  --abstr_ref_until_sat                   false
% 3.62/0.98  --abstr_ref_sig_restrict                funpre
% 3.62/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/0.98  --abstr_ref_under                       []
% 3.62/0.98  
% 3.62/0.98  ------ SAT Options
% 3.62/0.98  
% 3.62/0.98  --sat_mode                              false
% 3.62/0.98  --sat_fm_restart_options                ""
% 3.62/0.98  --sat_gr_def                            false
% 3.62/0.98  --sat_epr_types                         true
% 3.62/0.98  --sat_non_cyclic_types                  false
% 3.62/0.98  --sat_finite_models                     false
% 3.62/0.98  --sat_fm_lemmas                         false
% 3.62/0.98  --sat_fm_prep                           false
% 3.62/0.98  --sat_fm_uc_incr                        true
% 3.62/0.98  --sat_out_model                         small
% 3.62/0.98  --sat_out_clauses                       false
% 3.62/0.98  
% 3.62/0.98  ------ QBF Options
% 3.62/0.98  
% 3.62/0.98  --qbf_mode                              false
% 3.62/0.98  --qbf_elim_univ                         false
% 3.62/0.98  --qbf_dom_inst                          none
% 3.62/0.98  --qbf_dom_pre_inst                      false
% 3.62/0.98  --qbf_sk_in                             false
% 3.62/0.98  --qbf_pred_elim                         true
% 3.62/0.98  --qbf_split                             512
% 3.62/0.98  
% 3.62/0.98  ------ BMC1 Options
% 3.62/0.98  
% 3.62/0.98  --bmc1_incremental                      false
% 3.62/0.98  --bmc1_axioms                           reachable_all
% 3.62/0.98  --bmc1_min_bound                        0
% 3.62/0.98  --bmc1_max_bound                        -1
% 3.62/0.98  --bmc1_max_bound_default                -1
% 3.62/0.98  --bmc1_symbol_reachability              true
% 3.62/0.98  --bmc1_property_lemmas                  false
% 3.62/0.98  --bmc1_k_induction                      false
% 3.62/0.98  --bmc1_non_equiv_states                 false
% 3.62/0.98  --bmc1_deadlock                         false
% 3.62/0.98  --bmc1_ucm                              false
% 3.62/0.98  --bmc1_add_unsat_core                   none
% 3.62/0.98  --bmc1_unsat_core_children              false
% 3.62/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/0.98  --bmc1_out_stat                         full
% 3.62/0.98  --bmc1_ground_init                      false
% 3.62/0.98  --bmc1_pre_inst_next_state              false
% 3.62/0.98  --bmc1_pre_inst_state                   false
% 3.62/0.98  --bmc1_pre_inst_reach_state             false
% 3.62/0.98  --bmc1_out_unsat_core                   false
% 3.62/0.98  --bmc1_aig_witness_out                  false
% 3.62/0.98  --bmc1_verbose                          false
% 3.62/0.98  --bmc1_dump_clauses_tptp                false
% 3.62/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.62/0.98  --bmc1_dump_file                        -
% 3.62/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.62/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.62/0.98  --bmc1_ucm_extend_mode                  1
% 3.62/0.98  --bmc1_ucm_init_mode                    2
% 3.62/0.98  --bmc1_ucm_cone_mode                    none
% 3.62/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.62/0.98  --bmc1_ucm_relax_model                  4
% 3.62/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.62/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/0.98  --bmc1_ucm_layered_model                none
% 3.62/0.98  --bmc1_ucm_max_lemma_size               10
% 3.62/0.98  
% 3.62/0.98  ------ AIG Options
% 3.62/0.98  
% 3.62/0.98  --aig_mode                              false
% 3.62/0.98  
% 3.62/0.98  ------ Instantiation Options
% 3.62/0.98  
% 3.62/0.98  --instantiation_flag                    true
% 3.62/0.98  --inst_sos_flag                         false
% 3.62/0.98  --inst_sos_phase                        true
% 3.62/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/0.98  --inst_lit_sel_side                     none
% 3.62/0.98  --inst_solver_per_active                1400
% 3.62/0.98  --inst_solver_calls_frac                1.
% 3.62/0.98  --inst_passive_queue_type               priority_queues
% 3.62/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/0.98  --inst_passive_queues_freq              [25;2]
% 3.62/0.98  --inst_dismatching                      true
% 3.62/0.98  --inst_eager_unprocessed_to_passive     true
% 3.62/0.98  --inst_prop_sim_given                   true
% 3.62/0.98  --inst_prop_sim_new                     false
% 3.62/0.98  --inst_subs_new                         false
% 3.62/0.98  --inst_eq_res_simp                      false
% 3.62/0.98  --inst_subs_given                       false
% 3.62/0.98  --inst_orphan_elimination               true
% 3.62/0.98  --inst_learning_loop_flag               true
% 3.62/0.98  --inst_learning_start                   3000
% 3.62/0.98  --inst_learning_factor                  2
% 3.62/0.98  --inst_start_prop_sim_after_learn       3
% 3.62/0.98  --inst_sel_renew                        solver
% 3.62/0.98  --inst_lit_activity_flag                true
% 3.62/0.98  --inst_restr_to_given                   false
% 3.62/0.98  --inst_activity_threshold               500
% 3.62/0.98  --inst_out_proof                        true
% 3.62/0.98  
% 3.62/0.98  ------ Resolution Options
% 3.62/0.98  
% 3.62/0.98  --resolution_flag                       false
% 3.62/0.98  --res_lit_sel                           adaptive
% 3.62/0.98  --res_lit_sel_side                      none
% 3.62/0.98  --res_ordering                          kbo
% 3.62/0.98  --res_to_prop_solver                    active
% 3.62/0.98  --res_prop_simpl_new                    false
% 3.62/0.98  --res_prop_simpl_given                  true
% 3.62/0.98  --res_passive_queue_type                priority_queues
% 3.62/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/0.98  --res_passive_queues_freq               [15;5]
% 3.62/0.98  --res_forward_subs                      full
% 3.62/0.98  --res_backward_subs                     full
% 3.62/0.98  --res_forward_subs_resolution           true
% 3.62/0.98  --res_backward_subs_resolution          true
% 3.62/0.98  --res_orphan_elimination                true
% 3.62/0.98  --res_time_limit                        2.
% 3.62/0.98  --res_out_proof                         true
% 3.62/0.98  
% 3.62/0.98  ------ Superposition Options
% 3.62/0.98  
% 3.62/0.98  --superposition_flag                    true
% 3.62/0.98  --sup_passive_queue_type                priority_queues
% 3.62/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.62/0.98  --demod_completeness_check              fast
% 3.62/0.98  --demod_use_ground                      true
% 3.62/0.98  --sup_to_prop_solver                    passive
% 3.62/0.98  --sup_prop_simpl_new                    true
% 3.62/0.98  --sup_prop_simpl_given                  true
% 3.62/0.98  --sup_fun_splitting                     false
% 3.62/0.98  --sup_smt_interval                      50000
% 3.62/0.98  
% 3.62/0.98  ------ Superposition Simplification Setup
% 3.62/0.98  
% 3.62/0.98  --sup_indices_passive                   []
% 3.62/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_full_bw                           [BwDemod]
% 3.62/0.98  --sup_immed_triv                        [TrivRules]
% 3.62/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_immed_bw_main                     []
% 3.62/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/0.98  
% 3.62/0.98  ------ Combination Options
% 3.62/0.98  
% 3.62/0.98  --comb_res_mult                         3
% 3.62/0.98  --comb_sup_mult                         2
% 3.62/0.98  --comb_inst_mult                        10
% 3.62/0.98  
% 3.62/0.98  ------ Debug Options
% 3.62/0.98  
% 3.62/0.98  --dbg_backtrace                         false
% 3.62/0.98  --dbg_dump_prop_clauses                 false
% 3.62/0.98  --dbg_dump_prop_clauses_file            -
% 3.62/0.98  --dbg_out_stat                          false
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ Proving...
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  % SZS status Theorem for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  fof(f16,conjecture,(
% 3.62/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f17,negated_conjecture,(
% 3.62/0.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 3.62/0.98    inference(negated_conjecture,[],[f16])).
% 3.62/0.98  
% 3.62/0.98  fof(f23,plain,(
% 3.62/0.98    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f17])).
% 3.62/0.98  
% 3.62/0.98  fof(f24,plain,(
% 3.62/0.98    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f25,plain,(
% 3.62/0.98    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 3.62/0.98  
% 3.62/0.98  fof(f41,plain,(
% 3.62/0.98    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.62/0.98    inference(cnf_transformation,[],[f25])).
% 3.62/0.98  
% 3.62/0.98  fof(f12,axiom,(
% 3.62/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f18,plain,(
% 3.62/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f12])).
% 3.62/0.98  
% 3.62/0.98  fof(f37,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f18])).
% 3.62/0.98  
% 3.62/0.98  fof(f13,axiom,(
% 3.62/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f19,plain,(
% 3.62/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f13])).
% 3.62/0.98  
% 3.62/0.98  fof(f38,plain,(
% 3.62/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f19])).
% 3.62/0.98  
% 3.62/0.98  fof(f14,axiom,(
% 3.62/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f20,plain,(
% 3.62/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f14])).
% 3.62/0.98  
% 3.62/0.98  fof(f39,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f20])).
% 3.62/0.98  
% 3.62/0.98  fof(f3,axiom,(
% 3.62/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f28,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f3])).
% 3.62/0.98  
% 3.62/0.98  fof(f10,axiom,(
% 3.62/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f35,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f10])).
% 3.62/0.98  
% 3.62/0.98  fof(f7,axiom,(
% 3.62/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f32,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f7])).
% 3.62/0.98  
% 3.62/0.98  fof(f8,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f33,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f8])).
% 3.62/0.98  
% 3.62/0.98  fof(f9,axiom,(
% 3.62/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f34,plain,(
% 3.62/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f9])).
% 3.62/0.98  
% 3.62/0.98  fof(f43,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.62/0.98    inference(definition_unfolding,[],[f33,f34])).
% 3.62/0.98  
% 3.62/0.98  fof(f44,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.62/0.98    inference(definition_unfolding,[],[f32,f43])).
% 3.62/0.98  
% 3.62/0.98  fof(f45,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.62/0.98    inference(definition_unfolding,[],[f35,f44])).
% 3.62/0.98  
% 3.62/0.98  fof(f48,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 3.62/0.98    inference(definition_unfolding,[],[f28,f45,f45])).
% 3.62/0.98  
% 3.62/0.98  fof(f15,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f21,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.62/0.98    inference(ennf_transformation,[],[f15])).
% 3.62/0.98  
% 3.62/0.98  fof(f22,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/0.98    inference(flattening,[],[f21])).
% 3.62/0.98  
% 3.62/0.98  fof(f40,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f22])).
% 3.62/0.98  
% 3.62/0.98  fof(f51,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/0.98    inference(definition_unfolding,[],[f40,f45])).
% 3.62/0.98  
% 3.62/0.98  fof(f1,axiom,(
% 3.62/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f26,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f1])).
% 3.62/0.98  
% 3.62/0.98  fof(f46,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 3.62/0.98    inference(definition_unfolding,[],[f26,f45,f45])).
% 3.62/0.98  
% 3.62/0.98  fof(f6,axiom,(
% 3.62/0.98    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f31,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f6])).
% 3.62/0.98  
% 3.62/0.98  fof(f50,plain,(
% 3.62/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 3.62/0.98    inference(definition_unfolding,[],[f31,f45])).
% 3.62/0.98  
% 3.62/0.98  fof(f5,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f30,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f5])).
% 3.62/0.98  
% 3.62/0.98  fof(f49,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 3.62/0.98    inference(definition_unfolding,[],[f30,f45])).
% 3.62/0.98  
% 3.62/0.98  fof(f2,axiom,(
% 3.62/0.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f27,plain,(
% 3.62/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.62/0.98    inference(cnf_transformation,[],[f2])).
% 3.62/0.98  
% 3.62/0.98  fof(f47,plain,(
% 3.62/0.98    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.62/0.98    inference(definition_unfolding,[],[f27,f45])).
% 3.62/0.98  
% 3.62/0.98  fof(f42,plain,(
% 3.62/0.98    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 3.62/0.98    inference(cnf_transformation,[],[f25])).
% 3.62/0.98  
% 3.62/0.98  fof(f11,axiom,(
% 3.62/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f36,plain,(
% 3.62/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.62/0.98    inference(cnf_transformation,[],[f11])).
% 3.62/0.98  
% 3.62/0.98  cnf(c_12,negated_conjecture,
% 3.62/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 3.62/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_192,plain,
% 3.62/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/0.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_196,plain,
% 3.62/0.98      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4530,plain,
% 3.62/0.98      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_192,c_196]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_8,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.62/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_195,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.62/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4720,plain,
% 3.62/0.98      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
% 3.62/0.98      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_4530,c_195]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_13,plain,
% 3.62/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7045,plain,
% 3.62/0.98      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_4720,c_13]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7050,plain,
% 3.62/0.98      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_7045,c_196]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_9,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/0.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.62/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_194,plain,
% 3.62/0.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4516,plain,
% 3.62/0.98      ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_192,c_194]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4660,plain,
% 3.62/0.98      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_4530,c_4516]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7065,plain,
% 3.62/0.98      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 3.62/0.98      inference(light_normalisation,[status(thm)],[c_7050,c_4660]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 3.62/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7965,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) = k3_tarski(k3_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_7065,c_2]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_10,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.62/0.98      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_193,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1337,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(k3_subset_1(X0,X1),k3_subset_1(X0,X1),k3_subset_1(X0,X1),k3_subset_1(X0,X1),X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.62/0.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_195,c_193]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3038,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),X0)) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),X0)
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_192,c_1337]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3575,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),sK1)) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_192,c_3038]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_0,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 3.62/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3680,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3575,c_0]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_492,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0)) = k4_subset_1(sK0,sK1,X0)
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_192,c_193]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1338,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_subset_1(sK0,X0))) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,X0))
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_195,c_492]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1912,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_192,c_1338]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3685,plain,
% 3.62/0.98      ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
% 3.62/0.98      inference(light_normalisation,[status(thm)],[c_3680,c_1912]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3687,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),sK1)) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_3685,c_3575]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4663,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_4530,c_3687]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_8020,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
% 3.62/0.98      inference(light_normalisation,[status(thm)],[c_7965,c_4663]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_16786,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k4_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_8020,c_0]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5,plain,
% 3.62/0.98      ( k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 3.62/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_402,plain,
% 3.62/0.98      ( k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = k1_xboole_0 ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4,plain,
% 3.62/0.98      ( k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_964,plain,
% 3.62/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_402,c_4]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1119,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_964,c_2]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.62/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1131,plain,
% 3.62/0.98      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.62/0.98      inference(light_normalisation,[status(thm)],[c_1119,c_1]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_16803,plain,
% 3.62/0.98      ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = sK0 ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_16786,c_1131]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_84,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3725,plain,
% 3.62/0.98      ( X0 != X1
% 3.62/0.98      | X0 = k4_subset_1(X2,sK1,k4_xboole_0(sK0,sK1))
% 3.62/0.98      | k4_subset_1(X2,sK1,k4_xboole_0(sK0,sK1)) != X1 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_84]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3726,plain,
% 3.62/0.98      ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) != sK0
% 3.62/0.98      | sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
% 3.62/0.98      | sK0 != sK0 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_3725]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_321,plain,
% 3.62/0.98      ( X0 != X1
% 3.62/0.98      | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != X1
% 3.62/0.98      | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = X0 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_84]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1356,plain,
% 3.62/0.98      ( X0 != k4_subset_1(X1,sK1,k4_xboole_0(sK0,sK1))
% 3.62/0.98      | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = X0
% 3.62/0.98      | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k4_subset_1(X1,sK1,k4_xboole_0(sK0,sK1)) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_321]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1357,plain,
% 3.62/0.98      ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
% 3.62/0.98      | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = sK0
% 3.62/0.98      | sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_1356]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_92,plain,
% 3.62/0.98      ( X0 != X1
% 3.62/0.98      | X2 != X3
% 3.62/0.98      | X4 != X5
% 3.62/0.98      | k4_subset_1(X0,X4,X2) = k4_subset_1(X1,X5,X3) ),
% 3.62/0.98      theory(equality) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_323,plain,
% 3.62/0.98      ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k4_subset_1(X0,X1,X2)
% 3.62/0.98      | k3_subset_1(sK0,sK1) != X2
% 3.62/0.98      | sK1 != X1
% 3.62/0.98      | sK0 != X0 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_92]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_486,plain,
% 3.62/0.98      ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k4_subset_1(X0,sK1,X1)
% 3.62/0.98      | k3_subset_1(sK0,sK1) != X1
% 3.62/0.98      | sK1 != sK1
% 3.62/0.98      | sK0 != X0 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_323]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1073,plain,
% 3.62/0.98      ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k4_subset_1(X0,sK1,k4_xboole_0(sK0,sK1))
% 3.62/0.98      | k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
% 3.62/0.98      | sK1 != sK1
% 3.62/0.98      | sK0 != X0 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_486]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1074,plain,
% 3.62/0.98      ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
% 3.62/0.98      | k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
% 3.62/0.98      | sK1 != sK1
% 3.62/0.98      | sK0 != sK0 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_1073]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_83,plain,( X0 = X0 ),theory(equality) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_308,plain,
% 3.62/0.98      ( sK1 = sK1 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_83]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_251,plain,
% 3.62/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
% 3.62/0.98      | k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_11,negated_conjecture,
% 3.62/0.98      ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
% 3.62/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_6,plain,
% 3.62/0.98      ( k2_subset_1(X0) = X0 ),
% 3.62/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_205,plain,
% 3.62/0.98      ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != sK0 ),
% 3.62/0.98      inference(demodulation,[status(thm)],[c_11,c_6]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_102,plain,
% 3.62/0.98      ( sK0 = sK0 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_83]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(contradiction,plain,
% 3.62/0.98      ( $false ),
% 3.62/0.98      inference(minisat,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_16803,c_3726,c_1357,c_1074,c_308,c_251,c_205,c_102,
% 3.62/0.98                 c_12]) ).
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  ------                               Statistics
% 3.62/0.98  
% 3.62/0.98  ------ General
% 3.62/0.98  
% 3.62/0.98  abstr_ref_over_cycles:                  0
% 3.62/0.98  abstr_ref_under_cycles:                 0
% 3.62/0.98  gc_basic_clause_elim:                   0
% 3.62/0.98  forced_gc_time:                         0
% 3.62/0.98  parsing_time:                           0.005
% 3.62/0.98  unif_index_cands_time:                  0.
% 3.62/0.98  unif_index_add_time:                    0.
% 3.62/0.98  orderings_time:                         0.
% 3.62/0.98  out_proof_time:                         0.007
% 3.62/0.98  total_time:                             0.494
% 3.62/0.98  num_of_symbols:                         42
% 3.62/0.98  num_of_terms:                           19728
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing
% 3.62/0.98  
% 3.62/0.98  num_of_splits:                          0
% 3.62/0.98  num_of_split_atoms:                     0
% 3.62/0.98  num_of_reused_defs:                     0
% 3.62/0.98  num_eq_ax_congr_red:                    8
% 3.62/0.98  num_of_sem_filtered_clauses:            1
% 3.62/0.98  num_of_subtypes:                        0
% 3.62/0.98  monotx_restored_types:                  0
% 3.62/0.98  sat_num_of_epr_types:                   0
% 3.62/0.98  sat_num_of_non_cyclic_types:            0
% 3.62/0.98  sat_guarded_non_collapsed_types:        0
% 3.62/0.98  num_pure_diseq_elim:                    0
% 3.62/0.98  simp_replaced_by:                       0
% 3.62/0.98  res_preprocessed:                       60
% 3.62/0.98  prep_upred:                             0
% 3.62/0.98  prep_unflattend:                        0
% 3.62/0.98  smt_new_axioms:                         0
% 3.62/0.98  pred_elim_cands:                        1
% 3.62/0.98  pred_elim:                              0
% 3.62/0.98  pred_elim_cl:                           0
% 3.62/0.98  pred_elim_cycles:                       1
% 3.62/0.98  merged_defs:                            0
% 3.62/0.98  merged_defs_ncl:                        0
% 3.62/0.98  bin_hyper_res:                          0
% 3.62/0.98  prep_cycles:                            3
% 3.62/0.98  pred_elim_time:                         0.
% 3.62/0.98  splitting_time:                         0.
% 3.62/0.98  sem_filter_time:                        0.
% 3.62/0.98  monotx_time:                            0.
% 3.62/0.98  subtype_inf_time:                       0.
% 3.62/0.99  
% 3.62/0.99  ------ Problem properties
% 3.62/0.99  
% 3.62/0.99  clauses:                                13
% 3.62/0.99  conjectures:                            2
% 3.62/0.99  epr:                                    0
% 3.62/0.99  horn:                                   13
% 3.62/0.99  ground:                                 2
% 3.62/0.99  unary:                                  9
% 3.62/0.99  binary:                                 3
% 3.62/0.99  lits:                                   18
% 3.62/0.99  lits_eq:                                11
% 3.62/0.99  fd_pure:                                0
% 3.62/0.99  fd_pseudo:                              0
% 3.62/0.99  fd_cond:                                0
% 3.62/0.99  fd_pseudo_cond:                         0
% 3.62/0.99  ac_symbols:                             0
% 3.62/0.99  
% 3.62/0.99  ------ Propositional Solver
% 3.62/0.99  
% 3.62/0.99  prop_solver_calls:                      24
% 3.62/0.99  prop_fast_solver_calls:                 370
% 3.62/0.99  smt_solver_calls:                       0
% 3.62/0.99  smt_fast_solver_calls:                  0
% 3.62/0.99  prop_num_of_clauses:                    4275
% 3.62/0.99  prop_preprocess_simplified:             8194
% 3.62/0.99  prop_fo_subsumed:                       1
% 3.62/0.99  prop_solver_time:                       0.
% 3.62/0.99  smt_solver_time:                        0.
% 3.62/0.99  smt_fast_solver_time:                   0.
% 3.62/0.99  prop_fast_solver_time:                  0.
% 3.62/0.99  prop_unsat_core_time:                   0.
% 3.62/0.99  
% 3.62/0.99  ------ QBF
% 3.62/0.99  
% 3.62/0.99  qbf_q_res:                              0
% 3.62/0.99  qbf_num_tautologies:                    0
% 3.62/0.99  qbf_prep_cycles:                        0
% 3.62/0.99  
% 3.62/0.99  ------ BMC1
% 3.62/0.99  
% 3.62/0.99  bmc1_current_bound:                     -1
% 3.62/0.99  bmc1_last_solved_bound:                 -1
% 3.62/0.99  bmc1_unsat_core_size:                   -1
% 3.62/0.99  bmc1_unsat_core_parents_size:           -1
% 3.62/0.99  bmc1_merge_next_fun:                    0
% 3.62/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.62/0.99  
% 3.62/0.99  ------ Instantiation
% 3.62/0.99  
% 3.62/0.99  inst_num_of_clauses:                    1427
% 3.62/0.99  inst_num_in_passive:                    316
% 3.62/0.99  inst_num_in_active:                     538
% 3.62/0.99  inst_num_in_unprocessed:                573
% 3.62/0.99  inst_num_of_loops:                      540
% 3.62/0.99  inst_num_of_learning_restarts:          0
% 3.62/0.99  inst_num_moves_active_passive:          0
% 3.62/0.99  inst_lit_activity:                      0
% 3.62/0.99  inst_lit_activity_moves:                0
% 3.62/0.99  inst_num_tautologies:                   0
% 3.62/0.99  inst_num_prop_implied:                  0
% 3.62/0.99  inst_num_existing_simplified:           0
% 3.62/0.99  inst_num_eq_res_simplified:             0
% 3.62/0.99  inst_num_child_elim:                    0
% 3.62/0.99  inst_num_of_dismatching_blockings:      50
% 3.62/0.99  inst_num_of_non_proper_insts:           1035
% 3.62/0.99  inst_num_of_duplicates:                 0
% 3.62/0.99  inst_inst_num_from_inst_to_res:         0
% 3.62/0.99  inst_dismatching_checking_time:         0.
% 3.62/0.99  
% 3.62/0.99  ------ Resolution
% 3.62/0.99  
% 3.62/0.99  res_num_of_clauses:                     0
% 3.62/0.99  res_num_in_passive:                     0
% 3.62/0.99  res_num_in_active:                      0
% 3.62/0.99  res_num_of_loops:                       63
% 3.62/0.99  res_forward_subset_subsumed:            97
% 3.62/0.99  res_backward_subset_subsumed:           0
% 3.62/0.99  res_forward_subsumed:                   0
% 3.62/0.99  res_backward_subsumed:                  0
% 3.62/0.99  res_forward_subsumption_resolution:     0
% 3.62/0.99  res_backward_subsumption_resolution:    0
% 3.62/0.99  res_clause_to_clause_subsumption:       9388
% 3.62/0.99  res_orphan_elimination:                 0
% 3.62/0.99  res_tautology_del:                      63
% 3.62/0.99  res_num_eq_res_simplified:              0
% 3.62/0.99  res_num_sel_changes:                    0
% 3.62/0.99  res_moves_from_active_to_pass:          0
% 3.62/0.99  
% 3.62/0.99  ------ Superposition
% 3.62/0.99  
% 3.62/0.99  sup_time_total:                         0.
% 3.62/0.99  sup_time_generating:                    0.
% 3.62/0.99  sup_time_sim_full:                      0.
% 3.62/0.99  sup_time_sim_immed:                     0.
% 3.62/0.99  
% 3.62/0.99  sup_num_of_clauses:                     716
% 3.62/0.99  sup_num_in_active:                      89
% 3.62/0.99  sup_num_in_passive:                     627
% 3.62/0.99  sup_num_of_loops:                       106
% 3.62/0.99  sup_fw_superposition:                   2128
% 3.62/0.99  sup_bw_superposition:                   2069
% 3.62/0.99  sup_immediate_simplified:               2383
% 3.62/0.99  sup_given_eliminated:                   2
% 3.62/0.99  comparisons_done:                       0
% 3.62/0.99  comparisons_avoided:                    0
% 3.62/0.99  
% 3.62/0.99  ------ Simplifications
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  sim_fw_subset_subsumed:                 2
% 3.62/0.99  sim_bw_subset_subsumed:                 0
% 3.62/0.99  sim_fw_subsumed:                        746
% 3.62/0.99  sim_bw_subsumed:                        11
% 3.62/0.99  sim_fw_subsumption_res:                 0
% 3.62/0.99  sim_bw_subsumption_res:                 0
% 3.62/0.99  sim_tautology_del:                      0
% 3.62/0.99  sim_eq_tautology_del:                   592
% 3.62/0.99  sim_eq_res_simp:                        0
% 3.62/0.99  sim_fw_demodulated:                     829
% 3.62/0.99  sim_bw_demodulated:                     39
% 3.62/0.99  sim_light_normalised:                   1224
% 3.62/0.99  sim_joinable_taut:                      0
% 3.62/0.99  sim_joinable_simp:                      0
% 3.62/0.99  sim_ac_normalised:                      0
% 3.62/0.99  sim_smt_subsumption:                    0
% 3.62/0.99  
%------------------------------------------------------------------------------
