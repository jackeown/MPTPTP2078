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
% DateTime   : Thu Dec  3 11:25:25 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 150 expanded)
%              Number of clauses        :   39 (  61 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 175 expanded)
%              Number of equality atoms :   86 ( 148 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f36,f35,f35])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f31,f43,f43])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f17])).

fof(f23,plain,(
    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1)
   => k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25])).

fof(f44,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
    inference(definition_unfolding,[],[f44,f35])).

cnf(c_10,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_335,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_336,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9359,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_335,c_336])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_333,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10239,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_9359,c_333])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_744,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_10268,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_10239,c_744])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_337,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_10269,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10268,c_337])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_119,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
    inference(resolution,[status(thm)],[c_2,c_6])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_338,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_119,c_4])).

cnf(c_10349,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_10269,c_338])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_345,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_731,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_14,c_13])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_501,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_736,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_731,c_501])).

cnf(c_909,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_736])).

cnf(c_1364,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_345,c_909])).

cnf(c_15473,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(X2,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10349,c_1364])).

cnf(c_1350,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_909,c_345])).

cnf(c_15503,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_15473,c_1350])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17245,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_15503,c_15])).

cnf(c_17249,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_17245,c_736])).

cnf(c_17250,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_17249])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:59:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.87/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/0.98  
% 3.87/0.98  ------  iProver source info
% 3.87/0.98  
% 3.87/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.87/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/0.98  git: non_committed_changes: false
% 3.87/0.98  git: last_make_outside_of_git: false
% 3.87/0.98  
% 3.87/0.98  ------ 
% 3.87/0.98  
% 3.87/0.98  ------ Input Options
% 3.87/0.98  
% 3.87/0.98  --out_options                           all
% 3.87/0.98  --tptp_safe_out                         true
% 3.87/0.98  --problem_path                          ""
% 3.87/0.98  --include_path                          ""
% 3.87/0.98  --clausifier                            res/vclausify_rel
% 3.87/0.98  --clausifier_options                    ""
% 3.87/0.98  --stdin                                 false
% 3.87/0.98  --stats_out                             all
% 3.87/0.98  
% 3.87/0.98  ------ General Options
% 3.87/0.98  
% 3.87/0.98  --fof                                   false
% 3.87/0.98  --time_out_real                         305.
% 3.87/0.98  --time_out_virtual                      -1.
% 3.87/0.98  --symbol_type_check                     false
% 3.87/0.98  --clausify_out                          false
% 3.87/0.98  --sig_cnt_out                           false
% 3.87/0.98  --trig_cnt_out                          false
% 3.87/0.98  --trig_cnt_out_tolerance                1.
% 3.87/0.98  --trig_cnt_out_sk_spl                   false
% 3.87/0.98  --abstr_cl_out                          false
% 3.87/0.98  
% 3.87/0.98  ------ Global Options
% 3.87/0.98  
% 3.87/0.98  --schedule                              default
% 3.87/0.98  --add_important_lit                     false
% 3.87/0.98  --prop_solver_per_cl                    1000
% 3.87/0.98  --min_unsat_core                        false
% 3.87/0.98  --soft_assumptions                      false
% 3.87/0.98  --soft_lemma_size                       3
% 3.87/0.98  --prop_impl_unit_size                   0
% 3.87/0.98  --prop_impl_unit                        []
% 3.87/0.98  --share_sel_clauses                     true
% 3.87/0.98  --reset_solvers                         false
% 3.87/0.98  --bc_imp_inh                            [conj_cone]
% 3.87/0.98  --conj_cone_tolerance                   3.
% 3.87/0.98  --extra_neg_conj                        none
% 3.87/0.98  --large_theory_mode                     true
% 3.87/0.98  --prolific_symb_bound                   200
% 3.87/0.98  --lt_threshold                          2000
% 3.87/0.98  --clause_weak_htbl                      true
% 3.87/0.98  --gc_record_bc_elim                     false
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing Options
% 3.87/0.98  
% 3.87/0.98  --preprocessing_flag                    true
% 3.87/0.98  --time_out_prep_mult                    0.1
% 3.87/0.98  --splitting_mode                        input
% 3.87/0.98  --splitting_grd                         true
% 3.87/0.98  --splitting_cvd                         false
% 3.87/0.98  --splitting_cvd_svl                     false
% 3.87/0.98  --splitting_nvd                         32
% 3.87/0.98  --sub_typing                            true
% 3.87/0.98  --prep_gs_sim                           true
% 3.87/0.98  --prep_unflatten                        true
% 3.87/0.98  --prep_res_sim                          true
% 3.87/0.98  --prep_upred                            true
% 3.87/0.98  --prep_sem_filter                       exhaustive
% 3.87/0.98  --prep_sem_filter_out                   false
% 3.87/0.98  --pred_elim                             true
% 3.87/0.98  --res_sim_input                         true
% 3.87/0.98  --eq_ax_congr_red                       true
% 3.87/0.98  --pure_diseq_elim                       true
% 3.87/0.98  --brand_transform                       false
% 3.87/0.98  --non_eq_to_eq                          false
% 3.87/0.98  --prep_def_merge                        true
% 3.87/0.98  --prep_def_merge_prop_impl              false
% 3.87/0.98  --prep_def_merge_mbd                    true
% 3.87/0.98  --prep_def_merge_tr_red                 false
% 3.87/0.98  --prep_def_merge_tr_cl                  false
% 3.87/0.98  --smt_preprocessing                     true
% 3.87/0.98  --smt_ac_axioms                         fast
% 3.87/0.98  --preprocessed_out                      false
% 3.87/0.98  --preprocessed_stats                    false
% 3.87/0.98  
% 3.87/0.98  ------ Abstraction refinement Options
% 3.87/0.98  
% 3.87/0.98  --abstr_ref                             []
% 3.87/0.98  --abstr_ref_prep                        false
% 3.87/0.98  --abstr_ref_until_sat                   false
% 3.87/0.98  --abstr_ref_sig_restrict                funpre
% 3.87/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/0.98  --abstr_ref_under                       []
% 3.87/0.98  
% 3.87/0.98  ------ SAT Options
% 3.87/0.98  
% 3.87/0.98  --sat_mode                              false
% 3.87/0.98  --sat_fm_restart_options                ""
% 3.87/0.98  --sat_gr_def                            false
% 3.87/0.98  --sat_epr_types                         true
% 3.87/0.98  --sat_non_cyclic_types                  false
% 3.87/0.98  --sat_finite_models                     false
% 3.87/0.98  --sat_fm_lemmas                         false
% 3.87/0.98  --sat_fm_prep                           false
% 3.87/0.98  --sat_fm_uc_incr                        true
% 3.87/0.98  --sat_out_model                         small
% 3.87/0.98  --sat_out_clauses                       false
% 3.87/0.98  
% 3.87/0.98  ------ QBF Options
% 3.87/0.98  
% 3.87/0.98  --qbf_mode                              false
% 3.87/0.98  --qbf_elim_univ                         false
% 3.87/0.98  --qbf_dom_inst                          none
% 3.87/0.98  --qbf_dom_pre_inst                      false
% 3.87/0.98  --qbf_sk_in                             false
% 3.87/0.98  --qbf_pred_elim                         true
% 3.87/0.98  --qbf_split                             512
% 3.87/0.98  
% 3.87/0.98  ------ BMC1 Options
% 3.87/0.98  
% 3.87/0.98  --bmc1_incremental                      false
% 3.87/0.98  --bmc1_axioms                           reachable_all
% 3.87/0.98  --bmc1_min_bound                        0
% 3.87/0.98  --bmc1_max_bound                        -1
% 3.87/0.98  --bmc1_max_bound_default                -1
% 3.87/0.98  --bmc1_symbol_reachability              true
% 3.87/0.98  --bmc1_property_lemmas                  false
% 3.87/0.98  --bmc1_k_induction                      false
% 3.87/0.98  --bmc1_non_equiv_states                 false
% 3.87/0.98  --bmc1_deadlock                         false
% 3.87/0.98  --bmc1_ucm                              false
% 3.87/0.98  --bmc1_add_unsat_core                   none
% 3.87/0.98  --bmc1_unsat_core_children              false
% 3.87/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/0.98  --bmc1_out_stat                         full
% 3.87/0.98  --bmc1_ground_init                      false
% 3.87/0.98  --bmc1_pre_inst_next_state              false
% 3.87/0.98  --bmc1_pre_inst_state                   false
% 3.87/0.98  --bmc1_pre_inst_reach_state             false
% 3.87/0.98  --bmc1_out_unsat_core                   false
% 3.87/0.98  --bmc1_aig_witness_out                  false
% 3.87/0.98  --bmc1_verbose                          false
% 3.87/0.98  --bmc1_dump_clauses_tptp                false
% 3.87/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.87/0.98  --bmc1_dump_file                        -
% 3.87/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.87/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.87/0.98  --bmc1_ucm_extend_mode                  1
% 3.87/0.98  --bmc1_ucm_init_mode                    2
% 3.87/0.98  --bmc1_ucm_cone_mode                    none
% 3.87/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.87/0.98  --bmc1_ucm_relax_model                  4
% 3.87/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.87/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/0.98  --bmc1_ucm_layered_model                none
% 3.87/0.98  --bmc1_ucm_max_lemma_size               10
% 3.87/0.98  
% 3.87/0.98  ------ AIG Options
% 3.87/0.98  
% 3.87/0.98  --aig_mode                              false
% 3.87/0.98  
% 3.87/0.98  ------ Instantiation Options
% 3.87/0.98  
% 3.87/0.98  --instantiation_flag                    true
% 3.87/0.98  --inst_sos_flag                         true
% 3.87/0.98  --inst_sos_phase                        true
% 3.87/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/0.98  --inst_lit_sel_side                     num_symb
% 3.87/0.98  --inst_solver_per_active                1400
% 3.87/0.98  --inst_solver_calls_frac                1.
% 3.87/0.98  --inst_passive_queue_type               priority_queues
% 3.87/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/0.98  --inst_passive_queues_freq              [25;2]
% 3.87/0.98  --inst_dismatching                      true
% 3.87/0.98  --inst_eager_unprocessed_to_passive     true
% 3.87/0.98  --inst_prop_sim_given                   true
% 3.87/0.98  --inst_prop_sim_new                     false
% 3.87/0.98  --inst_subs_new                         false
% 3.87/0.98  --inst_eq_res_simp                      false
% 3.87/0.98  --inst_subs_given                       false
% 3.87/0.98  --inst_orphan_elimination               true
% 3.87/0.98  --inst_learning_loop_flag               true
% 3.87/0.98  --inst_learning_start                   3000
% 3.87/0.98  --inst_learning_factor                  2
% 3.87/0.98  --inst_start_prop_sim_after_learn       3
% 3.87/0.98  --inst_sel_renew                        solver
% 3.87/0.98  --inst_lit_activity_flag                true
% 3.87/0.98  --inst_restr_to_given                   false
% 3.87/0.98  --inst_activity_threshold               500
% 3.87/0.98  --inst_out_proof                        true
% 3.87/0.98  
% 3.87/0.98  ------ Resolution Options
% 3.87/0.98  
% 3.87/0.98  --resolution_flag                       true
% 3.87/0.98  --res_lit_sel                           adaptive
% 3.87/0.98  --res_lit_sel_side                      none
% 3.87/0.98  --res_ordering                          kbo
% 3.87/0.98  --res_to_prop_solver                    active
% 3.87/0.98  --res_prop_simpl_new                    false
% 3.87/0.98  --res_prop_simpl_given                  true
% 3.87/0.98  --res_passive_queue_type                priority_queues
% 3.87/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/0.98  --res_passive_queues_freq               [15;5]
% 3.87/0.98  --res_forward_subs                      full
% 3.87/0.98  --res_backward_subs                     full
% 3.87/0.98  --res_forward_subs_resolution           true
% 3.87/0.98  --res_backward_subs_resolution          true
% 3.87/0.98  --res_orphan_elimination                true
% 3.87/0.98  --res_time_limit                        2.
% 3.87/0.98  --res_out_proof                         true
% 3.87/0.98  
% 3.87/0.98  ------ Superposition Options
% 3.87/0.98  
% 3.87/0.98  --superposition_flag                    true
% 3.87/0.98  --sup_passive_queue_type                priority_queues
% 3.87/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.87/0.98  --demod_completeness_check              fast
% 3.87/0.98  --demod_use_ground                      true
% 3.87/0.98  --sup_to_prop_solver                    passive
% 3.87/0.98  --sup_prop_simpl_new                    true
% 3.87/0.98  --sup_prop_simpl_given                  true
% 3.87/0.98  --sup_fun_splitting                     true
% 3.87/0.98  --sup_smt_interval                      50000
% 3.87/0.98  
% 3.87/0.98  ------ Superposition Simplification Setup
% 3.87/0.98  
% 3.87/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.87/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.87/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.87/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.87/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.87/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.87/0.98  --sup_immed_triv                        [TrivRules]
% 3.87/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.98  --sup_immed_bw_main                     []
% 3.87/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.87/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.98  --sup_input_bw                          []
% 3.87/0.98  
% 3.87/0.98  ------ Combination Options
% 3.87/0.98  
% 3.87/0.98  --comb_res_mult                         3
% 3.87/0.98  --comb_sup_mult                         2
% 3.87/0.98  --comb_inst_mult                        10
% 3.87/0.98  
% 3.87/0.98  ------ Debug Options
% 3.87/0.98  
% 3.87/0.98  --dbg_backtrace                         false
% 3.87/0.98  --dbg_dump_prop_clauses                 false
% 3.87/0.98  --dbg_dump_prop_clauses_file            -
% 3.87/0.98  --dbg_out_stat                          false
% 3.87/0.98  ------ Parsing...
% 3.87/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/0.98  ------ Proving...
% 3.87/0.98  ------ Problem Properties 
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  clauses                                 15
% 3.87/0.98  conjectures                             1
% 3.87/0.98  EPR                                     1
% 3.87/0.98  Horn                                    15
% 3.87/0.98  unary                                   11
% 3.87/0.98  binary                                  4
% 3.87/0.98  lits                                    19
% 3.87/0.98  lits eq                                 14
% 3.87/0.98  fd_pure                                 0
% 3.87/0.98  fd_pseudo                               0
% 3.87/0.98  fd_cond                                 0
% 3.87/0.98  fd_pseudo_cond                          0
% 3.87/0.98  AC symbols                              1
% 3.87/0.98  
% 3.87/0.98  ------ Schedule dynamic 5 is on 
% 3.87/0.98  
% 3.87/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  ------ 
% 3.87/0.98  Current options:
% 3.87/0.98  ------ 
% 3.87/0.98  
% 3.87/0.98  ------ Input Options
% 3.87/0.98  
% 3.87/0.98  --out_options                           all
% 3.87/0.98  --tptp_safe_out                         true
% 3.87/0.98  --problem_path                          ""
% 3.87/0.98  --include_path                          ""
% 3.87/0.98  --clausifier                            res/vclausify_rel
% 3.87/0.98  --clausifier_options                    ""
% 3.87/0.98  --stdin                                 false
% 3.87/0.98  --stats_out                             all
% 3.87/0.98  
% 3.87/0.98  ------ General Options
% 3.87/0.98  
% 3.87/0.98  --fof                                   false
% 3.87/0.98  --time_out_real                         305.
% 3.87/0.98  --time_out_virtual                      -1.
% 3.87/0.98  --symbol_type_check                     false
% 3.87/0.98  --clausify_out                          false
% 3.87/0.98  --sig_cnt_out                           false
% 3.87/0.98  --trig_cnt_out                          false
% 3.87/0.98  --trig_cnt_out_tolerance                1.
% 3.87/0.98  --trig_cnt_out_sk_spl                   false
% 3.87/0.98  --abstr_cl_out                          false
% 3.87/0.98  
% 3.87/0.98  ------ Global Options
% 3.87/0.98  
% 3.87/0.98  --schedule                              default
% 3.87/0.98  --add_important_lit                     false
% 3.87/0.98  --prop_solver_per_cl                    1000
% 3.87/0.98  --min_unsat_core                        false
% 3.87/0.98  --soft_assumptions                      false
% 3.87/0.98  --soft_lemma_size                       3
% 3.87/0.98  --prop_impl_unit_size                   0
% 3.87/0.98  --prop_impl_unit                        []
% 3.87/0.98  --share_sel_clauses                     true
% 3.87/0.98  --reset_solvers                         false
% 3.87/0.98  --bc_imp_inh                            [conj_cone]
% 3.87/0.98  --conj_cone_tolerance                   3.
% 3.87/0.98  --extra_neg_conj                        none
% 3.87/0.98  --large_theory_mode                     true
% 3.87/0.98  --prolific_symb_bound                   200
% 3.87/0.98  --lt_threshold                          2000
% 3.87/0.98  --clause_weak_htbl                      true
% 3.87/0.98  --gc_record_bc_elim                     false
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing Options
% 3.87/0.98  
% 3.87/0.98  --preprocessing_flag                    true
% 3.87/0.98  --time_out_prep_mult                    0.1
% 3.87/0.98  --splitting_mode                        input
% 3.87/0.98  --splitting_grd                         true
% 3.87/0.98  --splitting_cvd                         false
% 3.87/0.98  --splitting_cvd_svl                     false
% 3.87/0.98  --splitting_nvd                         32
% 3.87/0.98  --sub_typing                            true
% 3.87/0.98  --prep_gs_sim                           true
% 3.87/0.98  --prep_unflatten                        true
% 3.87/0.98  --prep_res_sim                          true
% 3.87/0.98  --prep_upred                            true
% 3.87/0.98  --prep_sem_filter                       exhaustive
% 3.87/0.98  --prep_sem_filter_out                   false
% 3.87/0.98  --pred_elim                             true
% 3.87/0.98  --res_sim_input                         true
% 3.87/0.98  --eq_ax_congr_red                       true
% 3.87/0.98  --pure_diseq_elim                       true
% 3.87/0.98  --brand_transform                       false
% 3.87/0.98  --non_eq_to_eq                          false
% 3.87/0.98  --prep_def_merge                        true
% 3.87/0.98  --prep_def_merge_prop_impl              false
% 3.87/0.98  --prep_def_merge_mbd                    true
% 3.87/0.98  --prep_def_merge_tr_red                 false
% 3.87/0.98  --prep_def_merge_tr_cl                  false
% 3.87/0.98  --smt_preprocessing                     true
% 3.87/0.98  --smt_ac_axioms                         fast
% 3.87/0.98  --preprocessed_out                      false
% 3.87/0.98  --preprocessed_stats                    false
% 3.87/0.98  
% 3.87/0.98  ------ Abstraction refinement Options
% 3.87/0.98  
% 3.87/0.98  --abstr_ref                             []
% 3.87/0.98  --abstr_ref_prep                        false
% 3.87/0.98  --abstr_ref_until_sat                   false
% 3.87/0.98  --abstr_ref_sig_restrict                funpre
% 3.87/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/0.98  --abstr_ref_under                       []
% 3.87/0.98  
% 3.87/0.98  ------ SAT Options
% 3.87/0.98  
% 3.87/0.98  --sat_mode                              false
% 3.87/0.98  --sat_fm_restart_options                ""
% 3.87/0.98  --sat_gr_def                            false
% 3.87/0.98  --sat_epr_types                         true
% 3.87/0.98  --sat_non_cyclic_types                  false
% 3.87/0.98  --sat_finite_models                     false
% 3.87/0.98  --sat_fm_lemmas                         false
% 3.87/0.98  --sat_fm_prep                           false
% 3.87/0.98  --sat_fm_uc_incr                        true
% 3.87/0.98  --sat_out_model                         small
% 3.87/0.98  --sat_out_clauses                       false
% 3.87/0.98  
% 3.87/0.98  ------ QBF Options
% 3.87/0.98  
% 3.87/0.98  --qbf_mode                              false
% 3.87/0.98  --qbf_elim_univ                         false
% 3.87/0.98  --qbf_dom_inst                          none
% 3.87/0.98  --qbf_dom_pre_inst                      false
% 3.87/0.98  --qbf_sk_in                             false
% 3.87/0.98  --qbf_pred_elim                         true
% 3.87/0.98  --qbf_split                             512
% 3.87/0.98  
% 3.87/0.98  ------ BMC1 Options
% 3.87/0.98  
% 3.87/0.98  --bmc1_incremental                      false
% 3.87/0.98  --bmc1_axioms                           reachable_all
% 3.87/0.98  --bmc1_min_bound                        0
% 3.87/0.98  --bmc1_max_bound                        -1
% 3.87/0.98  --bmc1_max_bound_default                -1
% 3.87/0.98  --bmc1_symbol_reachability              true
% 3.87/0.98  --bmc1_property_lemmas                  false
% 3.87/0.98  --bmc1_k_induction                      false
% 3.87/0.98  --bmc1_non_equiv_states                 false
% 3.87/0.98  --bmc1_deadlock                         false
% 3.87/0.98  --bmc1_ucm                              false
% 3.87/0.98  --bmc1_add_unsat_core                   none
% 3.87/0.98  --bmc1_unsat_core_children              false
% 3.87/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/0.98  --bmc1_out_stat                         full
% 3.87/0.98  --bmc1_ground_init                      false
% 3.87/0.98  --bmc1_pre_inst_next_state              false
% 3.87/0.98  --bmc1_pre_inst_state                   false
% 3.87/0.98  --bmc1_pre_inst_reach_state             false
% 3.87/0.98  --bmc1_out_unsat_core                   false
% 3.87/0.98  --bmc1_aig_witness_out                  false
% 3.87/0.98  --bmc1_verbose                          false
% 3.87/0.98  --bmc1_dump_clauses_tptp                false
% 3.87/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.87/0.98  --bmc1_dump_file                        -
% 3.87/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.87/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.87/0.98  --bmc1_ucm_extend_mode                  1
% 3.87/0.98  --bmc1_ucm_init_mode                    2
% 3.87/0.98  --bmc1_ucm_cone_mode                    none
% 3.87/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.87/0.98  --bmc1_ucm_relax_model                  4
% 3.87/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.87/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/0.98  --bmc1_ucm_layered_model                none
% 3.87/0.98  --bmc1_ucm_max_lemma_size               10
% 3.87/0.98  
% 3.87/0.98  ------ AIG Options
% 3.87/0.98  
% 3.87/0.98  --aig_mode                              false
% 3.87/0.98  
% 3.87/0.98  ------ Instantiation Options
% 3.87/0.98  
% 3.87/0.98  --instantiation_flag                    true
% 3.87/0.98  --inst_sos_flag                         true
% 3.87/0.98  --inst_sos_phase                        true
% 3.87/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/0.98  --inst_lit_sel_side                     none
% 3.87/0.98  --inst_solver_per_active                1400
% 3.87/0.98  --inst_solver_calls_frac                1.
% 3.87/0.98  --inst_passive_queue_type               priority_queues
% 3.87/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/0.98  --inst_passive_queues_freq              [25;2]
% 3.87/0.98  --inst_dismatching                      true
% 3.87/0.98  --inst_eager_unprocessed_to_passive     true
% 3.87/0.98  --inst_prop_sim_given                   true
% 3.87/0.98  --inst_prop_sim_new                     false
% 3.87/0.98  --inst_subs_new                         false
% 3.87/0.98  --inst_eq_res_simp                      false
% 3.87/0.98  --inst_subs_given                       false
% 3.87/0.98  --inst_orphan_elimination               true
% 3.87/0.98  --inst_learning_loop_flag               true
% 3.87/0.98  --inst_learning_start                   3000
% 3.87/0.98  --inst_learning_factor                  2
% 3.87/0.98  --inst_start_prop_sim_after_learn       3
% 3.87/0.98  --inst_sel_renew                        solver
% 3.87/0.98  --inst_lit_activity_flag                true
% 3.87/0.98  --inst_restr_to_given                   false
% 3.87/0.98  --inst_activity_threshold               500
% 3.87/0.98  --inst_out_proof                        true
% 3.87/0.98  
% 3.87/0.98  ------ Resolution Options
% 3.87/0.98  
% 3.87/0.98  --resolution_flag                       false
% 3.87/0.98  --res_lit_sel                           adaptive
% 3.87/0.98  --res_lit_sel_side                      none
% 3.87/0.98  --res_ordering                          kbo
% 3.87/0.98  --res_to_prop_solver                    active
% 3.87/0.98  --res_prop_simpl_new                    false
% 3.87/0.98  --res_prop_simpl_given                  true
% 3.87/0.98  --res_passive_queue_type                priority_queues
% 3.87/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/0.98  --res_passive_queues_freq               [15;5]
% 3.87/0.98  --res_forward_subs                      full
% 3.87/0.98  --res_backward_subs                     full
% 3.87/0.98  --res_forward_subs_resolution           true
% 3.87/0.98  --res_backward_subs_resolution          true
% 3.87/0.98  --res_orphan_elimination                true
% 3.87/0.98  --res_time_limit                        2.
% 3.87/0.98  --res_out_proof                         true
% 3.87/0.98  
% 3.87/0.98  ------ Superposition Options
% 3.87/0.98  
% 3.87/0.98  --superposition_flag                    true
% 3.87/0.98  --sup_passive_queue_type                priority_queues
% 3.87/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.87/0.98  --demod_completeness_check              fast
% 3.87/0.98  --demod_use_ground                      true
% 3.87/0.98  --sup_to_prop_solver                    passive
% 3.87/0.98  --sup_prop_simpl_new                    true
% 3.87/0.98  --sup_prop_simpl_given                  true
% 3.87/0.98  --sup_fun_splitting                     true
% 3.87/0.98  --sup_smt_interval                      50000
% 3.87/0.98  
% 3.87/0.98  ------ Superposition Simplification Setup
% 3.87/0.98  
% 3.87/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.87/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.87/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.87/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.87/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.87/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.87/0.98  --sup_immed_triv                        [TrivRules]
% 3.87/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.98  --sup_immed_bw_main                     []
% 3.87/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.87/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.98  --sup_input_bw                          []
% 3.87/0.98  
% 3.87/0.98  ------ Combination Options
% 3.87/0.98  
% 3.87/0.98  --comb_res_mult                         3
% 3.87/0.98  --comb_sup_mult                         2
% 3.87/0.98  --comb_inst_mult                        10
% 3.87/0.98  
% 3.87/0.98  ------ Debug Options
% 3.87/0.98  
% 3.87/0.98  --dbg_backtrace                         false
% 3.87/0.98  --dbg_dump_prop_clauses                 false
% 3.87/0.98  --dbg_dump_prop_clauses_file            -
% 3.87/0.98  --dbg_out_stat                          false
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  ------ Proving...
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  % SZS status Theorem for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98   Resolution empty clause
% 3.87/0.98  
% 3.87/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  fof(f12,axiom,(
% 3.87/0.98    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f38,plain,(
% 3.87/0.98    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f12])).
% 3.87/0.98  
% 3.87/0.98  fof(f2,axiom,(
% 3.87/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f20,plain,(
% 3.87/0.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.87/0.98    inference(ennf_transformation,[],[f2])).
% 3.87/0.98  
% 3.87/0.98  fof(f28,plain,(
% 3.87/0.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f20])).
% 3.87/0.98  
% 3.87/0.98  fof(f13,axiom,(
% 3.87/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f24,plain,(
% 3.87/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.87/0.98    inference(nnf_transformation,[],[f13])).
% 3.87/0.98  
% 3.87/0.98  fof(f39,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f24])).
% 3.87/0.98  
% 3.87/0.98  fof(f8,axiom,(
% 3.87/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f34,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f8])).
% 3.87/0.98  
% 3.87/0.98  fof(f9,axiom,(
% 3.87/0.98    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f35,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f9])).
% 3.87/0.98  
% 3.87/0.98  fof(f48,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.87/0.98    inference(definition_unfolding,[],[f34,f35])).
% 3.87/0.98  
% 3.87/0.98  fof(f10,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f36,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f10])).
% 3.87/0.98  
% 3.87/0.98  fof(f49,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.87/0.98    inference(definition_unfolding,[],[f36,f35,f35])).
% 3.87/0.98  
% 3.87/0.98  fof(f4,axiom,(
% 3.87/0.98    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f30,plain,(
% 3.87/0.98    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f4])).
% 3.87/0.98  
% 3.87/0.98  fof(f45,plain,(
% 3.87/0.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.87/0.98    inference(definition_unfolding,[],[f30,f35])).
% 3.87/0.98  
% 3.87/0.98  fof(f6,axiom,(
% 3.87/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f32,plain,(
% 3.87/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.87/0.98    inference(cnf_transformation,[],[f6])).
% 3.87/0.98  
% 3.87/0.98  fof(f3,axiom,(
% 3.87/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f19,plain,(
% 3.87/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 3.87/0.98    inference(unused_predicate_definition_removal,[],[f3])).
% 3.87/0.98  
% 3.87/0.98  fof(f21,plain,(
% 3.87/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 3.87/0.98    inference(ennf_transformation,[],[f19])).
% 3.87/0.98  
% 3.87/0.98  fof(f29,plain,(
% 3.87/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.87/0.98    inference(cnf_transformation,[],[f21])).
% 3.87/0.98  
% 3.87/0.98  fof(f7,axiom,(
% 3.87/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f22,plain,(
% 3.87/0.98    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 3.87/0.98    inference(ennf_transformation,[],[f7])).
% 3.87/0.98  
% 3.87/0.98  fof(f33,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f22])).
% 3.87/0.98  
% 3.87/0.98  fof(f16,axiom,(
% 3.87/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f43,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f16])).
% 3.87/0.98  
% 3.87/0.98  fof(f47,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.87/0.98    inference(definition_unfolding,[],[f33,f43])).
% 3.87/0.98  
% 3.87/0.98  fof(f5,axiom,(
% 3.87/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f31,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f5])).
% 3.87/0.98  
% 3.87/0.98  fof(f46,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 3.87/0.98    inference(definition_unfolding,[],[f31,f43,f43])).
% 3.87/0.98  
% 3.87/0.98  fof(f14,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f41,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f14])).
% 3.87/0.98  
% 3.87/0.98  fof(f1,axiom,(
% 3.87/0.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f27,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f1])).
% 3.87/0.98  
% 3.87/0.98  fof(f15,axiom,(
% 3.87/0.98    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f42,plain,(
% 3.87/0.98    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.87/0.98    inference(cnf_transformation,[],[f15])).
% 3.87/0.98  
% 3.87/0.98  fof(f11,axiom,(
% 3.87/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f37,plain,(
% 3.87/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.87/0.98    inference(cnf_transformation,[],[f11])).
% 3.87/0.98  
% 3.87/0.98  fof(f17,conjecture,(
% 3.87/0.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f18,negated_conjecture,(
% 3.87/0.98    ~! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.87/0.98    inference(negated_conjecture,[],[f17])).
% 3.87/0.98  
% 3.87/0.98  fof(f23,plain,(
% 3.87/0.98    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1)),
% 3.87/0.98    inference(ennf_transformation,[],[f18])).
% 3.87/0.98  
% 3.87/0.98  fof(f25,plain,(
% 3.87/0.98    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1) => k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1)),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f26,plain,(
% 3.87/0.98    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1)),
% 3.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25])).
% 3.87/0.98  
% 3.87/0.98  fof(f44,plain,(
% 3.87/0.98    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1)),
% 3.87/0.98    inference(cnf_transformation,[],[f26])).
% 3.87/0.98  
% 3.87/0.98  fof(f50,plain,(
% 3.87/0.98    k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1)),
% 3.87/0.98    inference(definition_unfolding,[],[f44,f35])).
% 3.87/0.98  
% 3.87/0.98  cnf(c_10,plain,
% 3.87/0.98      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.87/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_335,plain,
% 3.87/0.98      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1,plain,
% 3.87/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.87/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_336,plain,
% 3.87/0.98      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9359,plain,
% 3.87/0.98      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_335,c_336]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_12,plain,
% 3.87/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_333,plain,
% 3.87/0.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_10239,plain,
% 3.87/0.98      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_9359,c_333]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_7,plain,
% 3.87/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.87/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_8,plain,
% 3.87/0.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 3.87/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_744,plain,
% 3.87/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_10268,plain,
% 3.87/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_10239,c_744]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3,plain,
% 3.87/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_5,plain,
% 3.87/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_337,plain,
% 3.87/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.87/0.98      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_10269,plain,
% 3.87/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.87/0.98      inference(light_normalisation,[status(thm)],[c_10268,c_337]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_2,plain,
% 3.87/0.98      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_6,plain,
% 3.87/0.98      ( ~ r1_tarski(X0,X1)
% 3.87/0.98      | k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
% 3.87/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_119,plain,
% 3.87/0.98      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 3.87/0.98      | k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_2,c_6]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_4,plain,
% 3.87/0.98      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.87/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_338,plain,
% 3.87/0.98      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 3.87/0.98      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 3.87/0.98      inference(demodulation,[status(thm)],[c_119,c_4]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_10349,plain,
% 3.87/0.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_10269,c_338]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_13,plain,
% 3.87/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.87/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_0,plain,
% 3.87/0.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.87/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_345,plain,
% 3.87/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_14,plain,
% 3.87/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_731,plain,
% 3.87/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_14,c_13]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9,plain,
% 3.87/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_501,plain,
% 3.87/0.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_736,plain,
% 3.87/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 3.87/0.98      inference(demodulation,[status(thm)],[c_731,c_501]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_909,plain,
% 3.87/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_0,c_736]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1364,plain,
% 3.87/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_345,c_909]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_15473,plain,
% 3.87/0.98      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(X2,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_10349,c_1364]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1350,plain,
% 3.87/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_909,c_345]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_15503,plain,
% 3.87/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.87/0.98      inference(demodulation,[status(thm)],[c_15473,c_1350]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_15,negated_conjecture,
% 3.87/0.98      ( k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
% 3.87/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_17245,plain,
% 3.87/0.98      ( k5_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
% 3.87/0.98      inference(demodulation,[status(thm)],[c_15503,c_15]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_17249,plain,
% 3.87/0.98      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
% 3.87/0.98      inference(demodulation,[status(thm)],[c_17245,c_736]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_17250,plain,
% 3.87/0.98      ( $false ),
% 3.87/0.98      inference(equality_resolution_simp,[status(thm)],[c_17249]) ).
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  ------                               Statistics
% 3.87/0.98  
% 3.87/0.98  ------ General
% 3.87/0.98  
% 3.87/0.98  abstr_ref_over_cycles:                  0
% 3.87/0.98  abstr_ref_under_cycles:                 0
% 3.87/0.98  gc_basic_clause_elim:                   0
% 3.87/0.98  forced_gc_time:                         0
% 3.87/0.98  parsing_time:                           0.007
% 3.87/0.98  unif_index_cands_time:                  0.
% 3.87/0.98  unif_index_add_time:                    0.
% 3.87/0.98  orderings_time:                         0.
% 3.87/0.98  out_proof_time:                         0.005
% 3.87/0.98  total_time:                             0.422
% 3.87/0.98  num_of_symbols:                         38
% 3.87/0.98  num_of_terms:                           21922
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing
% 3.87/0.98  
% 3.87/0.98  num_of_splits:                          0
% 3.87/0.98  num_of_split_atoms:                     0
% 3.87/0.98  num_of_reused_defs:                     0
% 3.87/0.98  num_eq_ax_congr_red:                    5
% 3.87/0.98  num_of_sem_filtered_clauses:            1
% 3.87/0.98  num_of_subtypes:                        0
% 3.87/0.98  monotx_restored_types:                  0
% 3.87/0.98  sat_num_of_epr_types:                   0
% 3.87/0.98  sat_num_of_non_cyclic_types:            0
% 3.87/0.98  sat_guarded_non_collapsed_types:        0
% 3.87/0.98  num_pure_diseq_elim:                    0
% 3.87/0.98  simp_replaced_by:                       0
% 3.87/0.98  res_preprocessed:                       72
% 3.87/0.98  prep_upred:                             0
% 3.87/0.98  prep_unflattend:                        0
% 3.87/0.98  smt_new_axioms:                         0
% 3.87/0.98  pred_elim_cands:                        1
% 3.87/0.98  pred_elim:                              1
% 3.87/0.98  pred_elim_cl:                           1
% 3.87/0.98  pred_elim_cycles:                       3
% 3.87/0.98  merged_defs:                            8
% 3.87/0.98  merged_defs_ncl:                        0
% 3.87/0.98  bin_hyper_res:                          8
% 3.87/0.98  prep_cycles:                            4
% 3.87/0.98  pred_elim_time:                         0.
% 3.87/0.98  splitting_time:                         0.
% 3.87/0.98  sem_filter_time:                        0.
% 3.87/0.98  monotx_time:                            0.
% 3.87/0.98  subtype_inf_time:                       0.
% 3.87/0.98  
% 3.87/0.98  ------ Problem properties
% 3.87/0.98  
% 3.87/0.98  clauses:                                15
% 3.87/0.98  conjectures:                            1
% 3.87/0.98  epr:                                    1
% 3.87/0.98  horn:                                   15
% 3.87/0.98  ground:                                 1
% 3.87/0.98  unary:                                  11
% 3.87/0.98  binary:                                 4
% 3.87/0.98  lits:                                   19
% 3.87/0.98  lits_eq:                                14
% 3.87/0.98  fd_pure:                                0
% 3.87/0.98  fd_pseudo:                              0
% 3.87/0.98  fd_cond:                                0
% 3.87/0.98  fd_pseudo_cond:                         0
% 3.87/0.98  ac_symbols:                             1
% 3.87/0.98  
% 3.87/0.98  ------ Propositional Solver
% 3.87/0.98  
% 3.87/0.98  prop_solver_calls:                      33
% 3.87/0.98  prop_fast_solver_calls:                 339
% 3.87/0.98  smt_solver_calls:                       0
% 3.87/0.98  smt_fast_solver_calls:                  0
% 3.87/0.98  prop_num_of_clauses:                    3186
% 3.87/0.98  prop_preprocess_simplified:             6643
% 3.87/0.98  prop_fo_subsumed:                       0
% 3.87/0.98  prop_solver_time:                       0.
% 3.87/0.98  smt_solver_time:                        0.
% 3.87/0.98  smt_fast_solver_time:                   0.
% 3.87/0.98  prop_fast_solver_time:                  0.
% 3.87/0.98  prop_unsat_core_time:                   0.
% 3.87/0.98  
% 3.87/0.98  ------ QBF
% 3.87/0.98  
% 3.87/0.98  qbf_q_res:                              0
% 3.87/0.98  qbf_num_tautologies:                    0
% 3.87/0.98  qbf_prep_cycles:                        0
% 3.87/0.98  
% 3.87/0.98  ------ BMC1
% 3.87/0.98  
% 3.87/0.98  bmc1_current_bound:                     -1
% 3.87/0.98  bmc1_last_solved_bound:                 -1
% 3.87/0.98  bmc1_unsat_core_size:                   -1
% 3.87/0.98  bmc1_unsat_core_parents_size:           -1
% 3.87/0.98  bmc1_merge_next_fun:                    0
% 3.87/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.87/0.98  
% 3.87/0.98  ------ Instantiation
% 3.87/0.98  
% 3.87/0.98  inst_num_of_clauses:                    1271
% 3.87/0.98  inst_num_in_passive:                    617
% 3.87/0.98  inst_num_in_active:                     455
% 3.87/0.98  inst_num_in_unprocessed:                199
% 3.87/0.98  inst_num_of_loops:                      510
% 3.87/0.98  inst_num_of_learning_restarts:          0
% 3.87/0.98  inst_num_moves_active_passive:          50
% 3.87/0.98  inst_lit_activity:                      0
% 3.87/0.98  inst_lit_activity_moves:                0
% 3.87/0.98  inst_num_tautologies:                   0
% 3.87/0.98  inst_num_prop_implied:                  0
% 3.87/0.98  inst_num_existing_simplified:           0
% 3.87/0.98  inst_num_eq_res_simplified:             0
% 3.87/0.98  inst_num_child_elim:                    0
% 3.87/0.98  inst_num_of_dismatching_blockings:      666
% 3.87/0.98  inst_num_of_non_proper_insts:           1462
% 3.87/0.98  inst_num_of_duplicates:                 0
% 3.87/0.98  inst_inst_num_from_inst_to_res:         0
% 3.87/0.98  inst_dismatching_checking_time:         0.
% 3.87/0.98  
% 3.87/0.98  ------ Resolution
% 3.87/0.98  
% 3.87/0.98  res_num_of_clauses:                     0
% 3.87/0.98  res_num_in_passive:                     0
% 3.87/0.98  res_num_in_active:                      0
% 3.87/0.98  res_num_of_loops:                       76
% 3.87/0.98  res_forward_subset_subsumed:            381
% 3.87/0.98  res_backward_subset_subsumed:           2
% 3.87/0.98  res_forward_subsumed:                   0
% 3.87/0.98  res_backward_subsumed:                  0
% 3.87/0.98  res_forward_subsumption_resolution:     0
% 3.87/0.98  res_backward_subsumption_resolution:    0
% 3.87/0.98  res_clause_to_clause_subsumption:       17172
% 3.87/0.98  res_orphan_elimination:                 0
% 3.87/0.98  res_tautology_del:                      121
% 3.87/0.98  res_num_eq_res_simplified:              0
% 3.87/0.98  res_num_sel_changes:                    0
% 3.87/0.98  res_moves_from_active_to_pass:          0
% 3.87/0.99  
% 3.87/0.99  ------ Superposition
% 3.87/0.99  
% 3.87/0.99  sup_time_total:                         0.
% 3.87/0.99  sup_time_generating:                    0.
% 3.87/0.99  sup_time_sim_full:                      0.
% 3.87/0.99  sup_time_sim_immed:                     0.
% 3.87/0.99  
% 3.87/0.99  sup_num_of_clauses:                     630
% 3.87/0.99  sup_num_in_active:                      84
% 3.87/0.99  sup_num_in_passive:                     546
% 3.87/0.99  sup_num_of_loops:                       100
% 3.87/0.99  sup_fw_superposition:                   5010
% 3.87/0.99  sup_bw_superposition:                   3190
% 3.87/0.99  sup_immediate_simplified:               2979
% 3.87/0.99  sup_given_eliminated:                   4
% 3.87/0.99  comparisons_done:                       0
% 3.87/0.99  comparisons_avoided:                    0
% 3.87/0.99  
% 3.87/0.99  ------ Simplifications
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  sim_fw_subset_subsumed:                 0
% 3.87/0.99  sim_bw_subset_subsumed:                 0
% 3.87/0.99  sim_fw_subsumed:                        259
% 3.87/0.99  sim_bw_subsumed:                        3
% 3.87/0.99  sim_fw_subsumption_res:                 0
% 3.87/0.99  sim_bw_subsumption_res:                 0
% 3.87/0.99  sim_tautology_del:                      1
% 3.87/0.99  sim_eq_tautology_del:                   757
% 3.87/0.99  sim_eq_res_simp:                        0
% 3.87/0.99  sim_fw_demodulated:                     2272
% 3.87/0.99  sim_bw_demodulated:                     40
% 3.87/0.99  sim_light_normalised:                   1067
% 3.87/0.99  sim_joinable_taut:                      129
% 3.87/0.99  sim_joinable_simp:                      0
% 3.87/0.99  sim_ac_normalised:                      0
% 3.87/0.99  sim_smt_subsumption:                    0
% 3.87/0.99  
%------------------------------------------------------------------------------
