%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:45 EST 2020

% Result     : Theorem 35.45s
% Output     : CNFRefutation 35.45s
% Verified   : 
% Statistics : Number of formulae       :  473 (537759 expanded)
%              Number of clauses        :  427 (179560 expanded)
%              Number of leaves         :   16 (159264 expanded)
%              Depth                    :   42
%              Number of atoms          :  514 (579000 expanded)
%              Number of equality atoms :  466 (519350 expanded)
%              Maximal formula depth    :    8 (   1 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22])).

fof(f39,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f39,f29])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f38,f29])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f34,f29,f41])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f35,f29,f29])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_5,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_346,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_12,c_1,c_5,c_0])).

cnf(c_528,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_530,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1939,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_528,c_530])).

cnf(c_541,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_2327,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_1939,c_541])).

cnf(c_2552,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(k3_xboole_0(X0,sK0),X1) ),
    inference(superposition,[status(thm)],[c_2327,c_5])).

cnf(c_542,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_2558,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2327,c_542])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_348,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_9,c_12,c_1,c_5,c_0])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_349,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_6,c_12,c_1,c_5,c_0])).

cnf(c_533,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_348,c_349])).

cnf(c_776,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_533,c_12])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_651,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_782,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_776,c_651])).

cnf(c_1046,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_782,c_349])).

cnf(c_10,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_347,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_12,c_1,c_5,c_0])).

cnf(c_1405,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1046,c_347])).

cnf(c_1413,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1405,c_533,c_1046])).

cnf(c_1685,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_1413,c_349])).

cnf(c_1712,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1685,c_11,c_651])).

cnf(c_540,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_2322,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_1939,c_5])).

cnf(c_2355,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) = k3_xboole_0(sK0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_540,c_2322])).

cnf(c_4478,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0)) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) ),
    inference(superposition,[status(thm)],[c_1712,c_2355])).

cnf(c_2326,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_1939,c_542])).

cnf(c_4531,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_4478,c_2326])).

cnf(c_2365,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(sK0,X1)) = k3_xboole_0(X1,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_2322,c_541])).

cnf(c_6893,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0),k3_xboole_0(sK0,X1)) = k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_4531,c_2365])).

cnf(c_4614,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0),sK0) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_4531,c_2327])).

cnf(c_2331,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_1939,c_542])).

cnf(c_4630,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0),sK0) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_4614,c_2331])).

cnf(c_4984,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0),k3_xboole_0(sK0,X1)) = k3_xboole_0(k3_xboole_0(X0,sK0),X1) ),
    inference(superposition,[status(thm)],[c_4630,c_5])).

cnf(c_6942,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,sK0)) = k3_xboole_0(k3_xboole_0(X1,sK0),X0) ),
    inference(light_normalisation,[status(thm)],[c_6893,c_4984])).

cnf(c_2500,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,sK0)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2326,c_542])).

cnf(c_6943,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK0),X1) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
    inference(demodulation,[status(thm)],[c_6942,c_2500])).

cnf(c_9670,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2552,c_2558,c_6943])).

cnf(c_936,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X0,X1),X2))))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_349])).

cnf(c_14243,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_936,c_2322])).

cnf(c_14260,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_14243,c_1939])).

cnf(c_16158,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),X1),k3_xboole_0(X0,k3_xboole_0(X1,sK0)))))) = sK0 ),
    inference(superposition,[status(thm)],[c_9670,c_14260])).

cnf(c_8,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_529,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_768,plain,
    ( r1_tarski(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_529])).

cnf(c_769,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_768,c_347])).

cnf(c_5564,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_769])).

cnf(c_15435,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1939,c_5564])).

cnf(c_16128,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_15435,c_530])).

cnf(c_2364,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1)) = k3_xboole_0(X1,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_2322,c_542])).

cnf(c_6451,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) ),
    inference(superposition,[status(thm)],[c_1712,c_2364])).

cnf(c_6529,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_6451,c_2326])).

cnf(c_16680,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1)),sK0) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[status(thm)],[c_16128,c_6529])).

cnf(c_16685,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[status(thm)],[c_16128,c_2327])).

cnf(c_2547,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0) = k3_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1712,c_2327])).

cnf(c_2580,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_2547,c_1712])).

cnf(c_16702,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,sK1),sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_16685,c_2580])).

cnf(c_16707,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1)),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_16680,c_16702])).

cnf(c_2549,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_2322,c_2327])).

cnf(c_2578,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0) = k3_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_2549,c_2327])).

cnf(c_2372,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,sK0)) = k3_xboole_0(X1,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_2322,c_542])).

cnf(c_7258,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X0,sK0)))) = k3_xboole_0(k3_xboole_0(X0,sK0),sK0) ),
    inference(superposition,[status(thm)],[c_2372,c_4531])).

cnf(c_4610,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_4531,c_542])).

cnf(c_4634,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_4610,c_2326])).

cnf(c_6595,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k3_xboole_0(k3_xboole_0(X0,sK0),sK0) ),
    inference(superposition,[status(thm)],[c_2331,c_6529])).

cnf(c_1909,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1712,c_542])).

cnf(c_1921,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1712,c_542])).

cnf(c_2477,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k3_xboole_0(k3_xboole_0(X0,X1),sK0) ),
    inference(superposition,[status(thm)],[c_542,c_2326])).

cnf(c_2356,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_541,c_2322])).

cnf(c_2513,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),sK0) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2477,c_2356])).

cnf(c_4902,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_4634,c_541])).

cnf(c_6448,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X2)))) = k3_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(sK0,X2)) ),
    inference(superposition,[status(thm)],[c_541,c_2364])).

cnf(c_2357,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_542,c_2322])).

cnf(c_5275,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X2)))) = k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_2357,c_540])).

cnf(c_6532,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(sK0,X2)) = k3_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X2,X0))) ),
    inference(light_normalisation,[status(thm)],[c_6448,c_5275])).

cnf(c_6691,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_6595,c_1909,c_1921,c_2513,c_4902,c_6532])).

cnf(c_7262,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK0),sK0) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_7258,c_4634,c_6691])).

cnf(c_16708,plain,
    ( k3_xboole_0(sK1,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_16707,c_2327,c_2578,c_7262])).

cnf(c_16892,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_16708,c_5])).

cnf(c_18079,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_16892])).

cnf(c_18363,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(X0,sK0),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_18079,c_5])).

cnf(c_2330,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_1939,c_540])).

cnf(c_2694,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2330,c_542])).

cnf(c_18107,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1)) = k3_xboole_0(sK1,k3_xboole_0(X1,k3_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_2694,c_16892])).

cnf(c_5145,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1)) = k3_xboole_0(sK0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_2356])).

cnf(c_18205,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_18107,c_5145])).

cnf(c_18420,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),X1) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_18363,c_6943,c_18205])).

cnf(c_39551,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k3_xboole_0(X0,sK0)))))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_16158,c_16158,c_18420])).

cnf(c_1394,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_5,c_347])).

cnf(c_942,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,X2))))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_349])).

cnf(c_544,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_2005,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,X3)))) = k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3)))) ),
    inference(superposition,[status(thm)],[c_347,c_544])).

cnf(c_21590,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_942,c_2005])).

cnf(c_21693,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X1,X1)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1712,c_21590])).

cnf(c_21886,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_21693,c_11,c_533,c_1413])).

cnf(c_22263,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_21886,c_5])).

cnf(c_22431,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_22263,c_5])).

cnf(c_46047,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_22431])).

cnf(c_53182,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_46047])).

cnf(c_1392,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_347])).

cnf(c_59537,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X2,k3_xboole_0(X1,k3_xboole_0(X0,X3)))) = k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X3,X0)))) ),
    inference(superposition,[status(thm)],[c_53182,c_1392])).

cnf(c_59670,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X2,k3_xboole_0(X1,k3_xboole_0(X0,X3)))) = k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X3)))) ),
    inference(demodulation,[status(thm)],[c_59537,c_53182])).

cnf(c_46276,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_22431,c_540])).

cnf(c_22278,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_21886,c_541])).

cnf(c_22202,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_21886])).

cnf(c_22667,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,X1),X2))) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_22202,c_542])).

cnf(c_22801,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X1,X2)))) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_22667,c_5])).

cnf(c_22281,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,X1)))) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_21886,c_542])).

cnf(c_22295,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X0))) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_21886,c_542])).

cnf(c_22418,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_22281,c_22295])).

cnf(c_22802,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X2,X0),X1) ),
    inference(demodulation,[status(thm)],[c_22801,c_1909,c_22418])).

cnf(c_46379,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_46276,c_1909,c_22278,c_22802])).

cnf(c_59671,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3)))) = k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X0,k3_xboole_0(X2,X3)))) ),
    inference(light_normalisation,[status(thm)],[c_59670,c_46379])).

cnf(c_1528,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_540,c_347])).

cnf(c_56872,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X2,k3_xboole_0(X1,k3_xboole_0(X0,X3)))) = k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X3)))) ),
    inference(superposition,[status(thm)],[c_46047,c_1392])).

cnf(c_57005,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3)))) = k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X3)))) ),
    inference(light_normalisation,[status(thm)],[c_56872,c_46379])).

cnf(c_1399,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_5,c_347])).

cnf(c_1417,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(light_normalisation,[status(thm)],[c_1399,c_5])).

cnf(c_1403,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) ),
    inference(superposition,[status(thm)],[c_5,c_347])).

cnf(c_1418,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_1417,c_1403])).

cnf(c_57006,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3)))) = k3_xboole_0(X2,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X2,X3))),X1)) ),
    inference(demodulation,[status(thm)],[c_57005,c_1418,c_46379])).

cnf(c_59672,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3)))) = k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X3)))) ),
    inference(demodulation,[status(thm)],[c_59671,c_1528,c_57006])).

cnf(c_53322,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_46047,c_0])).

cnf(c_60119,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X3))) = k3_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_542,c_53322])).

cnf(c_53364,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X3))) = k3_xboole_0(X2,k3_xboole_0(X3,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_46047,c_542])).

cnf(c_60497,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3))) ),
    inference(light_normalisation,[status(thm)],[c_60119,c_53364])).

cnf(c_64821,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X2,X0),k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(light_normalisation,[status(thm)],[c_1394,c_1394,c_59672,c_60497])).

cnf(c_64980,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1939,c_64821])).

cnf(c_70399,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_64980])).

cnf(c_83062,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),X0))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_39551,c_70399])).

cnf(c_2703,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X1,sK0)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2330,c_542])).

cnf(c_2700,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2330,c_347])).

cnf(c_2349,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2322])).

cnf(c_2955,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_2349,c_347])).

cnf(c_2962,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2955,c_533,c_2700])).

cnf(c_20072,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X0,sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2700,c_2962])).

cnf(c_20120,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_20072])).

cnf(c_40962,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1)),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2703,c_20120])).

cnf(c_41092,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_40962,c_5145])).

cnf(c_84171,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_83062,c_11,c_533,c_1413,c_41092])).

cnf(c_70560,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_64980,c_541])).

cnf(c_59536,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X0))) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_53182,c_5])).

cnf(c_84721,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) ),
    inference(superposition,[status(thm)],[c_70560,c_59536])).

cnf(c_5557,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k3_xboole_0(X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_769])).

cnf(c_14547,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k3_xboole_0(X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_5557])).

cnf(c_34191,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)),k3_xboole_0(sK0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_14547])).

cnf(c_35783,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)),k3_xboole_0(sK0,X1)) = k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)) ),
    inference(superposition,[status(thm)],[c_34191,c_530])).

cnf(c_2370,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) = k3_xboole_0(X0,k3_xboole_0(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_2322,c_540])).

cnf(c_22334,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)),k3_xboole_0(sK0,X1)) = k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) ),
    inference(superposition,[status(thm)],[c_21886,c_2370])).

cnf(c_2498,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
    inference(superposition,[status(thm)],[c_2326,c_540])).

cnf(c_9007,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_541,c_2498])).

cnf(c_22393,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)),k3_xboole_0(sK0,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_22334,c_9007])).

cnf(c_34189,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1939,c_14547])).

cnf(c_35328,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_34189,c_530])).

cnf(c_1938,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_529,c_530])).

cnf(c_2557,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_2327,c_0])).

cnf(c_3763,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_2349,c_2557])).

cnf(c_3789,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k3_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_3763,c_2557])).

cnf(c_35329,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_35328,c_1938,c_3789])).

cnf(c_35376,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_35328,c_35329])).

cnf(c_35784,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)) = k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(demodulation,[status(thm)],[c_35783,c_22393,c_35376])).

cnf(c_85174,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
    inference(demodulation,[status(thm)],[c_84721,c_2327,c_35784])).

cnf(c_90402,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ),
    inference(superposition,[status(thm)],[c_85174,c_1392])).

cnf(c_90571,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_90402,c_1939])).

cnf(c_91057,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_84171,c_90571])).

cnf(c_91062,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) = k5_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ),
    inference(superposition,[status(thm)],[c_0,c_90571])).

cnf(c_91897,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_91057,c_91062])).

cnf(c_2495,plain,
    ( k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)))) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) ),
    inference(superposition,[status(thm)],[c_2326,c_347])).

cnf(c_2506,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
    inference(demodulation,[status(thm)],[c_2495,c_2326])).

cnf(c_16921,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(X0,sK0))) = k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_16708,c_2506])).

cnf(c_16930,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0) = k3_xboole_0(sK1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_16708,c_2500])).

cnf(c_16934,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_16930,c_2578])).

cnf(c_16942,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
    inference(demodulation,[status(thm)],[c_16921,c_16934])).

cnf(c_4896,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,sK0),X1)) = k3_xboole_0(k3_xboole_0(X0,sK0),X1) ),
    inference(superposition,[status(thm)],[c_4634,c_5])).

cnf(c_4901,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,sK0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_4634,c_542])).

cnf(c_12949,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_4896,c_4901,c_6943])).

cnf(c_12985,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
    inference(superposition,[status(thm)],[c_0,c_12949])).

cnf(c_70328,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),X1)) = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_64980])).

cnf(c_75258,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK0))),X1)) = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))))) ),
    inference(superposition,[status(thm)],[c_12985,c_70328])).

cnf(c_780,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_533])).

cnf(c_1042,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_780,c_782])).

cnf(c_1052,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1042,c_11])).

cnf(c_1251,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1052,c_1052])).

cnf(c_1371,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
    inference(superposition,[status(thm)],[c_12,c_1251])).

cnf(c_20153,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X1,sK0) ),
    inference(superposition,[status(thm)],[c_20072,c_1371])).

cnf(c_20174,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_20153,c_11])).

cnf(c_945,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X2)) = k3_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_349,c_5])).

cnf(c_29067,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK0),X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_20174,c_945])).

cnf(c_22213,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) ),
    inference(superposition,[status(thm)],[c_2326,c_21886])).

cnf(c_22482,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_22213,c_2326])).

cnf(c_23355,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),X1),sK0),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),X1),sK0) ),
    inference(superposition,[status(thm)],[c_9670,c_22482])).

cnf(c_23474,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),sK0),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),sK0) ),
    inference(light_normalisation,[status(thm)],[c_23355,c_18420])).

cnf(c_4979,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0)),sK0) = k3_xboole_0(k3_xboole_0(X0,sK0),sK0) ),
    inference(superposition,[status(thm)],[c_2331,c_4630])).

cnf(c_5010,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,sK0),sK0)) = k3_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_4979,c_1909,c_2513,c_4902])).

cnf(c_5011,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),sK0) = k3_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_5010,c_1909,c_1921,c_2513])).

cnf(c_23475,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X0,sK0)),sK0)) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_23474,c_2513,c_5011,c_6943])).

cnf(c_2566,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
    inference(superposition,[status(thm)],[c_2327,c_540])).

cnf(c_10849,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),X2)) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X2) ),
    inference(superposition,[status(thm)],[c_2566,c_5])).

cnf(c_7228,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(X1,sK0),X2)) = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK0,X0)),X2) ),
    inference(superposition,[status(thm)],[c_2372,c_5])).

cnf(c_6878,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,k3_xboole_0(X2,sK0))) = k3_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_541,c_2365])).

cnf(c_6959,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,k3_xboole_0(X2,sK0))) = k3_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_6878,c_6532])).

cnf(c_7273,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X1,X2))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_7228,c_6943,c_6959])).

cnf(c_9703,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)) ),
    inference(superposition,[status(thm)],[c_540,c_9670])).

cnf(c_2492,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2326,c_542])).

cnf(c_8556,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X2)))) = k3_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,sK0)) ),
    inference(superposition,[status(thm)],[c_541,c_2492])).

cnf(c_7060,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X2)))) = k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK0,X2))) ),
    inference(superposition,[status(thm)],[c_2370,c_540])).

cnf(c_8654,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(sK0,X2))) ),
    inference(light_normalisation,[status(thm)],[c_8556,c_7060])).

cnf(c_9825,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(sK0,X2))) ),
    inference(light_normalisation,[status(thm)],[c_9703,c_7273,c_8654])).

cnf(c_10917,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(sK0,X2))) ),
    inference(light_normalisation,[status(thm)],[c_10849,c_7273,c_9825])).

cnf(c_11546,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))))) = k3_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,sK0)) ),
    inference(superposition,[status(thm)],[c_541,c_2694])).

cnf(c_5253,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))))) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X1),X0)) ),
    inference(superposition,[status(thm)],[c_541,c_2357])).

cnf(c_11641,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_11546,c_5253])).

cnf(c_12965,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,sK0)))) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)) ),
    inference(superposition,[status(thm)],[c_5,c_12949])).

cnf(c_13147,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,sK0)))) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_12965,c_11641])).

cnf(c_23476,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_23475,c_10917,c_11641,c_13147])).

cnf(c_23477,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,X1))) = k3_xboole_0(sK0,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_23476,c_18420])).

cnf(c_29098,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_29067,c_4901,c_18420,c_23477])).

cnf(c_14242,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))),sK0) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_936,c_2326])).

cnf(c_14261,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))),sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_14242,c_1939])).

cnf(c_16476,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))),sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_544,c_14261])).

cnf(c_46102,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))),k3_xboole_0(sK0,X1)) = k3_xboole_0(sK0,k3_xboole_0(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_16476,c_22431])).

cnf(c_30450,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))),k3_xboole_0(sK0,X1)) = k3_xboole_0(sK0,X1) ),
    inference(superposition,[status(thm)],[c_16476,c_5])).

cnf(c_46661,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_46102,c_30450])).

cnf(c_76159,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),X1)) = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(sK0,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_75258,c_29098,c_46661])).

cnf(c_70380,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X1,sK0))))) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(sK0,X1))))) ),
    inference(superposition,[status(thm)],[c_12985,c_64980])).

cnf(c_70493,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ),
    inference(superposition,[status(thm)],[c_64980,c_21886])).

cnf(c_70609,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))),sK0) ),
    inference(superposition,[status(thm)],[c_64980,c_6529])).

cnf(c_70614,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ),
    inference(superposition,[status(thm)],[c_64980,c_2322])).

cnf(c_70638,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),X1))) = k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X1)),sK0)) ),
    inference(superposition,[status(thm)],[c_64980,c_9670])).

cnf(c_11584,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1))) = k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_2694,c_347])).

cnf(c_2943,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1))) ),
    inference(superposition,[status(thm)],[c_2349,c_347])).

cnf(c_2945,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_2349,c_5])).

cnf(c_2964,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_2943,c_2945])).

cnf(c_11628,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_11584,c_2349,c_2964])).

cnf(c_1559,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_541,c_347])).

cnf(c_11629,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_11628,c_1559])).

cnf(c_70962,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X1)),sK0)) ),
    inference(light_normalisation,[status(thm)],[c_70638,c_11629])).

cnf(c_2559,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2327,c_541])).

cnf(c_56650,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(sK0,X1),X2))) = k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k5_xboole_0(k3_xboole_0(sK0,X1),k3_xboole_0(k3_xboole_0(sK0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_2559,c_1392])).

cnf(c_10208,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(sK0,X1),X2)) = k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,sK0))) ),
    inference(superposition,[status(thm)],[c_2559,c_541])).

cnf(c_22274,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))))) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_21886,c_21590])).

cnf(c_22424,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_22274,c_11,c_533,c_1413])).

cnf(c_8596,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1))) = k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_2492,c_347])).

cnf(c_2486,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1))) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1))) ),
    inference(superposition,[status(thm)],[c_2326,c_347])).

cnf(c_2488,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1)) = k3_xboole_0(k3_xboole_0(X0,sK0),X1) ),
    inference(superposition,[status(thm)],[c_2326,c_5])).

cnf(c_2507,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1))) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X0,sK0),X1)) ),
    inference(demodulation,[status(thm)],[c_2486,c_2488])).

cnf(c_8632,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_8596,c_2326,c_2506,c_2507,c_6943])).

cnf(c_45069,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,sK0)))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k5_xboole_0(sK0,k3_xboole_0(X2,sK0))) ),
    inference(superposition,[status(thm)],[c_22424,c_8632])).

cnf(c_45077,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X2,sK0))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k5_xboole_0(sK0,k3_xboole_0(X2,sK0))) ),
    inference(superposition,[status(thm)],[c_22424,c_2506])).

cnf(c_45125,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,k3_xboole_0(X2,sK0))) = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,sK0)),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_22424,c_2500])).

cnf(c_2741,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2331,c_541])).

cnf(c_13236,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,k3_xboole_0(X2,sK0))) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,sK0))) ),
    inference(superposition,[status(thm)],[c_2741,c_542])).

cnf(c_45177,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X2,sK0)) = k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_45125,c_13236])).

cnf(c_45227,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0)))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k5_xboole_0(sK0,k3_xboole_0(X2,sK0))) ),
    inference(demodulation,[status(thm)],[c_45077,c_45177])).

cnf(c_13226,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X2)))) = k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0)))) ),
    inference(superposition,[status(thm)],[c_2741,c_347])).

cnf(c_13269,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(X2,k3_xboole_0(X1,sK0)))) ),
    inference(demodulation,[status(thm)],[c_13226,c_2741])).

cnf(c_1401,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X2,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_347])).

cnf(c_13270,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0)))) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0)))) ),
    inference(demodulation,[status(thm)],[c_13269,c_1401,c_8632])).

cnf(c_45228,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k5_xboole_0(sK0,k3_xboole_0(X2,sK0))) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0)))) ),
    inference(light_normalisation,[status(thm)],[c_45227,c_13270])).

cnf(c_45236,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,sK0)))) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0)))) ),
    inference(demodulation,[status(thm)],[c_45069,c_45228])).

cnf(c_57325,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k5_xboole_0(k3_xboole_0(sK0,X1),k3_xboole_0(k3_xboole_0(sK0,X1),X2))) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0)))) ),
    inference(light_normalisation,[status(thm)],[c_56650,c_10208,c_45236])).

cnf(c_10205,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(sK0,X1)) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
    inference(superposition,[status(thm)],[c_2559,c_0])).

cnf(c_57326,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),sK0)) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0)))) ),
    inference(demodulation,[status(thm)],[c_57325,c_10205,c_11629,c_46379])).

cnf(c_70963,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
    inference(demodulation,[status(thm)],[c_70962,c_35376,c_46661,c_57326])).

cnf(c_70996,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
    inference(demodulation,[status(thm)],[c_70614,c_70963])).

cnf(c_70613,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))),sK0) ),
    inference(superposition,[status(thm)],[c_64980,c_2326])).

cnf(c_70997,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))),sK0) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
    inference(demodulation,[status(thm)],[c_70613,c_70963])).

cnf(c_71002,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
    inference(demodulation,[status(thm)],[c_70609,c_70996,c_70997])).

cnf(c_71149,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
    inference(demodulation,[status(thm)],[c_70493,c_71002])).

cnf(c_71368,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X1,sK0)))) ),
    inference(demodulation,[status(thm)],[c_70380,c_71149])).

cnf(c_71369,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
    inference(demodulation,[status(thm)],[c_71368,c_29098,c_46661])).

cnf(c_76160,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),X1)) = k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(demodulation,[status(thm)],[c_76159,c_71369])).

cnf(c_75661,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X1)),X2)))) = k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),sK0) ),
    inference(superposition,[status(thm)],[c_70328,c_20174])).

cnf(c_65386,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),sK0) ),
    inference(superposition,[status(thm)],[c_64821,c_2327])).

cnf(c_2695,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(sK0,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2330,c_541])).

cnf(c_11749,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
    inference(superposition,[status(thm)],[c_2695,c_347])).

cnf(c_11777,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_11749,c_3789,c_8632])).

cnf(c_65757,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),sK0) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_65386,c_11777])).

cnf(c_75701,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X1)),X2)))) = k3_xboole_0(X2,k5_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
    inference(demodulation,[status(thm)],[c_75661,c_782,c_65757])).

cnf(c_76247,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(sK0,X2))))) = k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0))) ),
    inference(demodulation,[status(thm)],[c_76160,c_75701])).

cnf(c_91898,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK2,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_91897,c_11,c_2580,c_16942,c_76247])).

cnf(c_97444,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = sK0 ),
    inference(superposition,[status(thm)],[c_0,c_91898])).

cnf(c_105898,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))) ),
    inference(superposition,[status(thm)],[c_97444,c_90571])).

cnf(c_6582,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_0,c_6529])).

cnf(c_106204,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X0),k3_xboole_0(X0,sK0)) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_6582,c_1401])).

cnf(c_2747,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X0,sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_2331,c_347])).

cnf(c_56747,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_2703,c_1392])).

cnf(c_50123,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(k3_xboole_0(X1,X0),sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),sK0))) ),
    inference(superposition,[status(thm)],[c_541,c_2747])).

cnf(c_28554,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(sK0,X1))))) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) ),
    inference(superposition,[status(thm)],[c_945,c_2357])).

cnf(c_28603,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(sK0,X1))))) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_28554,c_2326])).

cnf(c_30100,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(sK0,X1)))),X2)) = k3_xboole_0(k3_xboole_0(X0,sK0),X2) ),
    inference(superposition,[status(thm)],[c_28603,c_5])).

cnf(c_1655,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X2)) = k3_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_349,c_542])).

cnf(c_30263,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),sK0) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(demodulation,[status(thm)],[c_30100,c_1655,c_6943,c_22802])).

cnf(c_50303,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) ),
    inference(demodulation,[status(thm)],[c_50123,c_1418,c_30263,c_46379])).

cnf(c_57213,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(X1,k3_xboole_0(X1,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_56747,c_50303])).

cnf(c_95905,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),sK0))) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0)))))),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_39551,c_1401])).

cnf(c_1380,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1251,c_12])).

cnf(c_6256,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
    inference(superposition,[status(thm)],[c_544,c_1380])).

cnf(c_1247,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_782,c_1052])).

cnf(c_1274,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1247,c_12])).

cnf(c_5995,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_1274,c_1274])).

cnf(c_6369,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_6256,c_5995])).

cnf(c_50149,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2578,c_2747])).

cnf(c_50249,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(X0,sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,sK0)))) ),
    inference(light_normalisation,[status(thm)],[c_50149,c_2578,c_2747])).

cnf(c_50250,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(demodulation,[status(thm)],[c_50249,c_1909])).

cnf(c_96056,plain,
    ( k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0)))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),sK0)))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(demodulation,[status(thm)],[c_95905,c_11,c_6369,c_41092,c_50250])).

cnf(c_96057,plain,
    ( k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),sK0))))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(demodulation,[status(thm)],[c_96056,c_6369])).

cnf(c_96058,plain,
    ( k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k5_xboole_0(k3_xboole_0(X2,k3_xboole_0(X1,sK0)),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),sK0)))))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(demodulation,[status(thm)],[c_96057,c_6369])).

cnf(c_545,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_20158,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK0),k5_xboole_0(k3_xboole_0(sK0,X0),X1)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_20072,c_545])).

cnf(c_20170,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK0),k5_xboole_0(k3_xboole_0(sK0,X0),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_20158,c_11])).

cnf(c_26327,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),sK0),k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X2)) = X2 ),
    inference(superposition,[status(thm)],[c_542,c_20170])).

cnf(c_26510,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X0,sK0)),X2)) = X2 ),
    inference(light_normalisation,[status(thm)],[c_26327,c_2513])).

cnf(c_96059,plain,
    ( k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),sK0)))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(demodulation,[status(thm)],[c_96058,c_26510])).

cnf(c_1039,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_12,c_782])).

cnf(c_20156,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK0,X1)),k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X1,sK0) ),
    inference(superposition,[status(thm)],[c_20072,c_1039])).

cnf(c_20172,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK0,X1)),X0) = k3_xboole_0(X1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_20156,c_11])).

cnf(c_39811,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k3_xboole_0(X0,sK0))))),sK0) = k5_xboole_0(k5_xboole_0(X2,sK0),X2) ),
    inference(superposition,[status(thm)],[c_39551,c_20172])).

cnf(c_39847,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k3_xboole_0(X0,sK0))))),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_39811,c_1251])).

cnf(c_96060,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))) ),
    inference(demodulation,[status(thm)],[c_96059,c_39847])).

cnf(c_106294,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,sK0))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),X0) ),
    inference(demodulation,[status(thm)],[c_106204,c_1909,c_2747,c_22202,c_57213,c_96060])).

cnf(c_106616,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0) ),
    inference(demodulation,[status(thm)],[c_105898,c_106294])).

cnf(c_15516,plain,
    ( r1_tarski(k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1939,c_5564])).

cnf(c_15624,plain,
    ( r1_tarski(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))))),sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15516,c_6369])).

cnf(c_27168,plain,
    ( r1_tarski(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1939,c_15624])).

cnf(c_27189,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),sK0) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))) ),
    inference(superposition,[status(thm)],[c_27168,c_530])).

cnf(c_49874,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))),k3_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),sK0))) ),
    inference(superposition,[status(thm)],[c_27189,c_347])).

cnf(c_50380,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK2,sK1),sK0),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0))),sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_49874,c_533,c_1418,c_6369,c_6943])).

cnf(c_50381,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0)))),sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_50380,c_6369])).

cnf(c_21787,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))),k3_xboole_0(X1,sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_21590,c_2558])).

cnf(c_21796,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))),k3_xboole_0(X1,sK0)) = k3_xboole_0(X1,sK0) ),
    inference(demodulation,[status(thm)],[c_21787,c_2327])).

cnf(c_23567,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X0,sK0)))),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0)) = k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0) ),
    inference(superposition,[status(thm)],[c_2578,c_21796])).

cnf(c_23835,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,sK0))))),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_23567,c_2578,c_2747])).

cnf(c_23836,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),sK0)),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_23835,c_2326])).

cnf(c_24163,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0)),sK0)),sK0)) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0)) ),
    inference(superposition,[status(thm)],[c_23836,c_2355])).

cnf(c_24178,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0),sK0)),sK0)) = k3_xboole_0(sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_24163,c_2580])).

cnf(c_697,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_529])).

cnf(c_1940,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_697,c_530])).

cnf(c_9365,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_1712,c_2506])).

cnf(c_9479,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_9365,c_6691])).

cnf(c_24179,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0),sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_24178,c_1712,c_1940,c_6691,c_9479])).

cnf(c_24180,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_24179,c_6369])).

cnf(c_50382,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_50381,c_24180])).

cnf(c_49875,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))) ),
    inference(superposition,[status(thm)],[c_27189,c_5])).

cnf(c_50385,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_50382,c_49875])).

cnf(c_9897,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK0,X0),X1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_349,c_2558])).

cnf(c_10047,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK0,X0),X1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_9897,c_2327])).

cnf(c_24875,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X1,X0)))),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_10047,c_10047,c_18420])).

cnf(c_24947,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)),k5_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X0,X1)))),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0)) = k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0) ),
    inference(superposition,[status(thm)],[c_2357,c_24875])).

cnf(c_25309,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK0),k5_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X0,X1)))),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_24947,c_2326,c_2578])).

cnf(c_49900,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),k5_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),X0)))),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))) = k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),sK0) ),
    inference(superposition,[status(thm)],[c_27189,c_25309])).

cnf(c_2493,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(sK0,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2326,c_541])).

cnf(c_45113,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),sK0)) ),
    inference(superposition,[status(thm)],[c_22424,c_2493])).

cnf(c_8895,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2493,c_5])).

cnf(c_45196,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK0,X0)),sK0)) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_45113,c_8895])).

cnf(c_12967,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
    inference(superposition,[status(thm)],[c_541,c_12949])).

cnf(c_13010,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)))) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)) ),
    inference(superposition,[status(thm)],[c_12949,c_5])).

cnf(c_13107,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)))) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_13010,c_11641])).

cnf(c_13145,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X0),sK0))) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_12967,c_13107])).

cnf(c_13146,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X0,X2)))) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_13145,c_2513])).

cnf(c_22298,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X0)),X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_21886,c_542])).

cnf(c_45197,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
    inference(demodulation,[status(thm)],[c_45196,c_7273,c_13146,c_22298])).

cnf(c_45198,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,X1))) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_45197,c_18420])).

cnf(c_50359,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),k3_xboole_0(X0,sK0)))),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0) ),
    inference(demodulation,[status(thm)],[c_49900,c_5011,c_18420,c_45198])).

cnf(c_50394,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),k3_xboole_0(X0,sK0)))),k1_xboole_0) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0) ),
    inference(demodulation,[status(thm)],[c_50385,c_50359])).

cnf(c_50397,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_50394,c_1413])).

cnf(c_106617,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_106616,c_50397])).

cnf(c_9687,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK0,X0),X1))),sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_349,c_9670])).

cnf(c_9839,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK0,X0),X1))),sK0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_9687,c_2327])).

cnf(c_20856,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X1,X0)))),sK0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_9839,c_9839,c_18420])).

cnf(c_21610,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_1939,c_21590])).

cnf(c_22027,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_21610,c_1939])).

cnf(c_22028,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))))) = sK0 ),
    inference(demodulation,[status(thm)],[c_22027,c_6369])).

cnf(c_42734,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))))),sK0),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0)))))) = sK0 ),
    inference(superposition,[status(thm)],[c_20856,c_22028])).

cnf(c_2542,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK0,X0))),sK0) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0) ),
    inference(superposition,[status(thm)],[c_349,c_2327])).

cnf(c_2586,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK0,X0))),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_2542,c_2580])).

cnf(c_42935,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_42734,c_1939,c_2349,c_2580,c_2586])).

cnf(c_43144,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))),X0))) ),
    inference(superposition,[status(thm)],[c_42935,c_347])).

cnf(c_6926,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))),sK0) = k3_xboole_0(k3_xboole_0(sK0,X0),sK0) ),
    inference(superposition,[status(thm)],[c_2365,c_4630])).

cnf(c_6931,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))),sK0) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_6926,c_5011])).

cnf(c_6932,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_6931,c_1909,c_2513,c_4634])).

cnf(c_43135,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,sK0),k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))),k3_xboole_0(sK0,sK0))),k3_xboole_0(sK0,sK0)) = k3_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_42935,c_25309])).

cnf(c_20161,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(X0,sK0))) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_20072,c_544])).

cnf(c_20169,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(X0,sK0))) = X1 ),
    inference(demodulation,[status(thm)],[c_20161,c_11])).

cnf(c_43327,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))) = sK0 ),
    inference(demodulation,[status(thm)],[c_43135,c_1712,c_20169,c_35376])).

cnf(c_43761,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_43144,c_6932,c_43327])).

cnf(c_91160,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,X0))))) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))))) ),
    inference(superposition,[status(thm)],[c_16892,c_90571])).

cnf(c_91161,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,X0))))) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK0))))) ),
    inference(superposition,[status(thm)],[c_18079,c_90571])).

cnf(c_6485,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1))) = k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(X1,k3_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_2364,c_347])).

cnf(c_4894,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,sK0),X1))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X0,sK0),X1))) ),
    inference(superposition,[status(thm)],[c_4634,c_347])).

cnf(c_4934,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X0,sK0),X1))) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X0,sK0),X1)) ),
    inference(demodulation,[status(thm)],[c_4894,c_4896])).

cnf(c_4935,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X0,sK0),X1)) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
    inference(demodulation,[status(thm)],[c_4934,c_1418,c_1712])).

cnf(c_6516,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,k3_xboole_0(sK0,X0))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_6485,c_2326,c_2507,c_4935])).

cnf(c_16916,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(sK0,sK1))) = k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_16708,c_6516])).

cnf(c_2689,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)))) = sK0 ),
    inference(superposition,[status(thm)],[c_2330,c_349])).

cnf(c_16920,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0))) = sK0 ),
    inference(superposition,[status(thm)],[c_16708,c_2689])).

cnf(c_16943,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_16920,c_1052,c_2349])).

cnf(c_16948,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
    inference(demodulation,[status(thm)],[c_16916,c_16943])).

cnf(c_91665,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,X0))))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_91161,c_16948,c_29098])).

cnf(c_2565,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0),k3_xboole_0(X0,sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_2327,c_347])).

cnf(c_2581,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
    inference(demodulation,[status(thm)],[c_2580,c_2565])).

cnf(c_26166,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(sK0,X1) ),
    inference(superposition,[status(thm)],[c_20169,c_1247])).

cnf(c_91666,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,X0))))) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_91665,c_2581,c_26166])).

cnf(c_91667,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))))) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_91160,c_91666])).

cnf(c_91668,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k3_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_91667,c_16948,c_46661])).

cnf(c_106618,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_106617,c_43761,c_91668])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_531,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2979,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_531])).

cnf(c_68953,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_16708,c_2979])).

cnf(c_69150,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_68953,c_533])).

cnf(c_69151,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_69150])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_126,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_127,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_126])).

cnf(c_128,plain,
    ( k3_xboole_0(sK0,sK2) != k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_106618,c_69151,c_128])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 35.45/5.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.45/5.02  
% 35.45/5.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.45/5.02  
% 35.45/5.02  ------  iProver source info
% 35.45/5.02  
% 35.45/5.02  git: date: 2020-06-30 10:37:57 +0100
% 35.45/5.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.45/5.02  git: non_committed_changes: false
% 35.45/5.02  git: last_make_outside_of_git: false
% 35.45/5.02  
% 35.45/5.02  ------ 
% 35.45/5.02  
% 35.45/5.02  ------ Input Options
% 35.45/5.02  
% 35.45/5.02  --out_options                           all
% 35.45/5.02  --tptp_safe_out                         true
% 35.45/5.02  --problem_path                          ""
% 35.45/5.02  --include_path                          ""
% 35.45/5.02  --clausifier                            res/vclausify_rel
% 35.45/5.02  --clausifier_options                    ""
% 35.45/5.02  --stdin                                 false
% 35.45/5.02  --stats_out                             all
% 35.45/5.02  
% 35.45/5.02  ------ General Options
% 35.45/5.02  
% 35.45/5.02  --fof                                   false
% 35.45/5.02  --time_out_real                         305.
% 35.45/5.02  --time_out_virtual                      -1.
% 35.45/5.02  --symbol_type_check                     false
% 35.45/5.02  --clausify_out                          false
% 35.45/5.02  --sig_cnt_out                           false
% 35.45/5.02  --trig_cnt_out                          false
% 35.45/5.02  --trig_cnt_out_tolerance                1.
% 35.45/5.02  --trig_cnt_out_sk_spl                   false
% 35.45/5.02  --abstr_cl_out                          false
% 35.45/5.02  
% 35.45/5.02  ------ Global Options
% 35.45/5.02  
% 35.45/5.02  --schedule                              default
% 35.45/5.02  --add_important_lit                     false
% 35.45/5.02  --prop_solver_per_cl                    1000
% 35.45/5.02  --min_unsat_core                        false
% 35.45/5.02  --soft_assumptions                      false
% 35.45/5.02  --soft_lemma_size                       3
% 35.45/5.02  --prop_impl_unit_size                   0
% 35.45/5.02  --prop_impl_unit                        []
% 35.45/5.02  --share_sel_clauses                     true
% 35.45/5.02  --reset_solvers                         false
% 35.45/5.02  --bc_imp_inh                            [conj_cone]
% 35.45/5.02  --conj_cone_tolerance                   3.
% 35.45/5.02  --extra_neg_conj                        none
% 35.45/5.02  --large_theory_mode                     true
% 35.45/5.02  --prolific_symb_bound                   200
% 35.45/5.02  --lt_threshold                          2000
% 35.45/5.02  --clause_weak_htbl                      true
% 35.45/5.02  --gc_record_bc_elim                     false
% 35.45/5.02  
% 35.45/5.02  ------ Preprocessing Options
% 35.45/5.02  
% 35.45/5.02  --preprocessing_flag                    true
% 35.45/5.02  --time_out_prep_mult                    0.1
% 35.45/5.02  --splitting_mode                        input
% 35.45/5.02  --splitting_grd                         true
% 35.45/5.02  --splitting_cvd                         false
% 35.45/5.02  --splitting_cvd_svl                     false
% 35.45/5.02  --splitting_nvd                         32
% 35.45/5.02  --sub_typing                            true
% 35.45/5.02  --prep_gs_sim                           true
% 35.45/5.02  --prep_unflatten                        true
% 35.45/5.02  --prep_res_sim                          true
% 35.45/5.02  --prep_upred                            true
% 35.45/5.02  --prep_sem_filter                       exhaustive
% 35.45/5.02  --prep_sem_filter_out                   false
% 35.45/5.02  --pred_elim                             true
% 35.45/5.02  --res_sim_input                         true
% 35.45/5.02  --eq_ax_congr_red                       true
% 35.45/5.02  --pure_diseq_elim                       true
% 35.45/5.02  --brand_transform                       false
% 35.45/5.02  --non_eq_to_eq                          false
% 35.45/5.02  --prep_def_merge                        true
% 35.45/5.02  --prep_def_merge_prop_impl              false
% 35.45/5.02  --prep_def_merge_mbd                    true
% 35.45/5.02  --prep_def_merge_tr_red                 false
% 35.45/5.02  --prep_def_merge_tr_cl                  false
% 35.45/5.02  --smt_preprocessing                     true
% 35.45/5.02  --smt_ac_axioms                         fast
% 35.45/5.02  --preprocessed_out                      false
% 35.45/5.02  --preprocessed_stats                    false
% 35.45/5.02  
% 35.45/5.02  ------ Abstraction refinement Options
% 35.45/5.02  
% 35.45/5.02  --abstr_ref                             []
% 35.45/5.02  --abstr_ref_prep                        false
% 35.45/5.02  --abstr_ref_until_sat                   false
% 35.45/5.02  --abstr_ref_sig_restrict                funpre
% 35.45/5.02  --abstr_ref_af_restrict_to_split_sk     false
% 35.45/5.02  --abstr_ref_under                       []
% 35.45/5.02  
% 35.45/5.02  ------ SAT Options
% 35.45/5.02  
% 35.45/5.02  --sat_mode                              false
% 35.45/5.02  --sat_fm_restart_options                ""
% 35.45/5.02  --sat_gr_def                            false
% 35.45/5.02  --sat_epr_types                         true
% 35.45/5.02  --sat_non_cyclic_types                  false
% 35.45/5.02  --sat_finite_models                     false
% 35.45/5.02  --sat_fm_lemmas                         false
% 35.45/5.02  --sat_fm_prep                           false
% 35.45/5.02  --sat_fm_uc_incr                        true
% 35.45/5.02  --sat_out_model                         small
% 35.45/5.02  --sat_out_clauses                       false
% 35.45/5.02  
% 35.45/5.02  ------ QBF Options
% 35.45/5.02  
% 35.45/5.02  --qbf_mode                              false
% 35.45/5.02  --qbf_elim_univ                         false
% 35.45/5.02  --qbf_dom_inst                          none
% 35.45/5.02  --qbf_dom_pre_inst                      false
% 35.45/5.02  --qbf_sk_in                             false
% 35.45/5.02  --qbf_pred_elim                         true
% 35.45/5.02  --qbf_split                             512
% 35.45/5.02  
% 35.45/5.02  ------ BMC1 Options
% 35.45/5.02  
% 35.45/5.02  --bmc1_incremental                      false
% 35.45/5.02  --bmc1_axioms                           reachable_all
% 35.45/5.02  --bmc1_min_bound                        0
% 35.45/5.02  --bmc1_max_bound                        -1
% 35.45/5.02  --bmc1_max_bound_default                -1
% 35.45/5.02  --bmc1_symbol_reachability              true
% 35.45/5.02  --bmc1_property_lemmas                  false
% 35.45/5.02  --bmc1_k_induction                      false
% 35.45/5.02  --bmc1_non_equiv_states                 false
% 35.45/5.02  --bmc1_deadlock                         false
% 35.45/5.02  --bmc1_ucm                              false
% 35.45/5.02  --bmc1_add_unsat_core                   none
% 35.45/5.02  --bmc1_unsat_core_children              false
% 35.45/5.02  --bmc1_unsat_core_extrapolate_axioms    false
% 35.45/5.02  --bmc1_out_stat                         full
% 35.45/5.02  --bmc1_ground_init                      false
% 35.45/5.02  --bmc1_pre_inst_next_state              false
% 35.45/5.02  --bmc1_pre_inst_state                   false
% 35.45/5.02  --bmc1_pre_inst_reach_state             false
% 35.45/5.02  --bmc1_out_unsat_core                   false
% 35.45/5.02  --bmc1_aig_witness_out                  false
% 35.45/5.02  --bmc1_verbose                          false
% 35.45/5.02  --bmc1_dump_clauses_tptp                false
% 35.45/5.02  --bmc1_dump_unsat_core_tptp             false
% 35.45/5.02  --bmc1_dump_file                        -
% 35.45/5.02  --bmc1_ucm_expand_uc_limit              128
% 35.45/5.02  --bmc1_ucm_n_expand_iterations          6
% 35.45/5.02  --bmc1_ucm_extend_mode                  1
% 35.45/5.02  --bmc1_ucm_init_mode                    2
% 35.45/5.02  --bmc1_ucm_cone_mode                    none
% 35.45/5.02  --bmc1_ucm_reduced_relation_type        0
% 35.45/5.02  --bmc1_ucm_relax_model                  4
% 35.45/5.02  --bmc1_ucm_full_tr_after_sat            true
% 35.45/5.02  --bmc1_ucm_expand_neg_assumptions       false
% 35.45/5.02  --bmc1_ucm_layered_model                none
% 35.45/5.02  --bmc1_ucm_max_lemma_size               10
% 35.45/5.02  
% 35.45/5.02  ------ AIG Options
% 35.45/5.02  
% 35.45/5.02  --aig_mode                              false
% 35.45/5.02  
% 35.45/5.02  ------ Instantiation Options
% 35.45/5.02  
% 35.45/5.02  --instantiation_flag                    true
% 35.45/5.02  --inst_sos_flag                         true
% 35.45/5.02  --inst_sos_phase                        true
% 35.45/5.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.45/5.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.45/5.02  --inst_lit_sel_side                     num_symb
% 35.45/5.02  --inst_solver_per_active                1400
% 35.45/5.02  --inst_solver_calls_frac                1.
% 35.45/5.02  --inst_passive_queue_type               priority_queues
% 35.45/5.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.45/5.02  --inst_passive_queues_freq              [25;2]
% 35.45/5.02  --inst_dismatching                      true
% 35.45/5.02  --inst_eager_unprocessed_to_passive     true
% 35.45/5.02  --inst_prop_sim_given                   true
% 35.45/5.02  --inst_prop_sim_new                     false
% 35.45/5.02  --inst_subs_new                         false
% 35.45/5.02  --inst_eq_res_simp                      false
% 35.45/5.02  --inst_subs_given                       false
% 35.45/5.02  --inst_orphan_elimination               true
% 35.45/5.02  --inst_learning_loop_flag               true
% 35.45/5.02  --inst_learning_start                   3000
% 35.45/5.02  --inst_learning_factor                  2
% 35.45/5.02  --inst_start_prop_sim_after_learn       3
% 35.45/5.02  --inst_sel_renew                        solver
% 35.45/5.02  --inst_lit_activity_flag                true
% 35.45/5.02  --inst_restr_to_given                   false
% 35.45/5.02  --inst_activity_threshold               500
% 35.45/5.02  --inst_out_proof                        true
% 35.45/5.02  
% 35.45/5.02  ------ Resolution Options
% 35.45/5.02  
% 35.45/5.02  --resolution_flag                       true
% 35.45/5.02  --res_lit_sel                           adaptive
% 35.45/5.02  --res_lit_sel_side                      none
% 35.45/5.02  --res_ordering                          kbo
% 35.45/5.02  --res_to_prop_solver                    active
% 35.45/5.02  --res_prop_simpl_new                    false
% 35.45/5.02  --res_prop_simpl_given                  true
% 35.45/5.02  --res_passive_queue_type                priority_queues
% 35.45/5.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.45/5.02  --res_passive_queues_freq               [15;5]
% 35.45/5.02  --res_forward_subs                      full
% 35.45/5.02  --res_backward_subs                     full
% 35.45/5.02  --res_forward_subs_resolution           true
% 35.45/5.02  --res_backward_subs_resolution          true
% 35.45/5.02  --res_orphan_elimination                true
% 35.45/5.02  --res_time_limit                        2.
% 35.45/5.02  --res_out_proof                         true
% 35.45/5.02  
% 35.45/5.02  ------ Superposition Options
% 35.45/5.02  
% 35.45/5.02  --superposition_flag                    true
% 35.45/5.02  --sup_passive_queue_type                priority_queues
% 35.45/5.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.45/5.02  --sup_passive_queues_freq               [8;1;4]
% 35.45/5.02  --demod_completeness_check              fast
% 35.45/5.02  --demod_use_ground                      true
% 35.45/5.02  --sup_to_prop_solver                    passive
% 35.45/5.02  --sup_prop_simpl_new                    true
% 35.45/5.02  --sup_prop_simpl_given                  true
% 35.45/5.02  --sup_fun_splitting                     true
% 35.45/5.02  --sup_smt_interval                      50000
% 35.45/5.02  
% 35.45/5.02  ------ Superposition Simplification Setup
% 35.45/5.02  
% 35.45/5.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.45/5.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.45/5.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.45/5.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.45/5.02  --sup_full_triv                         [TrivRules;PropSubs]
% 35.45/5.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.45/5.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.45/5.02  --sup_immed_triv                        [TrivRules]
% 35.45/5.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.45/5.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.45/5.02  --sup_immed_bw_main                     []
% 35.45/5.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.45/5.02  --sup_input_triv                        [Unflattening;TrivRules]
% 35.45/5.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.45/5.02  --sup_input_bw                          []
% 35.45/5.02  
% 35.45/5.02  ------ Combination Options
% 35.45/5.02  
% 35.45/5.02  --comb_res_mult                         3
% 35.45/5.02  --comb_sup_mult                         2
% 35.45/5.02  --comb_inst_mult                        10
% 35.45/5.02  
% 35.45/5.02  ------ Debug Options
% 35.45/5.02  
% 35.45/5.02  --dbg_backtrace                         false
% 35.45/5.02  --dbg_dump_prop_clauses                 false
% 35.45/5.02  --dbg_dump_prop_clauses_file            -
% 35.45/5.02  --dbg_out_stat                          false
% 35.45/5.02  ------ Parsing...
% 35.45/5.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.45/5.02  
% 35.45/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.45/5.02  
% 35.45/5.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.45/5.02  
% 35.45/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.45/5.02  ------ Proving...
% 35.45/5.02  ------ Problem Properties 
% 35.45/5.02  
% 35.45/5.02  
% 35.45/5.02  clauses                                 14
% 35.45/5.02  conjectures                             1
% 35.45/5.02  EPR                                     0
% 35.45/5.02  Horn                                    14
% 35.45/5.02  unary                                   10
% 35.45/5.02  binary                                  4
% 35.45/5.02  lits                                    18
% 35.45/5.02  lits eq                                 12
% 35.45/5.02  fd_pure                                 0
% 35.45/5.02  fd_pseudo                               0
% 35.45/5.02  fd_cond                                 0
% 35.45/5.02  fd_pseudo_cond                          0
% 35.45/5.02  AC symbols                              2
% 35.45/5.02  
% 35.45/5.02  ------ Schedule dynamic 5 is on 
% 35.45/5.02  
% 35.45/5.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.45/5.02  
% 35.45/5.02  
% 35.45/5.02  ------ 
% 35.45/5.02  Current options:
% 35.45/5.02  ------ 
% 35.45/5.02  
% 35.45/5.02  ------ Input Options
% 35.45/5.02  
% 35.45/5.02  --out_options                           all
% 35.45/5.02  --tptp_safe_out                         true
% 35.45/5.02  --problem_path                          ""
% 35.45/5.02  --include_path                          ""
% 35.45/5.02  --clausifier                            res/vclausify_rel
% 35.45/5.02  --clausifier_options                    ""
% 35.45/5.02  --stdin                                 false
% 35.45/5.02  --stats_out                             all
% 35.45/5.02  
% 35.45/5.02  ------ General Options
% 35.45/5.02  
% 35.45/5.02  --fof                                   false
% 35.45/5.02  --time_out_real                         305.
% 35.45/5.02  --time_out_virtual                      -1.
% 35.45/5.02  --symbol_type_check                     false
% 35.45/5.02  --clausify_out                          false
% 35.45/5.02  --sig_cnt_out                           false
% 35.45/5.02  --trig_cnt_out                          false
% 35.45/5.02  --trig_cnt_out_tolerance                1.
% 35.45/5.02  --trig_cnt_out_sk_spl                   false
% 35.45/5.02  --abstr_cl_out                          false
% 35.45/5.02  
% 35.45/5.02  ------ Global Options
% 35.45/5.02  
% 35.45/5.02  --schedule                              default
% 35.45/5.02  --add_important_lit                     false
% 35.45/5.02  --prop_solver_per_cl                    1000
% 35.45/5.02  --min_unsat_core                        false
% 35.45/5.02  --soft_assumptions                      false
% 35.45/5.02  --soft_lemma_size                       3
% 35.45/5.02  --prop_impl_unit_size                   0
% 35.45/5.02  --prop_impl_unit                        []
% 35.45/5.02  --share_sel_clauses                     true
% 35.45/5.02  --reset_solvers                         false
% 35.45/5.02  --bc_imp_inh                            [conj_cone]
% 35.45/5.02  --conj_cone_tolerance                   3.
% 35.45/5.02  --extra_neg_conj                        none
% 35.45/5.02  --large_theory_mode                     true
% 35.45/5.02  --prolific_symb_bound                   200
% 35.45/5.02  --lt_threshold                          2000
% 35.45/5.02  --clause_weak_htbl                      true
% 35.45/5.02  --gc_record_bc_elim                     false
% 35.45/5.02  
% 35.45/5.02  ------ Preprocessing Options
% 35.45/5.02  
% 35.45/5.02  --preprocessing_flag                    true
% 35.45/5.02  --time_out_prep_mult                    0.1
% 35.45/5.02  --splitting_mode                        input
% 35.45/5.02  --splitting_grd                         true
% 35.45/5.02  --splitting_cvd                         false
% 35.45/5.02  --splitting_cvd_svl                     false
% 35.45/5.02  --splitting_nvd                         32
% 35.45/5.02  --sub_typing                            true
% 35.45/5.02  --prep_gs_sim                           true
% 35.45/5.02  --prep_unflatten                        true
% 35.45/5.02  --prep_res_sim                          true
% 35.45/5.02  --prep_upred                            true
% 35.45/5.02  --prep_sem_filter                       exhaustive
% 35.45/5.02  --prep_sem_filter_out                   false
% 35.45/5.02  --pred_elim                             true
% 35.45/5.02  --res_sim_input                         true
% 35.45/5.02  --eq_ax_congr_red                       true
% 35.45/5.02  --pure_diseq_elim                       true
% 35.45/5.02  --brand_transform                       false
% 35.45/5.02  --non_eq_to_eq                          false
% 35.45/5.02  --prep_def_merge                        true
% 35.45/5.02  --prep_def_merge_prop_impl              false
% 35.45/5.02  --prep_def_merge_mbd                    true
% 35.45/5.02  --prep_def_merge_tr_red                 false
% 35.45/5.02  --prep_def_merge_tr_cl                  false
% 35.45/5.02  --smt_preprocessing                     true
% 35.45/5.02  --smt_ac_axioms                         fast
% 35.45/5.02  --preprocessed_out                      false
% 35.45/5.02  --preprocessed_stats                    false
% 35.45/5.02  
% 35.45/5.02  ------ Abstraction refinement Options
% 35.45/5.02  
% 35.45/5.02  --abstr_ref                             []
% 35.45/5.02  --abstr_ref_prep                        false
% 35.45/5.02  --abstr_ref_until_sat                   false
% 35.45/5.02  --abstr_ref_sig_restrict                funpre
% 35.45/5.02  --abstr_ref_af_restrict_to_split_sk     false
% 35.45/5.02  --abstr_ref_under                       []
% 35.45/5.02  
% 35.45/5.02  ------ SAT Options
% 35.45/5.02  
% 35.45/5.02  --sat_mode                              false
% 35.45/5.02  --sat_fm_restart_options                ""
% 35.45/5.02  --sat_gr_def                            false
% 35.45/5.02  --sat_epr_types                         true
% 35.45/5.02  --sat_non_cyclic_types                  false
% 35.45/5.02  --sat_finite_models                     false
% 35.45/5.02  --sat_fm_lemmas                         false
% 35.45/5.02  --sat_fm_prep                           false
% 35.45/5.02  --sat_fm_uc_incr                        true
% 35.45/5.02  --sat_out_model                         small
% 35.45/5.02  --sat_out_clauses                       false
% 35.45/5.02  
% 35.45/5.02  ------ QBF Options
% 35.45/5.02  
% 35.45/5.02  --qbf_mode                              false
% 35.45/5.02  --qbf_elim_univ                         false
% 35.45/5.02  --qbf_dom_inst                          none
% 35.45/5.02  --qbf_dom_pre_inst                      false
% 35.45/5.02  --qbf_sk_in                             false
% 35.45/5.02  --qbf_pred_elim                         true
% 35.45/5.02  --qbf_split                             512
% 35.45/5.02  
% 35.45/5.02  ------ BMC1 Options
% 35.45/5.02  
% 35.45/5.02  --bmc1_incremental                      false
% 35.45/5.02  --bmc1_axioms                           reachable_all
% 35.45/5.02  --bmc1_min_bound                        0
% 35.45/5.02  --bmc1_max_bound                        -1
% 35.45/5.02  --bmc1_max_bound_default                -1
% 35.45/5.02  --bmc1_symbol_reachability              true
% 35.45/5.02  --bmc1_property_lemmas                  false
% 35.45/5.02  --bmc1_k_induction                      false
% 35.45/5.02  --bmc1_non_equiv_states                 false
% 35.45/5.02  --bmc1_deadlock                         false
% 35.45/5.02  --bmc1_ucm                              false
% 35.45/5.02  --bmc1_add_unsat_core                   none
% 35.45/5.02  --bmc1_unsat_core_children              false
% 35.45/5.02  --bmc1_unsat_core_extrapolate_axioms    false
% 35.45/5.02  --bmc1_out_stat                         full
% 35.45/5.02  --bmc1_ground_init                      false
% 35.45/5.02  --bmc1_pre_inst_next_state              false
% 35.45/5.02  --bmc1_pre_inst_state                   false
% 35.45/5.02  --bmc1_pre_inst_reach_state             false
% 35.45/5.02  --bmc1_out_unsat_core                   false
% 35.45/5.02  --bmc1_aig_witness_out                  false
% 35.45/5.02  --bmc1_verbose                          false
% 35.45/5.02  --bmc1_dump_clauses_tptp                false
% 35.45/5.02  --bmc1_dump_unsat_core_tptp             false
% 35.45/5.02  --bmc1_dump_file                        -
% 35.45/5.02  --bmc1_ucm_expand_uc_limit              128
% 35.45/5.02  --bmc1_ucm_n_expand_iterations          6
% 35.45/5.02  --bmc1_ucm_extend_mode                  1
% 35.45/5.02  --bmc1_ucm_init_mode                    2
% 35.45/5.02  --bmc1_ucm_cone_mode                    none
% 35.45/5.02  --bmc1_ucm_reduced_relation_type        0
% 35.45/5.02  --bmc1_ucm_relax_model                  4
% 35.45/5.02  --bmc1_ucm_full_tr_after_sat            true
% 35.45/5.02  --bmc1_ucm_expand_neg_assumptions       false
% 35.45/5.02  --bmc1_ucm_layered_model                none
% 35.45/5.02  --bmc1_ucm_max_lemma_size               10
% 35.45/5.02  
% 35.45/5.02  ------ AIG Options
% 35.45/5.02  
% 35.45/5.02  --aig_mode                              false
% 35.45/5.02  
% 35.45/5.02  ------ Instantiation Options
% 35.45/5.02  
% 35.45/5.02  --instantiation_flag                    true
% 35.45/5.02  --inst_sos_flag                         true
% 35.45/5.02  --inst_sos_phase                        true
% 35.45/5.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.45/5.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.45/5.02  --inst_lit_sel_side                     none
% 35.45/5.02  --inst_solver_per_active                1400
% 35.45/5.02  --inst_solver_calls_frac                1.
% 35.45/5.02  --inst_passive_queue_type               priority_queues
% 35.45/5.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.45/5.02  --inst_passive_queues_freq              [25;2]
% 35.45/5.02  --inst_dismatching                      true
% 35.45/5.02  --inst_eager_unprocessed_to_passive     true
% 35.45/5.02  --inst_prop_sim_given                   true
% 35.45/5.02  --inst_prop_sim_new                     false
% 35.45/5.02  --inst_subs_new                         false
% 35.45/5.02  --inst_eq_res_simp                      false
% 35.45/5.02  --inst_subs_given                       false
% 35.45/5.02  --inst_orphan_elimination               true
% 35.45/5.02  --inst_learning_loop_flag               true
% 35.45/5.02  --inst_learning_start                   3000
% 35.45/5.02  --inst_learning_factor                  2
% 35.45/5.02  --inst_start_prop_sim_after_learn       3
% 35.45/5.02  --inst_sel_renew                        solver
% 35.45/5.02  --inst_lit_activity_flag                true
% 35.45/5.02  --inst_restr_to_given                   false
% 35.45/5.02  --inst_activity_threshold               500
% 35.45/5.02  --inst_out_proof                        true
% 35.45/5.02  
% 35.45/5.02  ------ Resolution Options
% 35.45/5.02  
% 35.45/5.02  --resolution_flag                       false
% 35.45/5.02  --res_lit_sel                           adaptive
% 35.45/5.02  --res_lit_sel_side                      none
% 35.45/5.02  --res_ordering                          kbo
% 35.45/5.02  --res_to_prop_solver                    active
% 35.45/5.02  --res_prop_simpl_new                    false
% 35.45/5.02  --res_prop_simpl_given                  true
% 35.45/5.02  --res_passive_queue_type                priority_queues
% 35.45/5.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.45/5.02  --res_passive_queues_freq               [15;5]
% 35.45/5.02  --res_forward_subs                      full
% 35.45/5.02  --res_backward_subs                     full
% 35.45/5.02  --res_forward_subs_resolution           true
% 35.45/5.02  --res_backward_subs_resolution          true
% 35.45/5.02  --res_orphan_elimination                true
% 35.45/5.02  --res_time_limit                        2.
% 35.45/5.02  --res_out_proof                         true
% 35.45/5.02  
% 35.45/5.02  ------ Superposition Options
% 35.45/5.02  
% 35.45/5.02  --superposition_flag                    true
% 35.45/5.02  --sup_passive_queue_type                priority_queues
% 35.45/5.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.45/5.02  --sup_passive_queues_freq               [8;1;4]
% 35.45/5.02  --demod_completeness_check              fast
% 35.45/5.02  --demod_use_ground                      true
% 35.45/5.02  --sup_to_prop_solver                    passive
% 35.45/5.02  --sup_prop_simpl_new                    true
% 35.45/5.02  --sup_prop_simpl_given                  true
% 35.45/5.02  --sup_fun_splitting                     true
% 35.45/5.02  --sup_smt_interval                      50000
% 35.45/5.02  
% 35.45/5.02  ------ Superposition Simplification Setup
% 35.45/5.02  
% 35.45/5.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.45/5.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.45/5.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.45/5.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.45/5.02  --sup_full_triv                         [TrivRules;PropSubs]
% 35.45/5.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.45/5.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.45/5.02  --sup_immed_triv                        [TrivRules]
% 35.45/5.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.45/5.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.45/5.02  --sup_immed_bw_main                     []
% 35.45/5.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.45/5.02  --sup_input_triv                        [Unflattening;TrivRules]
% 35.45/5.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.45/5.02  --sup_input_bw                          []
% 35.45/5.02  
% 35.45/5.02  ------ Combination Options
% 35.45/5.02  
% 35.45/5.02  --comb_res_mult                         3
% 35.45/5.02  --comb_sup_mult                         2
% 35.45/5.02  --comb_inst_mult                        10
% 35.45/5.02  
% 35.45/5.02  ------ Debug Options
% 35.45/5.02  
% 35.45/5.02  --dbg_backtrace                         false
% 35.45/5.02  --dbg_dump_prop_clauses                 false
% 35.45/5.02  --dbg_dump_prop_clauses_file            -
% 35.45/5.02  --dbg_out_stat                          false
% 35.45/5.02  
% 35.45/5.02  
% 35.45/5.02  
% 35.45/5.02  
% 35.45/5.02  ------ Proving...
% 35.45/5.02  
% 35.45/5.02  
% 35.45/5.02  % SZS status Theorem for theBenchmark.p
% 35.45/5.02  
% 35.45/5.02  % SZS output start CNFRefutation for theBenchmark.p
% 35.45/5.02  
% 35.45/5.02  fof(f1,axiom,(
% 35.45/5.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f24,plain,(
% 35.45/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.45/5.02    inference(cnf_transformation,[],[f1])).
% 35.45/5.02  
% 35.45/5.02  fof(f15,conjecture,(
% 35.45/5.02    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f16,negated_conjecture,(
% 35.45/5.02    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 35.45/5.02    inference(negated_conjecture,[],[f15])).
% 35.45/5.02  
% 35.45/5.02  fof(f20,plain,(
% 35.45/5.02    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 35.45/5.02    inference(ennf_transformation,[],[f16])).
% 35.45/5.02  
% 35.45/5.02  fof(f22,plain,(
% 35.45/5.02    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 35.45/5.02    introduced(choice_axiom,[])).
% 35.45/5.02  
% 35.45/5.02  fof(f23,plain,(
% 35.45/5.02    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 35.45/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22])).
% 35.45/5.02  
% 35.45/5.02  fof(f39,plain,(
% 35.45/5.02    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 35.45/5.02    inference(cnf_transformation,[],[f23])).
% 35.45/5.02  
% 35.45/5.02  fof(f5,axiom,(
% 35.45/5.02    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f29,plain,(
% 35.45/5.02    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 35.45/5.02    inference(cnf_transformation,[],[f5])).
% 35.45/5.02  
% 35.45/5.02  fof(f48,plain,(
% 35.45/5.02    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 35.45/5.02    inference(definition_unfolding,[],[f39,f29])).
% 35.45/5.02  
% 35.45/5.02  fof(f13,axiom,(
% 35.45/5.02    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f37,plain,(
% 35.45/5.02    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 35.45/5.02    inference(cnf_transformation,[],[f13])).
% 35.45/5.02  
% 35.45/5.02  fof(f2,axiom,(
% 35.45/5.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f25,plain,(
% 35.45/5.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 35.45/5.02    inference(cnf_transformation,[],[f2])).
% 35.45/5.02  
% 35.45/5.02  fof(f6,axiom,(
% 35.45/5.02    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f30,plain,(
% 35.45/5.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 35.45/5.02    inference(cnf_transformation,[],[f6])).
% 35.45/5.02  
% 35.45/5.02  fof(f8,axiom,(
% 35.45/5.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f19,plain,(
% 35.45/5.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.45/5.02    inference(ennf_transformation,[],[f8])).
% 35.45/5.02  
% 35.45/5.02  fof(f32,plain,(
% 35.45/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.45/5.02    inference(cnf_transformation,[],[f19])).
% 35.45/5.02  
% 35.45/5.02  fof(f10,axiom,(
% 35.45/5.02    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f34,plain,(
% 35.45/5.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 35.45/5.02    inference(cnf_transformation,[],[f10])).
% 35.45/5.02  
% 35.45/5.02  fof(f14,axiom,(
% 35.45/5.02    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f38,plain,(
% 35.45/5.02    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 35.45/5.02    inference(cnf_transformation,[],[f14])).
% 35.45/5.02  
% 35.45/5.02  fof(f41,plain,(
% 35.45/5.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 35.45/5.02    inference(definition_unfolding,[],[f38,f29])).
% 35.45/5.02  
% 35.45/5.02  fof(f46,plain,(
% 35.45/5.02    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 35.45/5.02    inference(definition_unfolding,[],[f34,f29,f41])).
% 35.45/5.02  
% 35.45/5.02  fof(f7,axiom,(
% 35.45/5.02    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f31,plain,(
% 35.45/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 35.45/5.02    inference(cnf_transformation,[],[f7])).
% 35.45/5.02  
% 35.45/5.02  fof(f44,plain,(
% 35.45/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 35.45/5.02    inference(definition_unfolding,[],[f31,f41])).
% 35.45/5.02  
% 35.45/5.02  fof(f12,axiom,(
% 35.45/5.02    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f36,plain,(
% 35.45/5.02    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.45/5.02    inference(cnf_transformation,[],[f12])).
% 35.45/5.02  
% 35.45/5.02  fof(f11,axiom,(
% 35.45/5.02    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f35,plain,(
% 35.45/5.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 35.45/5.02    inference(cnf_transformation,[],[f11])).
% 35.45/5.02  
% 35.45/5.02  fof(f47,plain,(
% 35.45/5.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 35.45/5.02    inference(definition_unfolding,[],[f35,f29,f29])).
% 35.45/5.02  
% 35.45/5.02  fof(f9,axiom,(
% 35.45/5.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f33,plain,(
% 35.45/5.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.45/5.02    inference(cnf_transformation,[],[f9])).
% 35.45/5.02  
% 35.45/5.02  fof(f45,plain,(
% 35.45/5.02    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 35.45/5.02    inference(definition_unfolding,[],[f33,f29])).
% 35.45/5.02  
% 35.45/5.02  fof(f4,axiom,(
% 35.45/5.02    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f21,plain,(
% 35.45/5.02    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 35.45/5.02    inference(nnf_transformation,[],[f4])).
% 35.45/5.02  
% 35.45/5.02  fof(f27,plain,(
% 35.45/5.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 35.45/5.02    inference(cnf_transformation,[],[f21])).
% 35.45/5.02  
% 35.45/5.02  fof(f43,plain,(
% 35.45/5.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0) )),
% 35.45/5.02    inference(definition_unfolding,[],[f27,f29])).
% 35.45/5.02  
% 35.45/5.02  fof(f3,axiom,(
% 35.45/5.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.45/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.45/5.02  
% 35.45/5.02  fof(f17,plain,(
% 35.45/5.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 35.45/5.02    inference(unused_predicate_definition_removal,[],[f3])).
% 35.45/5.02  
% 35.45/5.02  fof(f18,plain,(
% 35.45/5.02    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 35.45/5.02    inference(ennf_transformation,[],[f17])).
% 35.45/5.02  
% 35.45/5.02  fof(f26,plain,(
% 35.45/5.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.45/5.02    inference(cnf_transformation,[],[f18])).
% 35.45/5.02  
% 35.45/5.02  fof(f40,plain,(
% 35.45/5.02    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 35.45/5.02    inference(cnf_transformation,[],[f23])).
% 35.45/5.02  
% 35.45/5.02  cnf(c_0,plain,
% 35.45/5.02      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.45/5.02      inference(cnf_transformation,[],[f24]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_14,negated_conjecture,
% 35.45/5.02      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 35.45/5.02      inference(cnf_transformation,[],[f48]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_12,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.45/5.02      inference(cnf_transformation,[],[f37]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1,plain,
% 35.45/5.02      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 35.45/5.02      inference(cnf_transformation,[],[f25]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_5,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 35.45/5.02      inference(cnf_transformation,[],[f30]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_346,negated_conjecture,
% 35.45/5.02      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(theory_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_14,c_12,c_1,c_5,c_0]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_528,plain,
% 35.45/5.02      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
% 35.45/5.02      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_7,plain,
% 35.45/5.02      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 35.45/5.02      inference(cnf_transformation,[],[f32]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_530,plain,
% 35.45/5.02      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 35.45/5.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1939,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_528,c_530]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_541,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2327,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_541]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2552,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(k3_xboole_0(X0,sK0),X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2327,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_542,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2558,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2327,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_9,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 35.45/5.02      inference(cnf_transformation,[],[f46]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_348,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 35.45/5.02      inference(theory_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_9,c_12,c_1,c_5,c_0]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 35.45/5.02      inference(cnf_transformation,[],[f44]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_349,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 35.45/5.02      inference(theory_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_6,c_12,c_1,c_5,c_0]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_533,plain,
% 35.45/5.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_348,c_349]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_776,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_533,c_12]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_11,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.45/5.02      inference(cnf_transformation,[],[f36]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_651,plain,
% 35.45/5.02      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_782,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_776,c_651]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1046,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_782,c_349]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_10,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 35.45/5.02      inference(cnf_transformation,[],[f47]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_347,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 35.45/5.02      inference(theory_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_10,c_12,c_1,c_5,c_0]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1405,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1046,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1413,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_1405,c_533,c_1046]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1685,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1413,c_349]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1712,plain,
% 35.45/5.02      ( k3_xboole_0(X0,X0) = X0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_1685,c_11,c_651]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_540,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2322,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(sK0,X0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2355,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) = k3_xboole_0(sK0,k3_xboole_0(X0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_540,c_2322]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4478,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0)) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1712,c_2355]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2326,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4531,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_4478,c_2326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2365,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(sK0,X1)) = k3_xboole_0(X1,k3_xboole_0(sK0,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2322,c_541]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6893,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0),k3_xboole_0(sK0,X1)) = k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1),k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_4531,c_2365]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4614,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0),sK0) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_4531,c_2327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2331,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4630,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0),sK0) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_4614,c_2331]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4984,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X0),k3_xboole_0(sK0,X1)) = k3_xboole_0(k3_xboole_0(X0,sK0),X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_4630,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6942,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,sK0)) = k3_xboole_0(k3_xboole_0(X1,sK0),X0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_6893,c_4984]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2500,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,sK0)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2326,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6943,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,sK0),X1) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_6942,c_2500]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_9670,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_2552,c_2558,c_6943]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_936,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X0,X1),X2))))) = k5_xboole_0(X0,X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_12,c_349]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_14243,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_936,c_2322]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_14260,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))))) = sK0 ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_14243,c_1939]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16158,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),X1),k3_xboole_0(X0,k3_xboole_0(X1,sK0)))))) = sK0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_9670,c_14260]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_8,plain,
% 35.45/5.02      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 35.45/5.02      inference(cnf_transformation,[],[f45]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_529,plain,
% 35.45/5.02      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 35.45/5.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_768,plain,
% 35.45/5.02      ( r1_tarski(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_5,c_529]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_769,plain,
% 35.45/5.02      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_768,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_5564,plain,
% 35.45/5.02      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_769]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_15435,plain,
% 35.45/5.02      ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_5564]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16128,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = sK0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_15435,c_530]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2364,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1)) = k3_xboole_0(X1,k3_xboole_0(sK0,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2322,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6451,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1712,c_2364]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6529,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_6451,c_2326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16680,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1)),sK0) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16128,c_6529]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16685,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16128,c_2327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2547,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0) = k3_xboole_0(sK0,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1712,c_2327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2580,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0) = sK0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_2547,c_1712]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16702,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(sK0,sK1),sK0) = sK0 ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_16685,c_2580]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16707,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,sK1)),sK0) = sK0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_16680,c_16702]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2549,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2322,c_2327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2578,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_2549,c_2327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2372,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,sK0)) = k3_xboole_0(X1,k3_xboole_0(sK0,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2322,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_7258,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X0,sK0)))) = k3_xboole_0(k3_xboole_0(X0,sK0),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2372,c_4531]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4610,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_4531,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4634,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_4610,c_2326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6595,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k3_xboole_0(k3_xboole_0(X0,sK0),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2331,c_6529]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1909,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1712,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1921,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1712,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2477,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k3_xboole_0(k3_xboole_0(X0,X1),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_542,c_2326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2356,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_541,c_2322]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2513,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),sK0) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_2477,c_2356]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4902,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_4634,c_541]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6448,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X2)))) = k3_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(sK0,X2)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_541,c_2364]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2357,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_542,c_2322]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_5275,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X2)))) = k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X2,X1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2357,c_540]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6532,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(sK0,X2)) = k3_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X2,X0))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_6448,c_5275]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6691,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_6595,c_1909,c_1921,c_2513,c_4902,c_6532]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_7262,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,sK0),sK0) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_7258,c_4634,c_6691]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16708,plain,
% 35.45/5.02      ( k3_xboole_0(sK1,sK0) = sK0 ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_16707,c_2327,c_2578,c_7262]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16892,plain,
% 35.45/5.02      ( k3_xboole_0(sK1,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16708,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_18079,plain,
% 35.45/5.02      ( k3_xboole_0(sK1,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,X0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_16892]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_18363,plain,
% 35.45/5.02      ( k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(X0,sK0),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_18079,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2330,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_540]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2694,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2330,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_18107,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1)) = k3_xboole_0(sK1,k3_xboole_0(X1,k3_xboole_0(X0,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2694,c_16892]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_5145,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1)) = k3_xboole_0(sK0,k3_xboole_0(X0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_2356]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_18205,plain,
% 35.45/5.02      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_18107,c_5145]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_18420,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(sK0,X0),X1) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_18363,c_6943,c_18205]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_39551,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k3_xboole_0(X0,sK0)))))) = sK0 ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_16158,c_16158,c_18420]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1394,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_5,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_942,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,X2))))) = k3_xboole_0(X0,X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_5,c_349]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_544,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2005,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,X3)))) = k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3)))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_347,c_544]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_21590,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = k3_xboole_0(X0,X1) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_942,c_2005]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_21693,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X1,X1)))) = k3_xboole_0(X0,X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1712,c_21590]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_21886,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_21693,c_11,c_533,c_1413]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22263,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_21886,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22431,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_22263,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_46047,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_22431]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_53182,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_46047]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1392,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_59537,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X2,k3_xboole_0(X1,k3_xboole_0(X0,X3)))) = k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X3,X0)))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_53182,c_1392]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_59670,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X2,k3_xboole_0(X1,k3_xboole_0(X0,X3)))) = k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X3)))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_59537,c_53182]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_46276,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_22431,c_540]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22278,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_21886,c_541]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22202,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X1,X0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_21886]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22667,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,X1),X2))) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_22202,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22801,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X1,X2)))) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_22667,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22281,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,X1)))) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_21886,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22295,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X0))) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_21886,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22418,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_22281,c_22295]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22802,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X2,X0),X1) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_22801,c_1909,c_22418]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_46379,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_46276,c_1909,c_22278,c_22802]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_59671,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3)))) = k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X0,k3_xboole_0(X2,X3)))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_59670,c_46379]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1528,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_540,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_56872,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X2,k3_xboole_0(X1,k3_xboole_0(X0,X3)))) = k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X3)))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_46047,c_1392]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_57005,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3)))) = k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X3)))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_56872,c_46379]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1399,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_5,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1417,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_1399,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1403,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_5,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1418,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_1417,c_1403]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_57006,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3)))) = k3_xboole_0(X2,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X2,X3))),X1)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_57005,c_1418,c_46379]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_59672,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3)))) = k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X3)))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_59671,c_1528,c_57006]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_53322,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_46047,c_0]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_60119,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X3))) = k3_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_542,c_53322]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_53364,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X3))) = k3_xboole_0(X2,k3_xboole_0(X3,k3_xboole_0(X0,X1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_46047,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_60497,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_60119,c_53364]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_64821,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X2,X0),k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_1394,c_1394,c_59672,c_60497]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_64980,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_64821]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70399,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_64980]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_83062,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),X0))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_39551,c_70399]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2703,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X1,sK0)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2330,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2700,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2330,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2349,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(sK0,X0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_2322]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2955,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2349,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2962,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k1_xboole_0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_2955,c_533,c_2700]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20072,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X0,sK0)) = k1_xboole_0 ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_2700,c_2962]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20120,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k1_xboole_0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_5,c_20072]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_40962,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1)),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k1_xboole_0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2703,c_20120]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_41092,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k1_xboole_0 ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_40962,c_5145]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_84171,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))) = k1_xboole_0 ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_83062,c_11,c_533,c_1413,c_41092]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70560,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_64980,c_541]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_59536,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X0))) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_53182,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_84721,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_70560,c_59536]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_5557,plain,
% 35.45/5.02      ( r1_tarski(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k3_xboole_0(X2,X0)) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_769]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_14547,plain,
% 35.45/5.02      ( r1_tarski(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k3_xboole_0(X0,X2)) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_5557]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_34191,plain,
% 35.45/5.02      ( r1_tarski(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)),k3_xboole_0(sK0,X1)) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2322,c_14547]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_35783,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)),k3_xboole_0(sK0,X1)) = k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_34191,c_530]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2370,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) = k3_xboole_0(X0,k3_xboole_0(sK0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2322,c_540]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22334,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)),k3_xboole_0(sK0,X1)) = k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_21886,c_2370]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2498,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2326,c_540]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_9007,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1))) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_541,c_2498]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22393,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)),k3_xboole_0(sK0,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_22334,c_9007]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_34189,plain,
% 35.45/5.02      ( r1_tarski(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_14547]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_35328,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_34189,c_530]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1938,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_529,c_530]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2557,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2327,c_0]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_3763,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2349,c_2557]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_3789,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_3763,c_2557]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_35329,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_35328,c_1938,c_3789]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_35376,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_35328,c_35329]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_35784,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)) = k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_35783,c_22393,c_35376]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_85174,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_84721,c_2327,c_35784]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_90402,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_85174,c_1392]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_90571,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_90402,c_1939]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_91057,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k1_xboole_0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_84171,c_90571]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_91062,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) = k5_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_90571]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_91897,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k1_xboole_0)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_91057,c_91062]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2495,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)))) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2326,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2506,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_2495,c_2326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16921,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(X0,sK0))) = k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16708,c_2506]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16930,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0) = k3_xboole_0(sK1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16708,c_2500]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16934,plain,
% 35.45/5.02      ( k3_xboole_0(sK1,k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_16930,c_2578]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16942,plain,
% 35.45/5.02      ( k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_16921,c_16934]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4896,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,sK0),X1)) = k3_xboole_0(k3_xboole_0(X0,sK0),X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_4634,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4901,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,sK0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_4634,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_12949,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_4896,c_4901,c_6943]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_12985,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_12949]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70328,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),X1)) = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_64980]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_75258,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK0))),X1)) = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_12985,c_70328]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_780,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_12,c_533]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1042,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_780,c_782]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1052,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_1042,c_11]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1251,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1052,c_1052]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1371,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_12,c_1251]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20153,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X1,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_20072,c_1371]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20174,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X1,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_20153,c_11]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_945,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X2)) = k3_xboole_0(X0,X2) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_349,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_29067,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK0),X0)) = k3_xboole_0(sK0,X0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_20174,c_945]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22213,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2326,c_21886]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22482,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_22213,c_2326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_23355,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),X1),sK0),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),X1),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_9670,c_22482]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_23474,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),sK0),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_23355,c_18420]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4979,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0)),sK0) = k3_xboole_0(k3_xboole_0(X0,sK0),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2331,c_4630]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_5010,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,sK0),sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_4979,c_1909,c_2513,c_4902]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_5011,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(sK0,X0),sK0) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_5010,c_1909,c_1921,c_2513]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_23475,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X0,sK0)),sK0)) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_23474,c_2513,c_5011,c_6943]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2566,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2327,c_540]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_10849,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),X2)) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X2) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2566,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_7228,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(X1,sK0),X2)) = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK0,X0)),X2) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2372,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6878,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,k3_xboole_0(X2,sK0))) = k3_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(sK0,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_541,c_2365]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6959,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,k3_xboole_0(X2,sK0))) = k3_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X0,X2))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_6878,c_6532]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_7273,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X1,X2))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),X2) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_7228,c_6943,c_6959]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_9703,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_540,c_9670]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2492,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2326,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_8556,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X2)))) = k3_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_541,c_2492]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_7060,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X2)))) = k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK0,X2))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2370,c_540]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_8654,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(sK0,X2))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_8556,c_7060]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_9825,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(sK0,X2))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_9703,c_7273,c_8654]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_10917,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(sK0,X2))) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_10849,c_7273,c_9825]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_11546,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))))) = k3_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_541,c_2694]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_5253,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))))) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X1),X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_541,c_2357]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_11641,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_11546,c_5253]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_12965,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,sK0)))) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_5,c_12949]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_13147,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,sK0)))) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_12965,c_11641]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_23476,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(sK0,k3_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_23475,c_10917,c_11641,c_13147]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_23477,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,X1))) = k3_xboole_0(sK0,k3_xboole_0(X0,X1)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_23476,c_18420]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_29098,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,X0) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_29067,c_4901,c_18420,c_23477]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_14242,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))),sK0) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_936,c_2326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_14261,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))),sK0) = sK0 ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_14242,c_1939]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16476,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))),sK0) = sK0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_544,c_14261]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_46102,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))),k3_xboole_0(sK0,X1)) = k3_xboole_0(sK0,k3_xboole_0(sK0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16476,c_22431]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_30450,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))),k3_xboole_0(sK0,X1)) = k3_xboole_0(sK0,X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16476,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_46661,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_46102,c_30450]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_76159,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),X1)) = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(sK0,X0)))) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_75258,c_29098,c_46661]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70380,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X1,sK0))))) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(sK0,X1))))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_12985,c_64980]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70493,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_64980,c_21886]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70609,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_64980,c_6529]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70614,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_64980,c_2322]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70638,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),X1))) = k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X1)),sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_64980,c_9670]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_11584,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1))) = k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2694,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2943,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2349,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2945,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2349,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2964,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X1))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_2943,c_2945]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_11628,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_11584,c_2349,c_2964]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1559,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_541,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_11629,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_11628,c_1559]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70962,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X1)),sK0)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_70638,c_11629]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2559,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2327,c_541]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_56650,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(sK0,X1),X2))) = k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k5_xboole_0(k3_xboole_0(sK0,X1),k3_xboole_0(k3_xboole_0(sK0,X1),X2))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2559,c_1392]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_10208,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(sK0,X1),X2)) = k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2559,c_541]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22274,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))))) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_21886,c_21590]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22424,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_22274,c_11,c_533,c_1413]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_8596,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1))) = k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2492,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2486,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1))) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2326,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2488,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1)) = k3_xboole_0(k3_xboole_0(X0,sK0),X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2326,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2507,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1))) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X0,sK0),X1)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_2486,c_2488]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_8632,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_8596,c_2326,c_2506,c_2507,c_6943]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45069,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,sK0)))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k5_xboole_0(sK0,k3_xboole_0(X2,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_22424,c_8632]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45077,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X2,sK0))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k5_xboole_0(sK0,k3_xboole_0(X2,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_22424,c_2506]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45125,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,k3_xboole_0(X2,sK0))) = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,sK0)),k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_22424,c_2500]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2741,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2331,c_541]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_13236,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X1,k3_xboole_0(X2,sK0))) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2741,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45177,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X2,sK0)) = k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_45125,c_13236]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45227,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0)))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k5_xboole_0(sK0,k3_xboole_0(X2,sK0))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_45077,c_45177]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_13226,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X2)))) = k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0)))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2741,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_13269,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(X2,k3_xboole_0(X1,sK0)))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_13226,c_2741]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1401,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X2,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_13270,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0)))) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0)))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_13269,c_1401,c_8632]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45228,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k5_xboole_0(sK0,k3_xboole_0(X2,sK0))) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0)))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_45227,c_13270]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45236,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,sK0)))) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0)))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_45069,c_45228]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_57325,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k5_xboole_0(k3_xboole_0(sK0,X1),k3_xboole_0(k3_xboole_0(sK0,X1),X2))) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0)))) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_56650,c_10208,c_45236]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_10205,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(sK0,X1)) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2559,c_0]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_57326,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),sK0)) = k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0)))) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_57325,c_10205,c_11629,c_46379]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70963,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_70962,c_35376,c_46661,c_57326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70996,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_70614,c_70963]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70613,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_64980,c_2326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_70997,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))),sK0) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_70613,c_70963]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_71002,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_70609,c_70996,c_70997]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_71149,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_70493,c_71002]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_71368,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X1,sK0)))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_70380,c_71149]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_71369,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(sK0,X1)))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_71368,c_29098,c_46661]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_76160,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),X1)) = k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_76159,c_71369]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_75661,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X1)),X2)))) = k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_70328,c_20174]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_65386,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_64821,c_2327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2695,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(sK0,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2330,c_541]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_11749,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0),k3_xboole_0(X1,k3_xboole_0(X0,sK0))) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2695,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_11777,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_11749,c_3789,c_8632]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_65757,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),sK0) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_65386,c_11777]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_75701,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X1)),X2)))) = k3_xboole_0(X2,k5_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_75661,c_782,c_65757]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_76247,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(sK0,X2))))) = k3_xboole_0(X1,k5_xboole_0(sK0,k3_xboole_0(X2,sK0))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_76160,c_75701]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_91898,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(sK2,sK0)) = sK0 ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_91897,c_11,c_2580,c_16942,c_76247]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_97444,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = sK0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_91898]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_105898,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_97444,c_90571]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6582,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_6529]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_106204,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),X0),k3_xboole_0(X0,sK0)) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_6582,c_1401]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2747,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X0,sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2331,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_56747,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2703,c_1392]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50123,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(k3_xboole_0(X1,X0),sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_541,c_2747]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_28554,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(sK0,X1))))) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_945,c_2357]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_28603,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(sK0,X1))))) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_28554,c_2326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_30100,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(sK0,X1)))),X2)) = k3_xboole_0(k3_xboole_0(X0,sK0),X2) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_28603,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1655,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X2)) = k3_xboole_0(X2,X0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_349,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_30263,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,X1),sK0) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_30100,c_1655,c_6943,c_22802]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50303,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_50123,c_1418,c_30263,c_46379]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_57213,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(X1,k3_xboole_0(X1,sK0))) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_56747,c_50303]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_95905,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),sK0))) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0)))))),k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_39551,c_1401]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1380,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1251,c_12]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6256,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_544,c_1380]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1247,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_782,c_1052]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1274,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1247,c_12]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_5995,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1274,c_1274]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6369,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_6256,c_5995]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50149,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2578,c_2747]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50249,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(X0,sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,sK0)))) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_50149,c_2578,c_2747]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50250,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_50249,c_1909]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_96056,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0)))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),sK0)))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_95905,c_11,c_6369,c_41092,c_50250]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_96057,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),sK0))))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_96056,c_6369]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_96058,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k5_xboole_0(k3_xboole_0(X2,k3_xboole_0(X1,sK0)),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),sK0)))))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_96057,c_6369]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_545,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20158,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,sK0),k5_xboole_0(k3_xboole_0(sK0,X0),X1)) = k5_xboole_0(X1,k1_xboole_0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_20072,c_545]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20170,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,sK0),k5_xboole_0(k3_xboole_0(sK0,X0),X1)) = X1 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_20158,c_11]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_26327,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),sK0),k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X2)) = X2 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_542,c_20170]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_26510,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X0,sK0)),X2)) = X2 ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_26327,c_2513]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_96059,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,k3_xboole_0(X1,sK0))))),sK0)))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_96058,c_26510]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1039,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_12,c_782]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20156,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK0,X1)),k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X1,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_20072,c_1039]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20172,plain,
% 35.45/5.02      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK0,X1)),X0) = k3_xboole_0(X1,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_20156,c_11]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_39811,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k3_xboole_0(X0,sK0))))),sK0) = k5_xboole_0(k5_xboole_0(X2,sK0),X2) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_39551,c_20172]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_39847,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k3_xboole_0(X0,sK0))))),sK0) = sK0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_39811,c_1251]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_96060,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_96059,c_39847]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_106294,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,sK0))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),X0) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_106204,c_1909,c_2747,c_22202,c_57213,c_96060]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_106616,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_105898,c_106294]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_15516,plain,
% 35.45/5.02      ( r1_tarski(k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))),sK0) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_5564]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_15624,plain,
% 35.45/5.02      ( r1_tarski(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))))),sK0) = iProver_top ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_15516,c_6369]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_27168,plain,
% 35.45/5.02      ( r1_tarski(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),sK0) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_15624]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_27189,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),sK0) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_27168,c_530]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_49874,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))),k3_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_27189,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50380,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK2,sK1),sK0),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0))),sK0)) = k1_xboole_0 ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_49874,c_533,c_1418,c_6369,c_6943]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50381,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0)))),sK0)) = k1_xboole_0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_50380,c_6369]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_21787,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))),k3_xboole_0(X1,sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X1)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_21590,c_2558]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_21796,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))),k3_xboole_0(X1,sK0)) = k3_xboole_0(X1,sK0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_21787,c_2327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_23567,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(X0,sK0)))),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0)) = k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2578,c_21796]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_23835,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,sK0))))),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_23567,c_2578,c_2747]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_23836,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK0)),sK0)),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_23835,c_2326]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_24163,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0)),sK0)),sK0)) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_23836,c_2355]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_24178,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0),sK0)),sK0)) = k3_xboole_0(sK0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_24163,c_2580]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_697,plain,
% 35.45/5.02      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_529]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_1940,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_697,c_530]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_9365,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1712,c_2506]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_9479,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_9365,c_6691]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_24179,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0),sK0)) = sK0 ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_24178,c_1712,c_1940,c_6691,c_9479]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_24180,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0)) = sK0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_24179,c_6369]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50382,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0)) = k1_xboole_0 ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_50381,c_24180]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_49875,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_27189,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50385,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))) = k1_xboole_0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_50382,c_49875]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_9897,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK0,X0),X1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_349,c_2558]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_10047,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK0,X0),X1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_9897,c_2327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_24875,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X1,X0)))),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_10047,c_10047,c_18420]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_24947,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)),k5_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X0,X1)))),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0)) = k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2357,c_24875]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_25309,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK0),k5_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X0,X1)))),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_24947,c_2326,c_2578]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_49900,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),k5_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),X0)))),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))) = k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_27189,c_25309]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2493,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(sK0,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2326,c_541]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45113,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_22424,c_2493]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_8895,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,k3_xboole_0(sK0,X1))) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2493,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45196,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK0,X0)),sK0)) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_45113,c_8895]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_12967,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_541,c_12949]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_13010,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)))) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_12949,c_5]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_13107,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)))) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_13010,c_11641]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_13145,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X0),sK0))) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_12967,c_13107]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_13146,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X0,X2)))) = k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(X2,X0),X1)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_13145,c_2513]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22298,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X0)),X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_21886,c_542]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45197,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,X0),X1)) = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_45196,c_7273,c_13146,c_22298]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_45198,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,X1))) = k3_xboole_0(X1,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_45197,c_18420]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50359,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),k3_xboole_0(X0,sK0)))),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0) ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_49900,c_5011,c_18420,c_45198]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50394,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),k3_xboole_0(X0,sK0)))),k1_xboole_0) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_50385,c_50359]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_50397,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)),sK0) = k1_xboole_0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_50394,c_1413]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_106617,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))) = k1_xboole_0 ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_106616,c_50397]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_9687,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK0,X0),X1))),sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_349,c_9670]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_9839,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK0,X0),X1))),sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_9687,c_2327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20856,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(sK0,k3_xboole_0(X1,X0)))),sK0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_9839,c_9839,c_18420]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_21610,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_1939,c_21590]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22027,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))))) = sK0 ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_21610,c_1939]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_22028,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)))))) = sK0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_22027,c_6369]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_42734,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))))),sK0),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0)))))) = sK0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_20856,c_22028]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2542,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK0,X0))),sK0) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_349,c_2327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2586,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK0,X0))),sK0) = sK0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_2542,c_2580]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_42935,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))))) = sK0 ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_42734,c_1939,c_2349,c_2580,c_2586]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_43144,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))),X0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_42935,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6926,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))),sK0) = k3_xboole_0(k3_xboole_0(sK0,X0),sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2365,c_4630]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6931,plain,
% 35.45/5.02      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))),sK0) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(light_normalisation,[status(thm)],[c_6926,c_5011]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6932,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_6931,c_1909,c_2513,c_4634]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_43135,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,sK0),k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))),k3_xboole_0(sK0,sK0))),k3_xboole_0(sK0,sK0)) = k3_xboole_0(sK0,sK0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_42935,c_25309]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20161,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(X0,sK0))) = k5_xboole_0(X1,k1_xboole_0) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_20072,c_544]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_20169,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(X1,k3_xboole_0(X0,sK0))) = X1 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_20161,c_11]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_43327,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)))) = sK0 ),
% 35.45/5.02      inference(demodulation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_43135,c_1712,c_20169,c_35376]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_43761,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_43144,c_6932,c_43327]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_91160,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,X0))))) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16892,c_90571]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_91161,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,X0))))) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK0))))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_18079,c_90571]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6485,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0),X1))) = k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(X1,k3_xboole_0(sK0,X0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2364,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4894,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,sK0),X1))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X0,sK0),X1))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_4634,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4934,plain,
% 35.45/5.02      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X0,sK0),X1))) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X0,sK0),X1)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_4894,c_4896]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4935,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X0,sK0),X1)) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_4934,c_1418,c_1712]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_6516,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,k3_xboole_0(sK0,X0))) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_6485,c_2326,c_2507,c_4935]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16916,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(sK0,sK1))) = k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16708,c_6516]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2689,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)))) = sK0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2330,c_349]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16920,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0))) = sK0 ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16708,c_2689]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16943,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_16920,c_1052,c_2349]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_16948,plain,
% 35.45/5.02      ( k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_16916,c_16943]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_91665,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,X0))))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_91161,c_16948,c_29098]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2565,plain,
% 35.45/5.02      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0),k3_xboole_0(X0,sK0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_2327,c_347]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2581,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_2580,c_2565]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_26166,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(sK0,X1) ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_20169,c_1247]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_91666,plain,
% 35.45/5.02      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,X0))))) = k3_xboole_0(sK0,X0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_91665,c_2581,c_26166]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_91667,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))))) = k3_xboole_0(sK0,X0) ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_91160,c_91666]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_91668,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k3_xboole_0(sK0,X0) ),
% 35.45/5.02      inference(light_normalisation,
% 35.45/5.02                [status(thm)],
% 35.45/5.02                [c_91667,c_16948,c_46661]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_106618,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_106617,c_43761,c_91668]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_4,plain,
% 35.45/5.02      ( r1_tarski(X0,X1)
% 35.45/5.02      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 35.45/5.02      inference(cnf_transformation,[],[f43]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_531,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 35.45/5.02      | r1_tarski(X0,X1) = iProver_top ),
% 35.45/5.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2979,plain,
% 35.45/5.02      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) != k1_xboole_0
% 35.45/5.02      | r1_tarski(X0,X1) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_0,c_531]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_68953,plain,
% 35.45/5.02      ( k5_xboole_0(sK0,sK0) != k1_xboole_0
% 35.45/5.02      | r1_tarski(sK0,sK1) = iProver_top ),
% 35.45/5.02      inference(superposition,[status(thm)],[c_16708,c_2979]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_69150,plain,
% 35.45/5.02      ( k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) = iProver_top ),
% 35.45/5.02      inference(demodulation,[status(thm)],[c_68953,c_533]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_69151,plain,
% 35.45/5.02      ( r1_tarski(sK0,sK1) = iProver_top ),
% 35.45/5.02      inference(equality_resolution_simp,[status(thm)],[c_69150]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_2,plain,
% 35.45/5.02      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 35.45/5.02      inference(cnf_transformation,[],[f26]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_13,negated_conjecture,
% 35.45/5.02      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 35.45/5.02      inference(cnf_transformation,[],[f40]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_126,plain,
% 35.45/5.02      ( ~ r1_tarski(sK0,sK1)
% 35.45/5.02      | k3_xboole_0(X0,X1) != k1_xboole_0
% 35.45/5.02      | sK2 != X1
% 35.45/5.02      | sK0 != X0 ),
% 35.45/5.02      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_127,plain,
% 35.45/5.02      ( ~ r1_tarski(sK0,sK1) | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
% 35.45/5.02      inference(unflattening,[status(thm)],[c_126]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(c_128,plain,
% 35.45/5.02      ( k3_xboole_0(sK0,sK2) != k1_xboole_0
% 35.45/5.02      | r1_tarski(sK0,sK1) != iProver_top ),
% 35.45/5.02      inference(predicate_to_equality,[status(thm)],[c_127]) ).
% 35.45/5.02  
% 35.45/5.02  cnf(contradiction,plain,
% 35.45/5.02      ( $false ),
% 35.45/5.02      inference(minisat,[status(thm)],[c_106618,c_69151,c_128]) ).
% 35.45/5.02  
% 35.45/5.02  
% 35.45/5.02  % SZS output end CNFRefutation for theBenchmark.p
% 35.45/5.02  
% 35.45/5.02  ------                               Statistics
% 35.45/5.02  
% 35.45/5.02  ------ General
% 35.45/5.02  
% 35.45/5.02  abstr_ref_over_cycles:                  0
% 35.45/5.02  abstr_ref_under_cycles:                 0
% 35.45/5.02  gc_basic_clause_elim:                   0
% 35.45/5.02  forced_gc_time:                         0
% 35.45/5.02  parsing_time:                           0.005
% 35.45/5.02  unif_index_cands_time:                  0.
% 35.45/5.02  unif_index_add_time:                    0.
% 35.45/5.02  orderings_time:                         0.
% 35.45/5.02  out_proof_time:                         0.025
% 35.45/5.02  total_time:                             4.099
% 35.45/5.02  num_of_symbols:                         39
% 35.45/5.02  num_of_terms:                           230087
% 35.45/5.02  
% 35.45/5.02  ------ Preprocessing
% 35.45/5.02  
% 35.45/5.02  num_of_splits:                          0
% 35.45/5.02  num_of_split_atoms:                     0
% 35.45/5.02  num_of_reused_defs:                     0
% 35.45/5.02  num_eq_ax_congr_red:                    0
% 35.45/5.02  num_of_sem_filtered_clauses:            1
% 35.45/5.02  num_of_subtypes:                        0
% 35.45/5.02  monotx_restored_types:                  0
% 35.45/5.02  sat_num_of_epr_types:                   0
% 35.45/5.02  sat_num_of_non_cyclic_types:            0
% 35.45/5.02  sat_guarded_non_collapsed_types:        0
% 35.45/5.02  num_pure_diseq_elim:                    0
% 35.45/5.02  simp_replaced_by:                       0
% 35.45/5.02  res_preprocessed:                       68
% 35.45/5.02  prep_upred:                             0
% 35.45/5.02  prep_unflattend:                        24
% 35.45/5.02  smt_new_axioms:                         0
% 35.45/5.02  pred_elim_cands:                        1
% 35.45/5.02  pred_elim:                              1
% 35.45/5.02  pred_elim_cl:                           1
% 35.45/5.02  pred_elim_cycles:                       3
% 35.45/5.02  merged_defs:                            8
% 35.45/5.02  merged_defs_ncl:                        0
% 35.45/5.02  bin_hyper_res:                          8
% 35.45/5.02  prep_cycles:                            4
% 35.45/5.02  pred_elim_time:                         0.001
% 35.45/5.02  splitting_time:                         0.
% 35.45/5.02  sem_filter_time:                        0.
% 35.45/5.02  monotx_time:                            0.
% 35.45/5.02  subtype_inf_time:                       0.
% 35.45/5.02  
% 35.45/5.02  ------ Problem properties
% 35.45/5.02  
% 35.45/5.02  clauses:                                14
% 35.45/5.02  conjectures:                            1
% 35.45/5.02  epr:                                    0
% 35.45/5.02  horn:                                   14
% 35.45/5.02  ground:                                 2
% 35.45/5.02  unary:                                  10
% 35.45/5.02  binary:                                 4
% 35.45/5.02  lits:                                   18
% 35.45/5.02  lits_eq:                                12
% 35.45/5.02  fd_pure:                                0
% 35.45/5.02  fd_pseudo:                              0
% 35.45/5.02  fd_cond:                                0
% 35.45/5.02  fd_pseudo_cond:                         0
% 35.45/5.02  ac_symbols:                             2
% 35.45/5.02  
% 35.45/5.02  ------ Propositional Solver
% 35.45/5.02  
% 35.45/5.02  prop_solver_calls:                      36
% 35.45/5.02  prop_fast_solver_calls:                 578
% 35.45/5.02  smt_solver_calls:                       0
% 35.45/5.02  smt_fast_solver_calls:                  0
% 35.45/5.02  prop_num_of_clauses:                    31180
% 35.45/5.02  prop_preprocess_simplified:             20731
% 35.45/5.02  prop_fo_subsumed:                       0
% 35.45/5.02  prop_solver_time:                       0.
% 35.45/5.02  smt_solver_time:                        0.
% 35.45/5.02  smt_fast_solver_time:                   0.
% 35.45/5.02  prop_fast_solver_time:                  0.
% 35.45/5.02  prop_unsat_core_time:                   0.003
% 35.45/5.02  
% 35.45/5.02  ------ QBF
% 35.45/5.02  
% 35.45/5.02  qbf_q_res:                              0
% 35.45/5.02  qbf_num_tautologies:                    0
% 35.45/5.02  qbf_prep_cycles:                        0
% 35.45/5.02  
% 35.45/5.02  ------ BMC1
% 35.45/5.02  
% 35.45/5.02  bmc1_current_bound:                     -1
% 35.45/5.02  bmc1_last_solved_bound:                 -1
% 35.45/5.02  bmc1_unsat_core_size:                   -1
% 35.45/5.02  bmc1_unsat_core_parents_size:           -1
% 35.45/5.02  bmc1_merge_next_fun:                    0
% 35.45/5.02  bmc1_unsat_core_clauses_time:           0.
% 35.45/5.02  
% 35.45/5.02  ------ Instantiation
% 35.45/5.02  
% 35.45/5.02  inst_num_of_clauses:                    3892
% 35.45/5.02  inst_num_in_passive:                    1066
% 35.45/5.02  inst_num_in_active:                     1303
% 35.45/5.02  inst_num_in_unprocessed:                1523
% 35.45/5.02  inst_num_of_loops:                      1360
% 35.45/5.02  inst_num_of_learning_restarts:          0
% 35.45/5.02  inst_num_moves_active_passive:          50
% 35.45/5.02  inst_lit_activity:                      0
% 35.45/5.02  inst_lit_activity_moves:                0
% 35.45/5.02  inst_num_tautologies:                   0
% 35.45/5.02  inst_num_prop_implied:                  0
% 35.45/5.02  inst_num_existing_simplified:           0
% 35.45/5.02  inst_num_eq_res_simplified:             0
% 35.45/5.02  inst_num_child_elim:                    0
% 35.45/5.02  inst_num_of_dismatching_blockings:      1672
% 35.45/5.02  inst_num_of_non_proper_insts:           3847
% 35.45/5.02  inst_num_of_duplicates:                 0
% 35.45/5.02  inst_inst_num_from_inst_to_res:         0
% 35.45/5.02  inst_dismatching_checking_time:         0.
% 35.45/5.02  
% 35.45/5.02  ------ Resolution
% 35.45/5.02  
% 35.45/5.02  res_num_of_clauses:                     0
% 35.45/5.02  res_num_in_passive:                     0
% 35.45/5.02  res_num_in_active:                      0
% 35.45/5.02  res_num_of_loops:                       72
% 35.45/5.02  res_forward_subset_subsumed:            1122
% 35.45/5.02  res_backward_subset_subsumed:           2
% 35.45/5.02  res_forward_subsumed:                   0
% 35.45/5.02  res_backward_subsumed:                  0
% 35.45/5.02  res_forward_subsumption_resolution:     0
% 35.45/5.02  res_backward_subsumption_resolution:    0
% 35.45/5.02  res_clause_to_clause_subsumption:       181532
% 35.45/5.02  res_orphan_elimination:                 0
% 35.45/5.02  res_tautology_del:                      317
% 35.45/5.02  res_num_eq_res_simplified:              0
% 35.45/5.02  res_num_sel_changes:                    0
% 35.45/5.02  res_moves_from_active_to_pass:          0
% 35.45/5.02  
% 35.45/5.02  ------ Superposition
% 35.45/5.02  
% 35.45/5.02  sup_time_total:                         0.
% 35.45/5.02  sup_time_generating:                    0.
% 35.45/5.02  sup_time_sim_full:                      0.
% 35.45/5.02  sup_time_sim_immed:                     0.
% 35.45/5.02  
% 35.45/5.02  sup_num_of_clauses:                     10307
% 35.45/5.02  sup_num_in_active:                      245
% 35.45/5.02  sup_num_in_passive:                     10062
% 35.45/5.02  sup_num_of_loops:                       271
% 35.45/5.02  sup_fw_superposition:                   21819
% 35.45/5.02  sup_bw_superposition:                   16513
% 35.45/5.02  sup_immediate_simplified:               27946
% 35.45/5.02  sup_given_eliminated:                   14
% 35.45/5.02  comparisons_done:                       0
% 35.45/5.02  comparisons_avoided:                    0
% 35.45/5.02  
% 35.45/5.02  ------ Simplifications
% 35.45/5.02  
% 35.45/5.02  
% 35.45/5.02  sim_fw_subset_subsumed:                 12
% 35.45/5.02  sim_bw_subset_subsumed:                 0
% 35.45/5.02  sim_fw_subsumed:                        2291
% 35.45/5.02  sim_bw_subsumed:                        115
% 35.45/5.02  sim_fw_subsumption_res:                 0
% 35.45/5.02  sim_bw_subsumption_res:                 0
% 35.45/5.02  sim_tautology_del:                      0
% 35.45/5.02  sim_eq_tautology_del:                   5136
% 35.45/5.02  sim_eq_res_simp:                        131
% 35.45/5.02  sim_fw_demodulated:                     26588
% 35.45/5.02  sim_bw_demodulated:                     681
% 35.45/5.02  sim_light_normalised:                   10706
% 35.45/5.02  sim_joinable_taut:                      1135
% 35.45/5.02  sim_joinable_simp:                      0
% 35.45/5.02  sim_ac_normalised:                      0
% 35.45/5.02  sim_smt_subsumption:                    0
% 35.45/5.02  
%------------------------------------------------------------------------------
