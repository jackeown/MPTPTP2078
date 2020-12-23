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
% DateTime   : Thu Dec  3 11:25:45 EST 2020

% Result     : Theorem 55.77s
% Output     : CNFRefutation 55.77s
% Verified   : 
% Statistics : Number of formulae       :  119 (3134 expanded)
%              Number of clauses        :   82 (1203 expanded)
%              Number of leaves         :   14 ( 829 expanded)
%              Depth                    :   35
%              Number of atoms          :  145 (4001 expanded)
%              Number of equality atoms :  104 (2746 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f27,f23,f23])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f32,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f32,f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f29,f23])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_764,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_3])).

cnf(c_4347,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_764])).

cnf(c_6,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_197,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_6,c_9,c_1,c_3,c_0])).

cnf(c_7177,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_4347,c_197])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7211,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7177,c_10])).

cnf(c_9886,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_7211])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_196,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
    inference(theory_normalisation,[status(thm)],[c_12,c_9,c_1,c_3,c_0])).

cnf(c_287,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_289,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4336,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_287,c_289])).

cnf(c_322,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_6698,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_4336,c_322])).

cnf(c_7722,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_0,c_6698])).

cnf(c_9394,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_7722,c_197])).

cnf(c_9431,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_9394,c_4336])).

cnf(c_11292,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),sK0)) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_7211,c_9431])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11406,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_11292,c_7,c_4336])).

cnf(c_9902,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6698,c_7211])).

cnf(c_17587,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11406,c_9902])).

cnf(c_6694,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_322])).

cnf(c_323,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_9684,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_4336,c_323])).

cnf(c_10904,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,sK0)) = k3_xboole_0(k3_xboole_0(X0,sK0),sK0) ),
    inference(superposition,[status(thm)],[c_6694,c_9684])).

cnf(c_7155,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_764,c_4347])).

cnf(c_7261,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_7155,c_2])).

cnf(c_10273,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_7261])).

cnf(c_17905,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_10904,c_10273])).

cnf(c_50028,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_17587,c_17905])).

cnf(c_2114,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_2,c_197])).

cnf(c_2134,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2114,c_2,c_10])).

cnf(c_50085,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_50028,c_2134,c_6698])).

cnf(c_53358,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_50085])).

cnf(c_53521,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))),sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_53358,c_197,c_6698])).

cnf(c_53712,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK2,k1_xboole_0)),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9886,c_53521])).

cnf(c_53897,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_53712,c_7])).

cnf(c_54431,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_53897,c_9902])).

cnf(c_10902,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) = k3_xboole_0(k3_xboole_0(sK0,X0),sK0) ),
    inference(superposition,[status(thm)],[c_764,c_9684])).

cnf(c_11020,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),sK0) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_10902,c_9684])).

cnf(c_11872,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k3_xboole_0(k3_xboole_0(X0,sK0),sK0) ),
    inference(superposition,[status(thm)],[c_6698,c_11020])).

cnf(c_20072,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_11872,c_10273])).

cnf(c_54501,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_54431,c_7,c_20072])).

cnf(c_54632,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_54501,c_197])).

cnf(c_54756,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_54632,c_7])).

cnf(c_110567,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK2,X0))) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_54756])).

cnf(c_7735,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) ),
    inference(superposition,[status(thm)],[c_6698,c_6694])).

cnf(c_7736,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) ),
    inference(superposition,[status(thm)],[c_6698,c_4347])).

cnf(c_7785,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_7735,c_6698,c_7736])).

cnf(c_223121,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK0)) = k3_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_110567,c_7785])).

cnf(c_223189,plain,
    ( k3_xboole_0(sK1,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_223121,c_2,c_11020])).

cnf(c_223050,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_110567,c_4336])).

cnf(c_2112,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X2,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_197])).

cnf(c_223595,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_223050,c_2112])).

cnf(c_234885,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,k5_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_223595,c_223189])).

cnf(c_234906,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK1),sK0) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_223189,c_234885])).

cnf(c_235236,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) = k5_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_234906,c_2])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_288,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_235871,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_235236,c_288])).

cnf(c_905,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_9])).

cnf(c_757,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_4767,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_905,c_757])).

cnf(c_235962,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_235871,c_4767])).

cnf(c_13565,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_9886,c_11406])).

cnf(c_13586,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK2,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_13565,c_7])).

cnf(c_8,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_11,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_76,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_77,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_76])).

cnf(c_286,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_659,plain,
    ( k5_xboole_0(X0,k3_xboole_0(sK2,X0)) != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_286])).

cnf(c_662,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK2,sK0)) != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_235962,c_13586,c_662])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:57:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.77/7.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.77/7.49  
% 55.77/7.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.77/7.49  
% 55.77/7.49  ------  iProver source info
% 55.77/7.49  
% 55.77/7.49  git: date: 2020-06-30 10:37:57 +0100
% 55.77/7.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.77/7.49  git: non_committed_changes: false
% 55.77/7.49  git: last_make_outside_of_git: false
% 55.77/7.49  
% 55.77/7.49  ------ 
% 55.77/7.49  ------ Parsing...
% 55.77/7.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.77/7.49  
% 55.77/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 55.77/7.49  
% 55.77/7.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.77/7.49  
% 55.77/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.77/7.49  ------ Proving...
% 55.77/7.49  ------ Problem Properties 
% 55.77/7.49  
% 55.77/7.49  
% 55.77/7.49  clauses                                 12
% 55.77/7.49  conjectures                             1
% 55.77/7.49  EPR                                     0
% 55.77/7.49  Horn                                    12
% 55.77/7.49  unary                                   10
% 55.77/7.49  binary                                  2
% 55.77/7.49  lits                                    14
% 55.77/7.49  lits eq                                 10
% 55.77/7.49  fd_pure                                 0
% 55.77/7.49  fd_pseudo                               0
% 55.77/7.49  fd_cond                                 0
% 55.77/7.49  fd_pseudo_cond                          0
% 55.77/7.49  AC symbols                              2
% 55.77/7.49  
% 55.77/7.49  ------ Input Options Time Limit: Unbounded
% 55.77/7.49  
% 55.77/7.49  
% 55.77/7.49  ------ 
% 55.77/7.49  Current options:
% 55.77/7.49  ------ 
% 55.77/7.49  
% 55.77/7.49  
% 55.77/7.49  
% 55.77/7.49  
% 55.77/7.49  ------ Proving...
% 55.77/7.49  
% 55.77/7.49  
% 55.77/7.49  % SZS status Theorem for theBenchmark.p
% 55.77/7.49  
% 55.77/7.49  % SZS output start CNFRefutation for theBenchmark.p
% 55.77/7.49  
% 55.77/7.49  fof(f1,axiom,(
% 55.77/7.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f20,plain,(
% 55.77/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 55.77/7.49    inference(cnf_transformation,[],[f1])).
% 55.77/7.49  
% 55.77/7.49  fof(f3,axiom,(
% 55.77/7.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f15,plain,(
% 55.77/7.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 55.77/7.49    inference(rectify,[],[f3])).
% 55.77/7.49  
% 55.77/7.49  fof(f22,plain,(
% 55.77/7.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 55.77/7.49    inference(cnf_transformation,[],[f15])).
% 55.77/7.49  
% 55.77/7.49  fof(f5,axiom,(
% 55.77/7.49    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f24,plain,(
% 55.77/7.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 55.77/7.49    inference(cnf_transformation,[],[f5])).
% 55.77/7.49  
% 55.77/7.49  fof(f8,axiom,(
% 55.77/7.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f27,plain,(
% 55.77/7.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 55.77/7.49    inference(cnf_transformation,[],[f8])).
% 55.77/7.49  
% 55.77/7.49  fof(f4,axiom,(
% 55.77/7.49    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f23,plain,(
% 55.77/7.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 55.77/7.49    inference(cnf_transformation,[],[f4])).
% 55.77/7.49  
% 55.77/7.49  fof(f35,plain,(
% 55.77/7.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 55.77/7.49    inference(definition_unfolding,[],[f27,f23,f23])).
% 55.77/7.49  
% 55.77/7.49  fof(f11,axiom,(
% 55.77/7.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f30,plain,(
% 55.77/7.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 55.77/7.49    inference(cnf_transformation,[],[f11])).
% 55.77/7.49  
% 55.77/7.49  fof(f2,axiom,(
% 55.77/7.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f21,plain,(
% 55.77/7.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 55.77/7.49    inference(cnf_transformation,[],[f2])).
% 55.77/7.49  
% 55.77/7.49  fof(f12,axiom,(
% 55.77/7.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f31,plain,(
% 55.77/7.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 55.77/7.49    inference(cnf_transformation,[],[f12])).
% 55.77/7.49  
% 55.77/7.49  fof(f13,conjecture,(
% 55.77/7.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f14,negated_conjecture,(
% 55.77/7.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 55.77/7.49    inference(negated_conjecture,[],[f13])).
% 55.77/7.49  
% 55.77/7.49  fof(f17,plain,(
% 55.77/7.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 55.77/7.49    inference(ennf_transformation,[],[f14])).
% 55.77/7.49  
% 55.77/7.49  fof(f18,plain,(
% 55.77/7.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 55.77/7.49    introduced(choice_axiom,[])).
% 55.77/7.49  
% 55.77/7.49  fof(f19,plain,(
% 55.77/7.49    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 55.77/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 55.77/7.49  
% 55.77/7.49  fof(f32,plain,(
% 55.77/7.49    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 55.77/7.49    inference(cnf_transformation,[],[f19])).
% 55.77/7.49  
% 55.77/7.49  fof(f37,plain,(
% 55.77/7.49    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 55.77/7.49    inference(definition_unfolding,[],[f32,f23])).
% 55.77/7.49  
% 55.77/7.49  fof(f6,axiom,(
% 55.77/7.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f16,plain,(
% 55.77/7.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 55.77/7.49    inference(ennf_transformation,[],[f6])).
% 55.77/7.49  
% 55.77/7.49  fof(f25,plain,(
% 55.77/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 55.77/7.49    inference(cnf_transformation,[],[f16])).
% 55.77/7.49  
% 55.77/7.49  fof(f9,axiom,(
% 55.77/7.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f28,plain,(
% 55.77/7.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.77/7.49    inference(cnf_transformation,[],[f9])).
% 55.77/7.49  
% 55.77/7.49  fof(f7,axiom,(
% 55.77/7.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f26,plain,(
% 55.77/7.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 55.77/7.49    inference(cnf_transformation,[],[f7])).
% 55.77/7.49  
% 55.77/7.49  fof(f34,plain,(
% 55.77/7.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 55.77/7.49    inference(definition_unfolding,[],[f26,f23])).
% 55.77/7.49  
% 55.77/7.49  fof(f10,axiom,(
% 55.77/7.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 55.77/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.77/7.49  
% 55.77/7.49  fof(f29,plain,(
% 55.77/7.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 55.77/7.49    inference(cnf_transformation,[],[f10])).
% 55.77/7.49  
% 55.77/7.49  fof(f36,plain,(
% 55.77/7.49    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 55.77/7.49    inference(definition_unfolding,[],[f29,f23])).
% 55.77/7.49  
% 55.77/7.49  fof(f33,plain,(
% 55.77/7.49    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 55.77/7.49    inference(cnf_transformation,[],[f19])).
% 55.77/7.49  
% 55.77/7.49  cnf(c_0,plain,
% 55.77/7.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 55.77/7.49      inference(cnf_transformation,[],[f20]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_2,plain,
% 55.77/7.49      ( k3_xboole_0(X0,X0) = X0 ),
% 55.77/7.49      inference(cnf_transformation,[],[f22]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_3,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 55.77/7.49      inference(cnf_transformation,[],[f24]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_764,plain,
% 55.77/7.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_2,c_3]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_4347,plain,
% 55.77/7.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_0,c_764]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_6,plain,
% 55.77/7.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 55.77/7.49      inference(cnf_transformation,[],[f35]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_9,plain,
% 55.77/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 55.77/7.49      inference(cnf_transformation,[],[f30]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_1,plain,
% 55.77/7.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 55.77/7.49      inference(cnf_transformation,[],[f21]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_197,plain,
% 55.77/7.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 55.77/7.49      inference(theory_normalisation,[status(thm)],[c_6,c_9,c_1,c_3,c_0]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_7177,plain,
% 55.77/7.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_4347,c_197]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_10,plain,
% 55.77/7.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.77/7.49      inference(cnf_transformation,[],[f31]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_7211,plain,
% 55.77/7.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_7177,c_10]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_9886,plain,
% 55.77/7.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_0,c_7211]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_12,negated_conjecture,
% 55.77/7.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 55.77/7.49      inference(cnf_transformation,[],[f37]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_196,negated_conjecture,
% 55.77/7.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) ),
% 55.77/7.49      inference(theory_normalisation,
% 55.77/7.49                [status(thm)],
% 55.77/7.49                [c_12,c_9,c_1,c_3,c_0]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_287,plain,
% 55.77/7.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
% 55.77/7.49      inference(predicate_to_equality,[status(thm)],[c_196]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_4,plain,
% 55.77/7.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 55.77/7.49      inference(cnf_transformation,[],[f25]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_289,plain,
% 55.77/7.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 55.77/7.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_4336,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_287,c_289]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_322,plain,
% 55.77/7.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_6698,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(X0,sK0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_4336,c_322]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_7722,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0)) = k3_xboole_0(X0,sK0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_0,c_6698]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_9394,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_7722,c_197]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_9431,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
% 55.77/7.49      inference(light_normalisation,[status(thm)],[c_9394,c_4336]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_11292,plain,
% 55.77/7.49      ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),sK0)) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k1_xboole_0)) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_7211,c_9431]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_7,plain,
% 55.77/7.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.77/7.49      inference(cnf_transformation,[],[f28]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_11406,plain,
% 55.77/7.49      ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),sK0)) = sK0 ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_11292,c_7,c_4336]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_9902,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) = k1_xboole_0 ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_6698,c_7211]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_17587,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k1_xboole_0 ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_11406,c_9902]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_6694,plain,
% 55.77/7.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_2,c_322]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_323,plain,
% 55.77/7.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_9684,plain,
% 55.77/7.49      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_4336,c_323]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_10904,plain,
% 55.77/7.49      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,sK0)) = k3_xboole_0(k3_xboole_0(X0,sK0),sK0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_6694,c_9684]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_7155,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_764,c_4347]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_7261,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_7155,c_2]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_10273,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_0,c_7261]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_17905,plain,
% 55.77/7.49      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,X0) ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_10904,c_10273]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_50028,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k1_xboole_0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_17587,c_17905]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_2114,plain,
% 55.77/7.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_2,c_197]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_2134,plain,
% 55.77/7.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_2114,c_2,c_10]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_50085,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_50028,c_2134,c_6698]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_53358,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_3,c_50085]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_53521,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))),sK0) = k1_xboole_0 ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_53358,c_197,c_6698]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_53712,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK2,k1_xboole_0)),sK0) = k1_xboole_0 ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_9886,c_53521]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_53897,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,sK2),sK0) = k1_xboole_0 ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_53712,c_7]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_54431,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k5_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_53897,c_9902]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_10902,plain,
% 55.77/7.49      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK0,X0)) = k3_xboole_0(k3_xboole_0(sK0,X0),sK0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_764,c_9684]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_11020,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(sK0,X0),sK0) = k3_xboole_0(X0,sK0) ),
% 55.77/7.49      inference(light_normalisation,[status(thm)],[c_10902,c_9684]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_11872,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k3_xboole_0(k3_xboole_0(X0,sK0),sK0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_6698,c_11020]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_20072,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) = k3_xboole_0(sK0,X0) ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_11872,c_10273]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_54501,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k3_xboole_0(X0,sK2)) = k1_xboole_0 ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_54431,c_7,c_20072]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_54632,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_54501,c_197]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_54756,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k3_xboole_0(sK0,X0) ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_54632,c_7]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_110567,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK2,X0))) = k3_xboole_0(sK0,X0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_0,c_54756]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_7735,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_6698,c_6694]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_7736,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),sK0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_6698,c_4347]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_7785,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,sK0) ),
% 55.77/7.49      inference(light_normalisation,[status(thm)],[c_7735,c_6698,c_7736]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_223121,plain,
% 55.77/7.49      ( k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK0)) = k3_xboole_0(sK0,sK0) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_110567,c_7785]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_223189,plain,
% 55.77/7.49      ( k3_xboole_0(sK1,sK0) = sK0 ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_223121,c_2,c_11020]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_223050,plain,
% 55.77/7.49      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_110567,c_4336]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_2112,plain,
% 55.77/7.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X2,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_0,c_197]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_223595,plain,
% 55.77/7.49      ( k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_223050,c_2112]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_234885,plain,
% 55.77/7.49      ( k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,k5_xboole_0(sK1,sK0)) ),
% 55.77/7.49      inference(light_normalisation,[status(thm)],[c_223595,c_223189]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_234906,plain,
% 55.77/7.49      ( k5_xboole_0(k3_xboole_0(sK1,sK1),sK0) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_223189,c_234885]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_235236,plain,
% 55.77/7.49      ( k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) = k5_xboole_0(sK1,sK0) ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_234906,c_2]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_5,plain,
% 55.77/7.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 55.77/7.49      inference(cnf_transformation,[],[f34]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_288,plain,
% 55.77/7.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 55.77/7.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_235871,plain,
% 55.77/7.49      ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK0)),sK1) = iProver_top ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_235236,c_288]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_905,plain,
% 55.77/7.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_10,c_9]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_757,plain,
% 55.77/7.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_4767,plain,
% 55.77/7.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_905,c_757]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_235962,plain,
% 55.77/7.49      ( r1_tarski(sK0,sK1) = iProver_top ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_235871,c_4767]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_13565,plain,
% 55.77/7.49      ( k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK0)) = sK0 ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_9886,c_11406]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_13586,plain,
% 55.77/7.49      ( k5_xboole_0(sK0,k3_xboole_0(sK2,sK0)) = sK0 ),
% 55.77/7.49      inference(demodulation,[status(thm)],[c_13565,c_7]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_8,plain,
% 55.77/7.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 55.77/7.49      inference(cnf_transformation,[],[f36]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_11,negated_conjecture,
% 55.77/7.49      ( ~ r1_xboole_0(sK0,sK2) | ~ r1_tarski(sK0,sK1) ),
% 55.77/7.49      inference(cnf_transformation,[],[f33]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_76,plain,
% 55.77/7.49      ( ~ r1_tarski(sK0,sK1)
% 55.77/7.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK0
% 55.77/7.49      | sK2 != X1 ),
% 55.77/7.49      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_77,plain,
% 55.77/7.49      ( ~ r1_tarski(sK0,sK1)
% 55.77/7.49      | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0 ),
% 55.77/7.49      inference(unflattening,[status(thm)],[c_76]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_286,plain,
% 55.77/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0
% 55.77/7.49      | r1_tarski(sK0,sK1) != iProver_top ),
% 55.77/7.49      inference(predicate_to_equality,[status(thm)],[c_77]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_659,plain,
% 55.77/7.49      ( k5_xboole_0(X0,k3_xboole_0(sK2,X0)) != sK0
% 55.77/7.49      | r1_tarski(sK0,sK1) != iProver_top ),
% 55.77/7.49      inference(superposition,[status(thm)],[c_0,c_286]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(c_662,plain,
% 55.77/7.49      ( k5_xboole_0(sK0,k3_xboole_0(sK2,sK0)) != sK0
% 55.77/7.49      | r1_tarski(sK0,sK1) != iProver_top ),
% 55.77/7.49      inference(instantiation,[status(thm)],[c_659]) ).
% 55.77/7.49  
% 55.77/7.49  cnf(contradiction,plain,
% 55.77/7.49      ( $false ),
% 55.77/7.49      inference(minisat,[status(thm)],[c_235962,c_13586,c_662]) ).
% 55.77/7.49  
% 55.77/7.49  
% 55.77/7.49  % SZS output end CNFRefutation for theBenchmark.p
% 55.77/7.49  
% 55.77/7.49  ------                               Statistics
% 55.77/7.49  
% 55.77/7.49  ------ Selected
% 55.77/7.49  
% 55.77/7.49  total_time:                             6.741
% 55.77/7.49  
%------------------------------------------------------------------------------
