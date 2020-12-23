%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:36 EST 2020

% Result     : Theorem 31.30s
% Output     : CNFRefutation 31.30s
% Verified   : 
% Statistics : Number of formulae       :  133 (1962 expanded)
%              Number of clauses        :  104 ( 706 expanded)
%              Number of leaves         :   13 ( 514 expanded)
%              Depth                    :   35
%              Number of atoms          :  190 (2625 expanded)
%              Number of equality atoms :  140 (1818 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   12 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f26,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f23,f22,f22])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_281,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_286,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1458,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_281,c_286])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1677,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1458,c_4])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1690,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_1677,c_3])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_284,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_639,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_284])).

cnf(c_758,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))))),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_639])).

cnf(c_11367,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1690,c_758])).

cnf(c_12324,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))),k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11367,c_286])).

cnf(c_12326,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,sK0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,sK0)),k4_xboole_0(sK1,sK2))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12324,c_5])).

cnf(c_12327,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,sK0)),k4_xboole_0(sK1,sK2))))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12326,c_5])).

cnf(c_12328,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12327,c_5])).

cnf(c_12329,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0))))))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12328,c_1690])).

cnf(c_12704,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))))))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12329,c_4])).

cnf(c_12825,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))))))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12704,c_3])).

cnf(c_409,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_284])).

cnf(c_1459,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_409,c_286])).

cnf(c_1472,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1459,c_3])).

cnf(c_643,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_648,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_643,c_5])).

cnf(c_649,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_648,c_5])).

cnf(c_5859,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0))))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1472,c_649])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_285,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_775,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_284,c_285])).

cnf(c_1463,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_775,c_286])).

cnf(c_6075,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5859,c_3,c_1463,c_1472])).

cnf(c_1788,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1690,c_639])).

cnf(c_2074,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1788,c_286])).

cnf(c_2076,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2074,c_5])).

cnf(c_2077,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2076,c_1690])).

cnf(c_2543,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),X1))) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_2077,c_5])).

cnf(c_776,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_281,c_285])).

cnf(c_1461,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_776,c_286])).

cnf(c_1769,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1461,c_5])).

cnf(c_1922,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_1472,c_1769])).

cnf(c_1969,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1922,c_3,c_1472])).

cnf(c_2262,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_1969,c_5])).

cnf(c_777,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_285])).

cnf(c_1464,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_777,c_286])).

cnf(c_2273,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2262,c_3,c_1464])).

cnf(c_2692,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2543,c_2273])).

cnf(c_4346,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),X1)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2692,c_4])).

cnf(c_4386,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4346,c_3])).

cnf(c_6489,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),X1)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_6075,c_4386])).

cnf(c_6665,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1)))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_6489,c_5])).

cnf(c_14789,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0)),X2) ),
    inference(superposition,[status(thm)],[c_6665,c_5])).

cnf(c_6475,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6075,c_5])).

cnf(c_14851,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14789,c_5,c_1472,c_2273,c_6475])).

cnf(c_15582,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_14851,c_12825])).

cnf(c_15833,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sK0,X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_15582,c_3])).

cnf(c_19700,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))))))) = k4_xboole_0(X0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_12825,c_15833])).

cnf(c_19881,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_19700,c_12825])).

cnf(c_640,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),X3) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_652,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))) ),
    inference(demodulation,[status(thm)],[c_640,c_5])).

cnf(c_7555,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)),X0))) ),
    inference(superposition,[status(thm)],[c_1690,c_652])).

cnf(c_7999,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ),
    inference(demodulation,[status(thm)],[c_7555,c_3,c_1472])).

cnf(c_8483,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0)))) ),
    inference(superposition,[status(thm)],[c_7999,c_4])).

cnf(c_8535,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_8483,c_4])).

cnf(c_25215,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_19881,c_8535])).

cnf(c_25326,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_25215,c_1690])).

cnf(c_25327,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_25326,c_3,c_1472])).

cnf(c_780,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_285])).

cnf(c_25619,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_25327,c_780])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_283,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1457,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_283,c_286])).

cnf(c_129388,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25619,c_1457])).

cnf(c_129772,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_129388,c_5,c_6475])).

cnf(c_1047,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X0)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_780])).

cnf(c_15106,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14851,c_1047])).

cnf(c_15129,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(sK0,X0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15106,c_3])).

cnf(c_130322,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_129772,c_15129])).

cnf(c_130323,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),k4_xboole_0(sK0,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_130322,c_3])).

cnf(c_130475,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0),k4_xboole_0(sK0,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_130323])).

cnf(c_107,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_306,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_38715,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0),X0)
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,sK2) != X0
    | sK1 != k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_77544,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0),k4_xboole_0(sK0,sK2))
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)
    | sK1 != k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_38715])).

cnf(c_77545,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)
    | sK1 != k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0),k4_xboole_0(sK0,sK2)) != iProver_top
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77544])).

cnf(c_14589,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_106,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_342,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_2857,plain,
    ( X0 != k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)
    | sK1 = X0
    | sK1 != k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_5475,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)
    | sK1 = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | sK1 != k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2857])).

cnf(c_105,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3784,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_1997,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_933,plain,
    ( X0 != k4_xboole_0(sK1,k1_xboole_0)
    | sK1 = X0
    | sK1 != k4_xboole_0(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_1125,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) != k4_xboole_0(sK1,k1_xboole_0)
    | sK1 = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)
    | sK1 != k4_xboole_0(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_571,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_389,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_469,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != sK1
    | sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_375,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_8,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_130475,c_77545,c_14589,c_5475,c_3784,c_1997,c_1125,c_571,c_469,c_375,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:30:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.30/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.30/4.49  
% 31.30/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.30/4.49  
% 31.30/4.49  ------  iProver source info
% 31.30/4.49  
% 31.30/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.30/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.30/4.49  git: non_committed_changes: false
% 31.30/4.49  git: last_make_outside_of_git: false
% 31.30/4.49  
% 31.30/4.49  ------ 
% 31.30/4.49  
% 31.30/4.49  ------ Input Options
% 31.30/4.49  
% 31.30/4.49  --out_options                           all
% 31.30/4.49  --tptp_safe_out                         true
% 31.30/4.49  --problem_path                          ""
% 31.30/4.49  --include_path                          ""
% 31.30/4.49  --clausifier                            res/vclausify_rel
% 31.30/4.49  --clausifier_options                    ""
% 31.30/4.49  --stdin                                 false
% 31.30/4.49  --stats_out                             all
% 31.30/4.49  
% 31.30/4.49  ------ General Options
% 31.30/4.49  
% 31.30/4.49  --fof                                   false
% 31.30/4.49  --time_out_real                         305.
% 31.30/4.49  --time_out_virtual                      -1.
% 31.30/4.49  --symbol_type_check                     false
% 31.30/4.49  --clausify_out                          false
% 31.30/4.49  --sig_cnt_out                           false
% 31.30/4.49  --trig_cnt_out                          false
% 31.30/4.49  --trig_cnt_out_tolerance                1.
% 31.30/4.49  --trig_cnt_out_sk_spl                   false
% 31.30/4.49  --abstr_cl_out                          false
% 31.30/4.49  
% 31.30/4.49  ------ Global Options
% 31.30/4.49  
% 31.30/4.49  --schedule                              default
% 31.30/4.49  --add_important_lit                     false
% 31.30/4.49  --prop_solver_per_cl                    1000
% 31.30/4.49  --min_unsat_core                        false
% 31.30/4.49  --soft_assumptions                      false
% 31.30/4.49  --soft_lemma_size                       3
% 31.30/4.49  --prop_impl_unit_size                   0
% 31.30/4.49  --prop_impl_unit                        []
% 31.30/4.49  --share_sel_clauses                     true
% 31.30/4.49  --reset_solvers                         false
% 31.30/4.49  --bc_imp_inh                            [conj_cone]
% 31.30/4.49  --conj_cone_tolerance                   3.
% 31.30/4.49  --extra_neg_conj                        none
% 31.30/4.49  --large_theory_mode                     true
% 31.30/4.49  --prolific_symb_bound                   200
% 31.30/4.49  --lt_threshold                          2000
% 31.30/4.49  --clause_weak_htbl                      true
% 31.30/4.49  --gc_record_bc_elim                     false
% 31.30/4.49  
% 31.30/4.49  ------ Preprocessing Options
% 31.30/4.49  
% 31.30/4.49  --preprocessing_flag                    true
% 31.30/4.49  --time_out_prep_mult                    0.1
% 31.30/4.49  --splitting_mode                        input
% 31.30/4.49  --splitting_grd                         true
% 31.30/4.49  --splitting_cvd                         false
% 31.30/4.49  --splitting_cvd_svl                     false
% 31.30/4.49  --splitting_nvd                         32
% 31.30/4.49  --sub_typing                            true
% 31.30/4.49  --prep_gs_sim                           true
% 31.30/4.49  --prep_unflatten                        true
% 31.30/4.49  --prep_res_sim                          true
% 31.30/4.49  --prep_upred                            true
% 31.30/4.49  --prep_sem_filter                       exhaustive
% 31.30/4.49  --prep_sem_filter_out                   false
% 31.30/4.49  --pred_elim                             true
% 31.30/4.49  --res_sim_input                         true
% 31.30/4.49  --eq_ax_congr_red                       true
% 31.30/4.49  --pure_diseq_elim                       true
% 31.30/4.49  --brand_transform                       false
% 31.30/4.49  --non_eq_to_eq                          false
% 31.30/4.49  --prep_def_merge                        true
% 31.30/4.49  --prep_def_merge_prop_impl              false
% 31.30/4.49  --prep_def_merge_mbd                    true
% 31.30/4.49  --prep_def_merge_tr_red                 false
% 31.30/4.49  --prep_def_merge_tr_cl                  false
% 31.30/4.49  --smt_preprocessing                     true
% 31.30/4.49  --smt_ac_axioms                         fast
% 31.30/4.49  --preprocessed_out                      false
% 31.30/4.49  --preprocessed_stats                    false
% 31.30/4.49  
% 31.30/4.49  ------ Abstraction refinement Options
% 31.30/4.49  
% 31.30/4.49  --abstr_ref                             []
% 31.30/4.49  --abstr_ref_prep                        false
% 31.30/4.49  --abstr_ref_until_sat                   false
% 31.30/4.49  --abstr_ref_sig_restrict                funpre
% 31.30/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.30/4.49  --abstr_ref_under                       []
% 31.30/4.49  
% 31.30/4.49  ------ SAT Options
% 31.30/4.49  
% 31.30/4.49  --sat_mode                              false
% 31.30/4.49  --sat_fm_restart_options                ""
% 31.30/4.49  --sat_gr_def                            false
% 31.30/4.49  --sat_epr_types                         true
% 31.30/4.49  --sat_non_cyclic_types                  false
% 31.30/4.49  --sat_finite_models                     false
% 31.30/4.49  --sat_fm_lemmas                         false
% 31.30/4.49  --sat_fm_prep                           false
% 31.30/4.49  --sat_fm_uc_incr                        true
% 31.30/4.49  --sat_out_model                         small
% 31.30/4.49  --sat_out_clauses                       false
% 31.30/4.49  
% 31.30/4.49  ------ QBF Options
% 31.30/4.49  
% 31.30/4.49  --qbf_mode                              false
% 31.30/4.49  --qbf_elim_univ                         false
% 31.30/4.49  --qbf_dom_inst                          none
% 31.30/4.49  --qbf_dom_pre_inst                      false
% 31.30/4.49  --qbf_sk_in                             false
% 31.30/4.49  --qbf_pred_elim                         true
% 31.30/4.49  --qbf_split                             512
% 31.30/4.49  
% 31.30/4.49  ------ BMC1 Options
% 31.30/4.49  
% 31.30/4.49  --bmc1_incremental                      false
% 31.30/4.49  --bmc1_axioms                           reachable_all
% 31.30/4.49  --bmc1_min_bound                        0
% 31.30/4.49  --bmc1_max_bound                        -1
% 31.30/4.49  --bmc1_max_bound_default                -1
% 31.30/4.49  --bmc1_symbol_reachability              true
% 31.30/4.49  --bmc1_property_lemmas                  false
% 31.30/4.49  --bmc1_k_induction                      false
% 31.30/4.49  --bmc1_non_equiv_states                 false
% 31.30/4.49  --bmc1_deadlock                         false
% 31.30/4.49  --bmc1_ucm                              false
% 31.30/4.49  --bmc1_add_unsat_core                   none
% 31.30/4.49  --bmc1_unsat_core_children              false
% 31.30/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.30/4.49  --bmc1_out_stat                         full
% 31.30/4.49  --bmc1_ground_init                      false
% 31.30/4.49  --bmc1_pre_inst_next_state              false
% 31.30/4.49  --bmc1_pre_inst_state                   false
% 31.30/4.49  --bmc1_pre_inst_reach_state             false
% 31.30/4.49  --bmc1_out_unsat_core                   false
% 31.30/4.49  --bmc1_aig_witness_out                  false
% 31.30/4.49  --bmc1_verbose                          false
% 31.30/4.49  --bmc1_dump_clauses_tptp                false
% 31.30/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.30/4.49  --bmc1_dump_file                        -
% 31.30/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.30/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.30/4.49  --bmc1_ucm_extend_mode                  1
% 31.30/4.49  --bmc1_ucm_init_mode                    2
% 31.30/4.49  --bmc1_ucm_cone_mode                    none
% 31.30/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.30/4.49  --bmc1_ucm_relax_model                  4
% 31.30/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.30/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.30/4.49  --bmc1_ucm_layered_model                none
% 31.30/4.49  --bmc1_ucm_max_lemma_size               10
% 31.30/4.49  
% 31.30/4.49  ------ AIG Options
% 31.30/4.49  
% 31.30/4.49  --aig_mode                              false
% 31.30/4.49  
% 31.30/4.49  ------ Instantiation Options
% 31.30/4.49  
% 31.30/4.49  --instantiation_flag                    true
% 31.30/4.49  --inst_sos_flag                         true
% 31.30/4.49  --inst_sos_phase                        true
% 31.30/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.30/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.30/4.49  --inst_lit_sel_side                     num_symb
% 31.30/4.49  --inst_solver_per_active                1400
% 31.30/4.49  --inst_solver_calls_frac                1.
% 31.30/4.49  --inst_passive_queue_type               priority_queues
% 31.30/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.30/4.49  --inst_passive_queues_freq              [25;2]
% 31.30/4.49  --inst_dismatching                      true
% 31.30/4.49  --inst_eager_unprocessed_to_passive     true
% 31.30/4.49  --inst_prop_sim_given                   true
% 31.30/4.49  --inst_prop_sim_new                     false
% 31.30/4.49  --inst_subs_new                         false
% 31.30/4.49  --inst_eq_res_simp                      false
% 31.30/4.49  --inst_subs_given                       false
% 31.30/4.49  --inst_orphan_elimination               true
% 31.30/4.49  --inst_learning_loop_flag               true
% 31.30/4.49  --inst_learning_start                   3000
% 31.30/4.49  --inst_learning_factor                  2
% 31.30/4.49  --inst_start_prop_sim_after_learn       3
% 31.30/4.49  --inst_sel_renew                        solver
% 31.30/4.49  --inst_lit_activity_flag                true
% 31.30/4.49  --inst_restr_to_given                   false
% 31.30/4.49  --inst_activity_threshold               500
% 31.30/4.49  --inst_out_proof                        true
% 31.30/4.49  
% 31.30/4.49  ------ Resolution Options
% 31.30/4.49  
% 31.30/4.49  --resolution_flag                       true
% 31.30/4.49  --res_lit_sel                           adaptive
% 31.30/4.49  --res_lit_sel_side                      none
% 31.30/4.49  --res_ordering                          kbo
% 31.30/4.49  --res_to_prop_solver                    active
% 31.30/4.49  --res_prop_simpl_new                    false
% 31.30/4.49  --res_prop_simpl_given                  true
% 31.30/4.49  --res_passive_queue_type                priority_queues
% 31.30/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.30/4.49  --res_passive_queues_freq               [15;5]
% 31.30/4.49  --res_forward_subs                      full
% 31.30/4.49  --res_backward_subs                     full
% 31.30/4.49  --res_forward_subs_resolution           true
% 31.30/4.49  --res_backward_subs_resolution          true
% 31.30/4.49  --res_orphan_elimination                true
% 31.30/4.49  --res_time_limit                        2.
% 31.30/4.49  --res_out_proof                         true
% 31.30/4.49  
% 31.30/4.49  ------ Superposition Options
% 31.30/4.49  
% 31.30/4.49  --superposition_flag                    true
% 31.30/4.49  --sup_passive_queue_type                priority_queues
% 31.30/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.30/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.30/4.49  --demod_completeness_check              fast
% 31.30/4.49  --demod_use_ground                      true
% 31.30/4.49  --sup_to_prop_solver                    passive
% 31.30/4.49  --sup_prop_simpl_new                    true
% 31.30/4.49  --sup_prop_simpl_given                  true
% 31.30/4.49  --sup_fun_splitting                     true
% 31.30/4.49  --sup_smt_interval                      50000
% 31.30/4.49  
% 31.30/4.49  ------ Superposition Simplification Setup
% 31.30/4.49  
% 31.30/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.30/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.30/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.30/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.30/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.30/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.30/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.30/4.49  --sup_immed_triv                        [TrivRules]
% 31.30/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.30/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.30/4.49  --sup_immed_bw_main                     []
% 31.30/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.30/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.30/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.30/4.49  --sup_input_bw                          []
% 31.30/4.49  
% 31.30/4.49  ------ Combination Options
% 31.30/4.49  
% 31.30/4.49  --comb_res_mult                         3
% 31.30/4.49  --comb_sup_mult                         2
% 31.30/4.49  --comb_inst_mult                        10
% 31.30/4.49  
% 31.30/4.49  ------ Debug Options
% 31.30/4.49  
% 31.30/4.49  --dbg_backtrace                         false
% 31.30/4.49  --dbg_dump_prop_clauses                 false
% 31.30/4.49  --dbg_dump_prop_clauses_file            -
% 31.30/4.49  --dbg_out_stat                          false
% 31.30/4.49  ------ Parsing...
% 31.30/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.30/4.49  
% 31.30/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.30/4.49  
% 31.30/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.30/4.49  
% 31.30/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.30/4.49  ------ Proving...
% 31.30/4.49  ------ Problem Properties 
% 31.30/4.49  
% 31.30/4.49  
% 31.30/4.49  clauses                                 10
% 31.30/4.49  conjectures                             2
% 31.30/4.49  EPR                                     1
% 31.30/4.49  Horn                                    10
% 31.30/4.49  unary                                   6
% 31.30/4.49  binary                                  4
% 31.30/4.49  lits                                    14
% 31.30/4.49  lits eq                                 5
% 31.30/4.49  fd_pure                                 0
% 31.30/4.49  fd_pseudo                               0
% 31.30/4.49  fd_cond                                 0
% 31.30/4.49  fd_pseudo_cond                          0
% 31.30/4.49  AC symbols                              0
% 31.30/4.49  
% 31.30/4.49  ------ Schedule dynamic 5 is on 
% 31.30/4.49  
% 31.30/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.30/4.49  
% 31.30/4.49  
% 31.30/4.49  ------ 
% 31.30/4.49  Current options:
% 31.30/4.49  ------ 
% 31.30/4.49  
% 31.30/4.49  ------ Input Options
% 31.30/4.49  
% 31.30/4.49  --out_options                           all
% 31.30/4.49  --tptp_safe_out                         true
% 31.30/4.49  --problem_path                          ""
% 31.30/4.49  --include_path                          ""
% 31.30/4.49  --clausifier                            res/vclausify_rel
% 31.30/4.49  --clausifier_options                    ""
% 31.30/4.49  --stdin                                 false
% 31.30/4.49  --stats_out                             all
% 31.30/4.49  
% 31.30/4.49  ------ General Options
% 31.30/4.49  
% 31.30/4.49  --fof                                   false
% 31.30/4.49  --time_out_real                         305.
% 31.30/4.49  --time_out_virtual                      -1.
% 31.30/4.49  --symbol_type_check                     false
% 31.30/4.49  --clausify_out                          false
% 31.30/4.49  --sig_cnt_out                           false
% 31.30/4.49  --trig_cnt_out                          false
% 31.30/4.49  --trig_cnt_out_tolerance                1.
% 31.30/4.49  --trig_cnt_out_sk_spl                   false
% 31.30/4.49  --abstr_cl_out                          false
% 31.30/4.49  
% 31.30/4.49  ------ Global Options
% 31.30/4.49  
% 31.30/4.49  --schedule                              default
% 31.30/4.49  --add_important_lit                     false
% 31.30/4.49  --prop_solver_per_cl                    1000
% 31.30/4.49  --min_unsat_core                        false
% 31.30/4.49  --soft_assumptions                      false
% 31.30/4.49  --soft_lemma_size                       3
% 31.30/4.49  --prop_impl_unit_size                   0
% 31.30/4.49  --prop_impl_unit                        []
% 31.30/4.49  --share_sel_clauses                     true
% 31.30/4.49  --reset_solvers                         false
% 31.30/4.49  --bc_imp_inh                            [conj_cone]
% 31.30/4.49  --conj_cone_tolerance                   3.
% 31.30/4.49  --extra_neg_conj                        none
% 31.30/4.49  --large_theory_mode                     true
% 31.30/4.49  --prolific_symb_bound                   200
% 31.30/4.49  --lt_threshold                          2000
% 31.30/4.49  --clause_weak_htbl                      true
% 31.30/4.49  --gc_record_bc_elim                     false
% 31.30/4.49  
% 31.30/4.49  ------ Preprocessing Options
% 31.30/4.49  
% 31.30/4.49  --preprocessing_flag                    true
% 31.30/4.49  --time_out_prep_mult                    0.1
% 31.30/4.49  --splitting_mode                        input
% 31.30/4.49  --splitting_grd                         true
% 31.30/4.49  --splitting_cvd                         false
% 31.30/4.49  --splitting_cvd_svl                     false
% 31.30/4.49  --splitting_nvd                         32
% 31.30/4.49  --sub_typing                            true
% 31.30/4.49  --prep_gs_sim                           true
% 31.30/4.49  --prep_unflatten                        true
% 31.30/4.49  --prep_res_sim                          true
% 31.30/4.49  --prep_upred                            true
% 31.30/4.49  --prep_sem_filter                       exhaustive
% 31.30/4.49  --prep_sem_filter_out                   false
% 31.30/4.49  --pred_elim                             true
% 31.30/4.49  --res_sim_input                         true
% 31.30/4.49  --eq_ax_congr_red                       true
% 31.30/4.49  --pure_diseq_elim                       true
% 31.30/4.49  --brand_transform                       false
% 31.30/4.49  --non_eq_to_eq                          false
% 31.30/4.49  --prep_def_merge                        true
% 31.30/4.49  --prep_def_merge_prop_impl              false
% 31.30/4.49  --prep_def_merge_mbd                    true
% 31.30/4.49  --prep_def_merge_tr_red                 false
% 31.30/4.49  --prep_def_merge_tr_cl                  false
% 31.30/4.49  --smt_preprocessing                     true
% 31.30/4.49  --smt_ac_axioms                         fast
% 31.30/4.49  --preprocessed_out                      false
% 31.30/4.49  --preprocessed_stats                    false
% 31.30/4.49  
% 31.30/4.49  ------ Abstraction refinement Options
% 31.30/4.49  
% 31.30/4.49  --abstr_ref                             []
% 31.30/4.49  --abstr_ref_prep                        false
% 31.30/4.49  --abstr_ref_until_sat                   false
% 31.30/4.49  --abstr_ref_sig_restrict                funpre
% 31.30/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.30/4.49  --abstr_ref_under                       []
% 31.30/4.49  
% 31.30/4.49  ------ SAT Options
% 31.30/4.49  
% 31.30/4.49  --sat_mode                              false
% 31.30/4.49  --sat_fm_restart_options                ""
% 31.30/4.49  --sat_gr_def                            false
% 31.30/4.49  --sat_epr_types                         true
% 31.30/4.49  --sat_non_cyclic_types                  false
% 31.30/4.49  --sat_finite_models                     false
% 31.30/4.49  --sat_fm_lemmas                         false
% 31.30/4.49  --sat_fm_prep                           false
% 31.30/4.49  --sat_fm_uc_incr                        true
% 31.30/4.49  --sat_out_model                         small
% 31.30/4.49  --sat_out_clauses                       false
% 31.30/4.49  
% 31.30/4.49  ------ QBF Options
% 31.30/4.49  
% 31.30/4.49  --qbf_mode                              false
% 31.30/4.49  --qbf_elim_univ                         false
% 31.30/4.49  --qbf_dom_inst                          none
% 31.30/4.49  --qbf_dom_pre_inst                      false
% 31.30/4.49  --qbf_sk_in                             false
% 31.30/4.49  --qbf_pred_elim                         true
% 31.30/4.49  --qbf_split                             512
% 31.30/4.49  
% 31.30/4.49  ------ BMC1 Options
% 31.30/4.49  
% 31.30/4.49  --bmc1_incremental                      false
% 31.30/4.49  --bmc1_axioms                           reachable_all
% 31.30/4.49  --bmc1_min_bound                        0
% 31.30/4.49  --bmc1_max_bound                        -1
% 31.30/4.49  --bmc1_max_bound_default                -1
% 31.30/4.49  --bmc1_symbol_reachability              true
% 31.30/4.49  --bmc1_property_lemmas                  false
% 31.30/4.49  --bmc1_k_induction                      false
% 31.30/4.49  --bmc1_non_equiv_states                 false
% 31.30/4.49  --bmc1_deadlock                         false
% 31.30/4.49  --bmc1_ucm                              false
% 31.30/4.49  --bmc1_add_unsat_core                   none
% 31.30/4.49  --bmc1_unsat_core_children              false
% 31.30/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.30/4.49  --bmc1_out_stat                         full
% 31.30/4.49  --bmc1_ground_init                      false
% 31.30/4.49  --bmc1_pre_inst_next_state              false
% 31.30/4.49  --bmc1_pre_inst_state                   false
% 31.30/4.49  --bmc1_pre_inst_reach_state             false
% 31.30/4.49  --bmc1_out_unsat_core                   false
% 31.30/4.49  --bmc1_aig_witness_out                  false
% 31.30/4.49  --bmc1_verbose                          false
% 31.30/4.49  --bmc1_dump_clauses_tptp                false
% 31.30/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.30/4.49  --bmc1_dump_file                        -
% 31.30/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.30/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.30/4.49  --bmc1_ucm_extend_mode                  1
% 31.30/4.49  --bmc1_ucm_init_mode                    2
% 31.30/4.49  --bmc1_ucm_cone_mode                    none
% 31.30/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.30/4.49  --bmc1_ucm_relax_model                  4
% 31.30/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.30/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.30/4.49  --bmc1_ucm_layered_model                none
% 31.30/4.49  --bmc1_ucm_max_lemma_size               10
% 31.30/4.49  
% 31.30/4.49  ------ AIG Options
% 31.30/4.49  
% 31.30/4.49  --aig_mode                              false
% 31.30/4.49  
% 31.30/4.49  ------ Instantiation Options
% 31.30/4.49  
% 31.30/4.49  --instantiation_flag                    true
% 31.30/4.49  --inst_sos_flag                         true
% 31.30/4.49  --inst_sos_phase                        true
% 31.30/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.30/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.30/4.49  --inst_lit_sel_side                     none
% 31.30/4.49  --inst_solver_per_active                1400
% 31.30/4.49  --inst_solver_calls_frac                1.
% 31.30/4.49  --inst_passive_queue_type               priority_queues
% 31.30/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.30/4.49  --inst_passive_queues_freq              [25;2]
% 31.30/4.49  --inst_dismatching                      true
% 31.30/4.49  --inst_eager_unprocessed_to_passive     true
% 31.30/4.49  --inst_prop_sim_given                   true
% 31.30/4.49  --inst_prop_sim_new                     false
% 31.30/4.49  --inst_subs_new                         false
% 31.30/4.49  --inst_eq_res_simp                      false
% 31.30/4.49  --inst_subs_given                       false
% 31.30/4.49  --inst_orphan_elimination               true
% 31.30/4.49  --inst_learning_loop_flag               true
% 31.30/4.49  --inst_learning_start                   3000
% 31.30/4.49  --inst_learning_factor                  2
% 31.30/4.49  --inst_start_prop_sim_after_learn       3
% 31.30/4.49  --inst_sel_renew                        solver
% 31.30/4.49  --inst_lit_activity_flag                true
% 31.30/4.49  --inst_restr_to_given                   false
% 31.30/4.49  --inst_activity_threshold               500
% 31.30/4.49  --inst_out_proof                        true
% 31.30/4.49  
% 31.30/4.49  ------ Resolution Options
% 31.30/4.49  
% 31.30/4.49  --resolution_flag                       false
% 31.30/4.49  --res_lit_sel                           adaptive
% 31.30/4.49  --res_lit_sel_side                      none
% 31.30/4.49  --res_ordering                          kbo
% 31.30/4.49  --res_to_prop_solver                    active
% 31.30/4.49  --res_prop_simpl_new                    false
% 31.30/4.49  --res_prop_simpl_given                  true
% 31.30/4.49  --res_passive_queue_type                priority_queues
% 31.30/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.30/4.49  --res_passive_queues_freq               [15;5]
% 31.30/4.49  --res_forward_subs                      full
% 31.30/4.49  --res_backward_subs                     full
% 31.30/4.49  --res_forward_subs_resolution           true
% 31.30/4.49  --res_backward_subs_resolution          true
% 31.30/4.49  --res_orphan_elimination                true
% 31.30/4.49  --res_time_limit                        2.
% 31.30/4.49  --res_out_proof                         true
% 31.30/4.49  
% 31.30/4.49  ------ Superposition Options
% 31.30/4.49  
% 31.30/4.49  --superposition_flag                    true
% 31.30/4.49  --sup_passive_queue_type                priority_queues
% 31.30/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.30/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.30/4.49  --demod_completeness_check              fast
% 31.30/4.49  --demod_use_ground                      true
% 31.30/4.49  --sup_to_prop_solver                    passive
% 31.30/4.49  --sup_prop_simpl_new                    true
% 31.30/4.49  --sup_prop_simpl_given                  true
% 31.30/4.49  --sup_fun_splitting                     true
% 31.30/4.49  --sup_smt_interval                      50000
% 31.30/4.49  
% 31.30/4.49  ------ Superposition Simplification Setup
% 31.30/4.49  
% 31.30/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.30/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.30/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.30/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.30/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.30/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.30/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.30/4.49  --sup_immed_triv                        [TrivRules]
% 31.30/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.30/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.30/4.49  --sup_immed_bw_main                     []
% 31.30/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.30/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.30/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.30/4.49  --sup_input_bw                          []
% 31.30/4.49  
% 31.30/4.49  ------ Combination Options
% 31.30/4.49  
% 31.30/4.49  --comb_res_mult                         3
% 31.30/4.49  --comb_sup_mult                         2
% 31.30/4.49  --comb_inst_mult                        10
% 31.30/4.49  
% 31.30/4.49  ------ Debug Options
% 31.30/4.49  
% 31.30/4.49  --dbg_backtrace                         false
% 31.30/4.49  --dbg_dump_prop_clauses                 false
% 31.30/4.49  --dbg_dump_prop_clauses_file            -
% 31.30/4.49  --dbg_out_stat                          false
% 31.30/4.49  
% 31.30/4.49  
% 31.30/4.49  
% 31.30/4.49  
% 31.30/4.49  ------ Proving...
% 31.30/4.49  
% 31.30/4.49  
% 31.30/4.49  % SZS status Theorem for theBenchmark.p
% 31.30/4.49  
% 31.30/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.30/4.49  
% 31.30/4.49  fof(f9,conjecture,(
% 31.30/4.49    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 31.30/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.30/4.49  
% 31.30/4.49  fof(f10,negated_conjecture,(
% 31.30/4.49    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 31.30/4.49    inference(negated_conjecture,[],[f9])).
% 31.30/4.49  
% 31.30/4.49  fof(f13,plain,(
% 31.30/4.49    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 31.30/4.49    inference(ennf_transformation,[],[f10])).
% 31.30/4.49  
% 31.30/4.49  fof(f15,plain,(
% 31.30/4.49    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 31.30/4.49    introduced(choice_axiom,[])).
% 31.30/4.49  
% 31.30/4.49  fof(f16,plain,(
% 31.30/4.49    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 31.30/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 31.30/4.49  
% 31.30/4.49  fof(f26,plain,(
% 31.30/4.49    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 31.30/4.49    inference(cnf_transformation,[],[f16])).
% 31.30/4.49  
% 31.30/4.49  fof(f1,axiom,(
% 31.30/4.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 31.30/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.30/4.49  
% 31.30/4.49  fof(f14,plain,(
% 31.30/4.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 31.30/4.49    inference(nnf_transformation,[],[f1])).
% 31.30/4.49  
% 31.30/4.49  fof(f17,plain,(
% 31.30/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 31.30/4.49    inference(cnf_transformation,[],[f14])).
% 31.30/4.49  
% 31.30/4.49  fof(f5,axiom,(
% 31.30/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 31.30/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.30/4.49  
% 31.30/4.49  fof(f22,plain,(
% 31.30/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.30/4.49    inference(cnf_transformation,[],[f5])).
% 31.30/4.49  
% 31.30/4.49  fof(f29,plain,(
% 31.30/4.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 31.30/4.49    inference(definition_unfolding,[],[f17,f22])).
% 31.30/4.49  
% 31.30/4.49  fof(f4,axiom,(
% 31.30/4.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.30/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.30/4.49  
% 31.30/4.49  fof(f21,plain,(
% 31.30/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.30/4.49    inference(cnf_transformation,[],[f4])).
% 31.30/4.49  
% 31.30/4.49  fof(f30,plain,(
% 31.30/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 31.30/4.49    inference(definition_unfolding,[],[f21,f22])).
% 31.30/4.49  
% 31.30/4.49  fof(f3,axiom,(
% 31.30/4.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 31.30/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.30/4.49  
% 31.30/4.49  fof(f20,plain,(
% 31.30/4.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.30/4.49    inference(cnf_transformation,[],[f3])).
% 31.30/4.49  
% 31.30/4.49  fof(f6,axiom,(
% 31.30/4.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 31.30/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.30/4.49  
% 31.30/4.49  fof(f23,plain,(
% 31.30/4.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 31.30/4.49    inference(cnf_transformation,[],[f6])).
% 31.30/4.49  
% 31.30/4.49  fof(f31,plain,(
% 31.30/4.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 31.30/4.49    inference(definition_unfolding,[],[f23,f22,f22])).
% 31.30/4.49  
% 31.30/4.49  fof(f7,axiom,(
% 31.30/4.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 31.30/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.30/4.49  
% 31.30/4.49  fof(f24,plain,(
% 31.30/4.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 31.30/4.49    inference(cnf_transformation,[],[f7])).
% 31.30/4.49  
% 31.30/4.49  fof(f2,axiom,(
% 31.30/4.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 31.30/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.30/4.49  
% 31.30/4.49  fof(f11,plain,(
% 31.30/4.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 31.30/4.49    inference(ennf_transformation,[],[f2])).
% 31.30/4.49  
% 31.30/4.49  fof(f19,plain,(
% 31.30/4.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 31.30/4.49    inference(cnf_transformation,[],[f11])).
% 31.30/4.49  
% 31.30/4.49  fof(f8,axiom,(
% 31.30/4.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 31.30/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.30/4.49  
% 31.30/4.49  fof(f12,plain,(
% 31.30/4.49    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 31.30/4.49    inference(ennf_transformation,[],[f8])).
% 31.30/4.49  
% 31.30/4.49  fof(f25,plain,(
% 31.30/4.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 31.30/4.49    inference(cnf_transformation,[],[f12])).
% 31.30/4.49  
% 31.30/4.49  fof(f27,plain,(
% 31.30/4.49    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 31.30/4.49    inference(cnf_transformation,[],[f16])).
% 31.30/4.49  
% 31.30/4.49  cnf(c_9,negated_conjecture,
% 31.30/4.49      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 31.30/4.49      inference(cnf_transformation,[],[f26]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_281,plain,
% 31.30/4.49      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 31.30/4.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1,plain,
% 31.30/4.49      ( ~ r1_xboole_0(X0,X1)
% 31.30/4.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 31.30/4.49      inference(cnf_transformation,[],[f29]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_286,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 31.30/4.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 31.30/4.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1458,plain,
% 31.30/4.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_281,c_286]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_4,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.30/4.49      inference(cnf_transformation,[],[f30]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1677,plain,
% 31.30/4.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_1458,c_4]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_3,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.30/4.49      inference(cnf_transformation,[],[f20]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1690,plain,
% 31.30/4.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_1677,c_3]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_5,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 31.30/4.49      inference(cnf_transformation,[],[f31]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_6,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 31.30/4.49      inference(cnf_transformation,[],[f24]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_284,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 31.30/4.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_639,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_5,c_284]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_758,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))))),X3) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_5,c_639]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_11367,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_1690,c_758]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_12324,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))),k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_11367,c_286]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_12326,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,sK0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,sK0)),k4_xboole_0(sK1,sK2))))))) = k1_xboole_0 ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_12324,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_12327,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,sK0)),k4_xboole_0(sK1,sK2))))))))) = k1_xboole_0 ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_12326,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_12328,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))))))))) = k1_xboole_0 ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_12327,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_12329,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0))))))))) = k1_xboole_0 ),
% 31.30/4.49      inference(light_normalisation,[status(thm)],[c_12328,c_1690]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_12704,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))))))) = k4_xboole_0(X0,k1_xboole_0) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_12329,c_4]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_12825,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))))))) = X0 ),
% 31.30/4.49      inference(light_normalisation,[status(thm)],[c_12704,c_3]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_409,plain,
% 31.30/4.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_3,c_284]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1459,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_409,c_286]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1472,plain,
% 31.30/4.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.30/4.49      inference(light_normalisation,[status(thm)],[c_1459,c_3]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_643,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_648,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_643,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_649,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_648,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_5859,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0))))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_1472,c_649]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_2,plain,
% 31.30/4.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 31.30/4.49      inference(cnf_transformation,[],[f19]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_285,plain,
% 31.30/4.49      ( r1_xboole_0(X0,X1) != iProver_top
% 31.30/4.49      | r1_xboole_0(X1,X0) = iProver_top ),
% 31.30/4.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_775,plain,
% 31.30/4.49      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_284,c_285]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1463,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_775,c_286]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_6075,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_5859,c_3,c_1463,c_1472]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1788,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_1690,c_639]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_2074,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_1788,c_286]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_2076,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))))) = k1_xboole_0 ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_2074,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_2077,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))))) = k1_xboole_0 ),
% 31.30/4.49      inference(light_normalisation,[status(thm)],[c_2076,c_1690]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_2543,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),X1))) = k4_xboole_0(k1_xboole_0,X1) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_2077,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_776,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_281,c_285]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1461,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)) = k1_xboole_0 ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_776,c_286]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1769,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_1461,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1922,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,sK0) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_1472,c_1769]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1969,plain,
% 31.30/4.49      ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_1922,c_3,c_1472]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_2262,plain,
% 31.30/4.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_1969,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_777,plain,
% 31.30/4.49      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_409,c_285]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1464,plain,
% 31.30/4.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_777,c_286]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_2273,plain,
% 31.30/4.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_2262,c_3,c_1464]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_2692,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),X1))) = k1_xboole_0 ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_2543,c_2273]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_4346,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),X1)) = k4_xboole_0(X0,k1_xboole_0) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_2692,c_4]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_4386,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),X1)) = X0 ),
% 31.30/4.49      inference(light_normalisation,[status(thm)],[c_4346,c_3]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_6489,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),X1)) = k4_xboole_0(sK0,X0) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_6075,c_4386]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_6665,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1)))) = k4_xboole_0(sK0,X0) ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_6489,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_14789,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0)),X2) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_6665,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_6475,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_6075,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_14851,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
% 31.30/4.49      inference(demodulation,
% 31.30/4.49                [status(thm)],
% 31.30/4.49                [c_14789,c_5,c_1472,c_2273,c_6475]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_15582,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_14851,c_12825]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_15833,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sK0,X0)) = k4_xboole_0(X0,X1) ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_15582,c_3]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_19700,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))))))) = k4_xboole_0(X0,k4_xboole_0(sK0,X0)) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_12825,c_15833]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_19881,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(sK0,X0)) = X0 ),
% 31.30/4.49      inference(light_normalisation,[status(thm)],[c_19700,c_12825]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_640,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),X3) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_652,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))) ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_640,c_5]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_7555,plain,
% 31.30/4.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)),X0))) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_1690,c_652]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_7999,plain,
% 31.30/4.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_7555,c_3,c_1472]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_8483,plain,
% 31.30/4.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0)))) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_7999,c_4]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_8535,plain,
% 31.30/4.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_8483,c_4]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_25215,plain,
% 31.30/4.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_19881,c_8535]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_25326,plain,
% 31.30/4.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK0))) ),
% 31.30/4.49      inference(light_normalisation,[status(thm)],[c_25215,c_1690]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_25327,plain,
% 31.30/4.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,sK1) ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_25326,c_3,c_1472]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_780,plain,
% 31.30/4.49      ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_639,c_285]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_25619,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_25327,c_780]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_7,plain,
% 31.30/4.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 31.30/4.49      inference(cnf_transformation,[],[f25]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_283,plain,
% 31.30/4.49      ( r1_xboole_0(X0,X1) != iProver_top
% 31.30/4.49      | r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 31.30/4.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1457,plain,
% 31.30/4.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k1_xboole_0
% 31.30/4.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_283,c_286]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_129388,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0))) = k1_xboole_0 ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_25619,c_1457]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_129772,plain,
% 31.30/4.49      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k1_xboole_0 ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_129388,c_5,c_6475]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_1047,plain,
% 31.30/4.49      ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X0)))))) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_5,c_780]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_15106,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)))) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_14851,c_1047]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_15129,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(sK0,X0)))) = iProver_top ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_15106,c_3]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_130322,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)) = iProver_top ),
% 31.30/4.49      inference(superposition,[status(thm)],[c_129772,c_15129]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_130323,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),X1),X2),k4_xboole_0(sK0,sK2)) = iProver_top ),
% 31.30/4.49      inference(demodulation,[status(thm)],[c_130322,c_3]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_130475,plain,
% 31.30/4.49      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0),k4_xboole_0(sK0,sK2)) = iProver_top ),
% 31.30/4.49      inference(instantiation,[status(thm)],[c_130323]) ).
% 31.30/4.49  
% 31.30/4.49  cnf(c_107,plain,
% 31.30/4.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.30/4.49      theory(equality) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_306,plain,
% 31.30/4.50      ( ~ r1_xboole_0(X0,X1)
% 31.30/4.50      | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
% 31.30/4.50      | k4_xboole_0(sK0,sK2) != X1
% 31.30/4.50      | sK1 != X0 ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_107]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_38715,plain,
% 31.30/4.50      ( ~ r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0),X0)
% 31.30/4.50      | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
% 31.30/4.50      | k4_xboole_0(sK0,sK2) != X0
% 31.30/4.50      | sK1 != k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_306]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_77544,plain,
% 31.30/4.50      ( ~ r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0),k4_xboole_0(sK0,sK2))
% 31.30/4.50      | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
% 31.30/4.50      | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)
% 31.30/4.50      | sK1 != k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_38715]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_77545,plain,
% 31.30/4.50      ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)
% 31.30/4.50      | sK1 != k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0)
% 31.30/4.50      | r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0),k4_xboole_0(sK0,sK2)) != iProver_top
% 31.30/4.50      | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = iProver_top ),
% 31.30/4.50      inference(predicate_to_equality,[status(thm)],[c_77544]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_14589,plain,
% 31.30/4.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_3]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_106,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_342,plain,
% 31.30/4.50      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_106]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_2857,plain,
% 31.30/4.50      ( X0 != k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)
% 31.30/4.50      | sK1 = X0
% 31.30/4.50      | sK1 != k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_342]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_5475,plain,
% 31.30/4.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)
% 31.30/4.50      | sK1 = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0),k1_xboole_0)
% 31.30/4.50      | sK1 != k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_2857]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_105,plain,( X0 = X0 ),theory(equality) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_3784,plain,
% 31.30/4.50      ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_105]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_1997,plain,
% 31.30/4.50      ( k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0) ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_3]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_933,plain,
% 31.30/4.50      ( X0 != k4_xboole_0(sK1,k1_xboole_0)
% 31.30/4.50      | sK1 = X0
% 31.30/4.50      | sK1 != k4_xboole_0(sK1,k1_xboole_0) ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_342]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_1125,plain,
% 31.30/4.50      ( k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) != k4_xboole_0(sK1,k1_xboole_0)
% 31.30/4.50      | sK1 = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)
% 31.30/4.50      | sK1 != k4_xboole_0(sK1,k1_xboole_0) ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_933]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_571,plain,
% 31.30/4.50      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_3]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_389,plain,
% 31.30/4.50      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_342]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_469,plain,
% 31.30/4.50      ( k4_xboole_0(sK1,k1_xboole_0) != sK1
% 31.30/4.50      | sK1 = k4_xboole_0(sK1,k1_xboole_0)
% 31.30/4.50      | sK1 != sK1 ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_389]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_375,plain,
% 31.30/4.50      ( sK1 = sK1 ),
% 31.30/4.50      inference(instantiation,[status(thm)],[c_105]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_8,negated_conjecture,
% 31.30/4.50      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 31.30/4.50      inference(cnf_transformation,[],[f27]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(c_11,plain,
% 31.30/4.50      ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != iProver_top ),
% 31.30/4.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.30/4.50  
% 31.30/4.50  cnf(contradiction,plain,
% 31.30/4.50      ( $false ),
% 31.30/4.50      inference(minisat,
% 31.30/4.50                [status(thm)],
% 31.30/4.50                [c_130475,c_77545,c_14589,c_5475,c_3784,c_1997,c_1125,
% 31.30/4.50                 c_571,c_469,c_375,c_11]) ).
% 31.30/4.50  
% 31.30/4.50  
% 31.30/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.30/4.50  
% 31.30/4.50  ------                               Statistics
% 31.30/4.50  
% 31.30/4.50  ------ General
% 31.30/4.50  
% 31.30/4.50  abstr_ref_over_cycles:                  0
% 31.30/4.50  abstr_ref_under_cycles:                 0
% 31.30/4.50  gc_basic_clause_elim:                   0
% 31.30/4.50  forced_gc_time:                         0
% 31.30/4.50  parsing_time:                           0.006
% 31.30/4.50  unif_index_cands_time:                  0.
% 31.30/4.50  unif_index_add_time:                    0.
% 31.30/4.50  orderings_time:                         0.
% 31.30/4.50  out_proof_time:                         0.013
% 31.30/4.50  total_time:                             3.547
% 31.30/4.50  num_of_symbols:                         37
% 31.30/4.50  num_of_terms:                           139966
% 31.30/4.50  
% 31.30/4.50  ------ Preprocessing
% 31.30/4.50  
% 31.30/4.50  num_of_splits:                          0
% 31.30/4.50  num_of_split_atoms:                     0
% 31.30/4.50  num_of_reused_defs:                     0
% 31.30/4.50  num_eq_ax_congr_red:                    0
% 31.30/4.50  num_of_sem_filtered_clauses:            1
% 31.30/4.50  num_of_subtypes:                        0
% 31.30/4.50  monotx_restored_types:                  0
% 31.30/4.50  sat_num_of_epr_types:                   0
% 31.30/4.50  sat_num_of_non_cyclic_types:            0
% 31.30/4.50  sat_guarded_non_collapsed_types:        0
% 31.30/4.50  num_pure_diseq_elim:                    0
% 31.30/4.50  simp_replaced_by:                       0
% 31.30/4.50  res_preprocessed:                       39
% 31.30/4.50  prep_upred:                             0
% 31.30/4.50  prep_unflattend:                        0
% 31.30/4.50  smt_new_axioms:                         0
% 31.30/4.50  pred_elim_cands:                        1
% 31.30/4.50  pred_elim:                              0
% 31.30/4.50  pred_elim_cl:                           0
% 31.30/4.50  pred_elim_cycles:                       1
% 31.30/4.50  merged_defs:                            6
% 31.30/4.50  merged_defs_ncl:                        0
% 31.30/4.50  bin_hyper_res:                          6
% 31.30/4.50  prep_cycles:                            3
% 31.30/4.50  pred_elim_time:                         0.
% 31.30/4.50  splitting_time:                         0.
% 31.30/4.50  sem_filter_time:                        0.
% 31.30/4.50  monotx_time:                            0.
% 31.30/4.50  subtype_inf_time:                       0.
% 31.30/4.50  
% 31.30/4.50  ------ Problem properties
% 31.30/4.50  
% 31.30/4.50  clauses:                                10
% 31.30/4.50  conjectures:                            2
% 31.30/4.50  epr:                                    1
% 31.30/4.50  horn:                                   10
% 31.30/4.50  ground:                                 2
% 31.30/4.50  unary:                                  6
% 31.30/4.50  binary:                                 4
% 31.30/4.50  lits:                                   14
% 31.30/4.50  lits_eq:                                5
% 31.30/4.50  fd_pure:                                0
% 31.30/4.50  fd_pseudo:                              0
% 31.30/4.50  fd_cond:                                0
% 31.30/4.50  fd_pseudo_cond:                         0
% 31.30/4.50  ac_symbols:                             0
% 31.30/4.50  
% 31.30/4.50  ------ Propositional Solver
% 31.30/4.50  
% 31.30/4.50  prop_solver_calls:                      33
% 31.30/4.50  prop_fast_solver_calls:                 751
% 31.30/4.50  smt_solver_calls:                       0
% 31.30/4.50  smt_fast_solver_calls:                  0
% 31.30/4.50  prop_num_of_clauses:                    27141
% 31.30/4.50  prop_preprocess_simplified:             28826
% 31.30/4.50  prop_fo_subsumed:                       2
% 31.30/4.50  prop_solver_time:                       0.
% 31.30/4.50  smt_solver_time:                        0.
% 31.30/4.50  smt_fast_solver_time:                   0.
% 31.30/4.50  prop_fast_solver_time:                  0.
% 31.30/4.50  prop_unsat_core_time:                   0.003
% 31.30/4.50  
% 31.30/4.50  ------ QBF
% 31.30/4.50  
% 31.30/4.50  qbf_q_res:                              0
% 31.30/4.50  qbf_num_tautologies:                    0
% 31.30/4.50  qbf_prep_cycles:                        0
% 31.30/4.50  
% 31.30/4.50  ------ BMC1
% 31.30/4.50  
% 31.30/4.50  bmc1_current_bound:                     -1
% 31.30/4.50  bmc1_last_solved_bound:                 -1
% 31.30/4.50  bmc1_unsat_core_size:                   -1
% 31.30/4.50  bmc1_unsat_core_parents_size:           -1
% 31.30/4.50  bmc1_merge_next_fun:                    0
% 31.30/4.50  bmc1_unsat_core_clauses_time:           0.
% 31.30/4.50  
% 31.30/4.50  ------ Instantiation
% 31.30/4.50  
% 31.30/4.50  inst_num_of_clauses:                    7018
% 31.30/4.50  inst_num_in_passive:                    2069
% 31.30/4.50  inst_num_in_active:                     2397
% 31.30/4.50  inst_num_in_unprocessed:                2554
% 31.30/4.50  inst_num_of_loops:                      2570
% 31.30/4.50  inst_num_of_learning_restarts:          0
% 31.30/4.50  inst_num_moves_active_passive:          168
% 31.30/4.50  inst_lit_activity:                      0
% 31.30/4.50  inst_lit_activity_moves:                0
% 31.30/4.50  inst_num_tautologies:                   0
% 31.30/4.50  inst_num_prop_implied:                  0
% 31.30/4.50  inst_num_existing_simplified:           0
% 31.30/4.50  inst_num_eq_res_simplified:             0
% 31.30/4.50  inst_num_child_elim:                    0
% 31.30/4.50  inst_num_of_dismatching_blockings:      9614
% 31.30/4.50  inst_num_of_non_proper_insts:           10588
% 31.30/4.50  inst_num_of_duplicates:                 0
% 31.30/4.50  inst_inst_num_from_inst_to_res:         0
% 31.30/4.50  inst_dismatching_checking_time:         0.
% 31.30/4.50  
% 31.30/4.50  ------ Resolution
% 31.30/4.50  
% 31.30/4.50  res_num_of_clauses:                     0
% 31.30/4.50  res_num_in_passive:                     0
% 31.30/4.50  res_num_in_active:                      0
% 31.30/4.50  res_num_of_loops:                       42
% 31.30/4.50  res_forward_subset_subsumed:            736
% 31.30/4.50  res_backward_subset_subsumed:           12
% 31.30/4.50  res_forward_subsumed:                   0
% 31.30/4.50  res_backward_subsumed:                  0
% 31.30/4.50  res_forward_subsumption_resolution:     0
% 31.30/4.50  res_backward_subsumption_resolution:    0
% 31.30/4.50  res_clause_to_clause_subsumption:       144153
% 31.30/4.50  res_orphan_elimination:                 0
% 31.30/4.50  res_tautology_del:                      872
% 31.30/4.50  res_num_eq_res_simplified:              0
% 31.30/4.50  res_num_sel_changes:                    0
% 31.30/4.50  res_moves_from_active_to_pass:          0
% 31.30/4.50  
% 31.30/4.50  ------ Superposition
% 31.30/4.50  
% 31.30/4.50  sup_time_total:                         0.
% 31.30/4.50  sup_time_generating:                    0.
% 31.30/4.50  sup_time_sim_full:                      0.
% 31.30/4.50  sup_time_sim_immed:                     0.
% 31.30/4.50  
% 31.30/4.50  sup_num_of_clauses:                     4129
% 31.30/4.50  sup_num_in_active:                      414
% 31.30/4.50  sup_num_in_passive:                     3715
% 31.30/4.50  sup_num_of_loops:                       513
% 31.30/4.50  sup_fw_superposition:                   25556
% 31.30/4.50  sup_bw_superposition:                   20107
% 31.30/4.50  sup_immediate_simplified:               23091
% 31.30/4.50  sup_given_eliminated:                   57
% 31.30/4.50  comparisons_done:                       0
% 31.30/4.50  comparisons_avoided:                    0
% 31.30/4.50  
% 31.30/4.50  ------ Simplifications
% 31.30/4.50  
% 31.30/4.50  
% 31.30/4.50  sim_fw_subset_subsumed:                 143
% 31.30/4.50  sim_bw_subset_subsumed:                 1
% 31.30/4.50  sim_fw_subsumed:                        6458
% 31.30/4.50  sim_bw_subsumed:                        110
% 31.30/4.50  sim_fw_subsumption_res:                 0
% 31.30/4.50  sim_bw_subsumption_res:                 0
% 31.30/4.50  sim_tautology_del:                      187
% 31.30/4.50  sim_eq_tautology_del:                   3166
% 31.30/4.50  sim_eq_res_simp:                        74
% 31.30/4.50  sim_fw_demodulated:                     23284
% 31.30/4.50  sim_bw_demodulated:                     289
% 31.30/4.50  sim_light_normalised:                   5602
% 31.30/4.50  sim_joinable_taut:                      0
% 31.30/4.50  sim_joinable_simp:                      0
% 31.30/4.50  sim_ac_normalised:                      0
% 31.30/4.50  sim_smt_subsumption:                    0
% 31.30/4.50  
%------------------------------------------------------------------------------
