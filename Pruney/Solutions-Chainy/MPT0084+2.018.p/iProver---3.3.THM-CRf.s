%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:15 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :  182 (8785 expanded)
%              Number of clauses        :  150 (2336 expanded)
%              Number of leaves         :    9 (2504 expanded)
%              Depth                    :   33
%              Number of atoms          :  218 (13498 expanded)
%              Number of equality atoms :  176 (7735 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f26,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f23,f21,f21,f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f22,f21,f21])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f21,f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f24,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_53,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_7,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_101,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_53,c_7])).

cnf(c_102,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_101])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_184,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_102,c_6])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_153,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_102,c_5])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_168,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_153,c_4])).

cnf(c_233,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_184,c_168])).

cnf(c_234,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_233,c_4])).

cnf(c_265,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_102,c_234])).

cnf(c_288,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK0 ),
    inference(demodulation,[status(thm)],[c_265,c_4])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_161,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_165,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_161,c_5])).

cnf(c_14482,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)))) ),
    inference(superposition,[status(thm)],[c_288,c_165])).

cnf(c_160,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_15014,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))))))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_165,c_160])).

cnf(c_15019,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_165,c_160])).

cnf(c_7540,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) ),
    inference(superposition,[status(thm)],[c_6,c_160])).

cnf(c_143,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_7724,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_160,c_143])).

cnf(c_7750,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_7724,c_5,c_6])).

cnf(c_8144,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
    inference(demodulation,[status(thm)],[c_7540,c_7750])).

cnf(c_205,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_8145,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_8144,c_205])).

cnf(c_15045,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_15019,c_8145])).

cnf(c_15018,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X0))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) ),
    inference(superposition,[status(thm)],[c_165,c_6])).

cnf(c_15046,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) ),
    inference(demodulation,[status(thm)],[c_15018,c_15045])).

cnf(c_15050,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(demodulation,[status(thm)],[c_15014,c_15045,c_15046])).

cnf(c_489,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_143,c_6])).

cnf(c_7438,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_0,c_160])).

cnf(c_466,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) ),
    inference(superposition,[status(thm)],[c_143,c_0])).

cnf(c_522,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_466,c_5])).

cnf(c_8317,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(demodulation,[status(thm)],[c_7438,c_6,c_522])).

cnf(c_15051,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_15050,c_489,c_8317])).

cnf(c_16178,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(demodulation,[status(thm)],[c_14482,c_15051])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_94,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_95,plain,
    ( k4_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_94])).

cnf(c_271,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_102,c_234])).

cnf(c_283,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_271,c_102])).

cnf(c_284,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_283,c_4])).

cnf(c_16179,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_16178,c_95,c_284])).

cnf(c_150,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_429,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK2) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_95,c_143])).

cnf(c_540,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK2) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_429,c_4])).

cnf(c_702,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),sK2) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_540])).

cnf(c_1249,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),X1)),sK2) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_702,c_143])).

cnf(c_465,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1),X3) ),
    inference(superposition,[status(thm)],[c_143,c_143])).

cnf(c_523,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X3) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X3),X2))) ),
    inference(demodulation,[status(thm)],[c_465,c_522])).

cnf(c_524,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))),X2) ),
    inference(light_normalisation,[status(thm)],[c_523,c_5])).

cnf(c_1256,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
    inference(demodulation,[status(thm)],[c_1249,c_5,c_524])).

cnf(c_1257,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_1256,c_95])).

cnf(c_1258,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
    inference(demodulation,[status(thm)],[c_1257,c_5,c_150])).

cnf(c_1322,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_95,c_1258])).

cnf(c_131,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_147,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_131,c_5])).

cnf(c_1240,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0)))),sK2) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_147,c_702])).

cnf(c_176,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_102,c_6])).

cnf(c_146,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_102,c_5])).

cnf(c_170,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_146,c_5])).

cnf(c_242,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_176,c_5,c_170])).

cnf(c_318,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_95,c_242])).

cnf(c_335,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(demodulation,[status(thm)],[c_318,c_4])).

cnf(c_341,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_335,c_131])).

cnf(c_410,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(sK2,sK2)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_341,c_6])).

cnf(c_340,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_335,c_6])).

cnf(c_342,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(sK2,sK2)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK2))) ),
    inference(demodulation,[status(thm)],[c_340,c_341])).

cnf(c_411,plain,
    ( k4_xboole_0(sK0,sK0) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_341,c_131])).

cnf(c_412,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_411,c_284])).

cnf(c_544,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_410,c_342,c_412])).

cnf(c_545,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_544,c_4,c_5])).

cnf(c_1272,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),sK2) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1240,c_545])).

cnf(c_177,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_131,c_6])).

cnf(c_263,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_234])).

cnf(c_964,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_263,c_147])).

cnf(c_152,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_95,c_5])).

cnf(c_169,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_152,c_4])).

cnf(c_314,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_169,c_242])).

cnf(c_967,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_314,c_147])).

cnf(c_339,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_335,c_5])).

cnf(c_343,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK2,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_339,c_341])).

cnf(c_344,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0))) = k4_xboole_0(k4_xboole_0(sK2,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_343,c_314])).

cnf(c_1059,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK2,sK2),X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_967,c_344])).

cnf(c_1060,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_1059,c_4,c_314,c_412])).

cnf(c_1064,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(demodulation,[status(thm)],[c_964,c_1060])).

cnf(c_312,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_242])).

cnf(c_1065,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1064,c_284,c_312])).

cnf(c_1005,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_147,c_0])).

cnf(c_1017,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),sK0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_147,c_312])).

cnf(c_1031,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_1005,c_1017])).

cnf(c_360,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_170,c_234])).

cnf(c_361,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_360,c_170])).

cnf(c_907,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_131,c_361])).

cnf(c_1034,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1031,c_907])).

cnf(c_1066,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_1065,c_1034])).

cnf(c_1013,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X0))),sK2) ),
    inference(superposition,[status(thm)],[c_147,c_540])).

cnf(c_1014,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_147,c_131])).

cnf(c_1024,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X0))),sK2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) ),
    inference(demodulation,[status(thm)],[c_1013,c_1014])).

cnf(c_1025,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),sK2) ),
    inference(light_normalisation,[status(thm)],[c_1024,c_907])).

cnf(c_1067,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),sK2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_1066,c_1025])).

cnf(c_1273,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) ),
    inference(demodulation,[status(thm)],[c_1272,c_177,c_1067])).

cnf(c_1274,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1273,c_1066])).

cnf(c_1422,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1322,c_4,c_1274])).

cnf(c_1323,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_288,c_1258])).

cnf(c_180,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_241,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_180,c_150])).

cnf(c_1421,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X0,X0),sK0) ),
    inference(demodulation,[status(thm)],[c_1323,c_5,c_6,c_241])).

cnf(c_1423,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k4_xboole_0(X0,X0),sK0) ),
    inference(demodulation,[status(thm)],[c_1422,c_1421])).

cnf(c_4550,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0))) ),
    inference(superposition,[status(thm)],[c_150,c_1423])).

cnf(c_438,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_284,c_143])).

cnf(c_538,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK0) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_438,c_4])).

cnf(c_1146,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK0) ),
    inference(superposition,[status(thm)],[c_361,c_538])).

cnf(c_5025,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK0),sK0) ),
    inference(light_normalisation,[status(thm)],[c_4550,c_1146])).

cnf(c_1317,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(sK0,sK0))) = k4_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_361,c_1258])).

cnf(c_969,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_361,c_147])).

cnf(c_1056,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_969,c_284])).

cnf(c_1057,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_1056,c_4,c_150])).

cnf(c_1426,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1317,c_284,c_1057])).

cnf(c_1427,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_1426,c_4,c_522,c_1146])).

cnf(c_2819,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_150,c_5])).

cnf(c_5026,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_5025,c_4,c_150,c_1427,c_2819])).

cnf(c_909,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK0))) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_335,c_361])).

cnf(c_931,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(demodulation,[status(thm)],[c_909,c_361])).

cnf(c_709,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK0),sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_540])).

cnf(c_777,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_709,c_284,c_335])).

cnf(c_778,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_777,c_4])).

cnf(c_932,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_931,c_335,c_778])).

cnf(c_2802,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),sK2) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_932,c_150])).

cnf(c_197,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_95,c_6])).

cnf(c_221,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) ),
    inference(demodulation,[status(thm)],[c_197,c_4,c_5])).

cnf(c_376,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_221,c_242])).

cnf(c_571,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_376,c_242])).

cnf(c_1570,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0))) = k4_xboole_0(k4_xboole_0(X0,X0),sK2) ),
    inference(superposition,[status(thm)],[c_571,c_147])).

cnf(c_1631,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),sK2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1570,c_545])).

cnf(c_2948,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),sK2) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_2802,c_4,c_1631])).

cnf(c_5586,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_5026,c_2948])).

cnf(c_5588,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5586,c_932])).

cnf(c_16180,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16179,c_4,c_5588])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_51,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_106,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_9])).

cnf(c_107,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_106])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16180,c_107])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.08/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/1.49  
% 7.08/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.08/1.49  
% 7.08/1.49  ------  iProver source info
% 7.08/1.49  
% 7.08/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.08/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.08/1.49  git: non_committed_changes: false
% 7.08/1.49  git: last_make_outside_of_git: false
% 7.08/1.49  
% 7.08/1.49  ------ 
% 7.08/1.49  
% 7.08/1.49  ------ Input Options
% 7.08/1.49  
% 7.08/1.49  --out_options                           all
% 7.08/1.49  --tptp_safe_out                         true
% 7.08/1.49  --problem_path                          ""
% 7.08/1.49  --include_path                          ""
% 7.08/1.49  --clausifier                            res/vclausify_rel
% 7.08/1.49  --clausifier_options                    --mode clausify
% 7.08/1.49  --stdin                                 false
% 7.08/1.49  --stats_out                             all
% 7.08/1.49  
% 7.08/1.49  ------ General Options
% 7.08/1.49  
% 7.08/1.49  --fof                                   false
% 7.08/1.49  --time_out_real                         305.
% 7.08/1.49  --time_out_virtual                      -1.
% 7.08/1.49  --symbol_type_check                     false
% 7.08/1.49  --clausify_out                          false
% 7.08/1.49  --sig_cnt_out                           false
% 7.08/1.49  --trig_cnt_out                          false
% 7.08/1.49  --trig_cnt_out_tolerance                1.
% 7.08/1.49  --trig_cnt_out_sk_spl                   false
% 7.08/1.49  --abstr_cl_out                          false
% 7.08/1.49  
% 7.08/1.49  ------ Global Options
% 7.08/1.49  
% 7.08/1.49  --schedule                              default
% 7.08/1.49  --add_important_lit                     false
% 7.08/1.49  --prop_solver_per_cl                    1000
% 7.08/1.49  --min_unsat_core                        false
% 7.08/1.49  --soft_assumptions                      false
% 7.08/1.49  --soft_lemma_size                       3
% 7.08/1.49  --prop_impl_unit_size                   0
% 7.08/1.49  --prop_impl_unit                        []
% 7.08/1.49  --share_sel_clauses                     true
% 7.08/1.49  --reset_solvers                         false
% 7.08/1.49  --bc_imp_inh                            [conj_cone]
% 7.08/1.49  --conj_cone_tolerance                   3.
% 7.08/1.49  --extra_neg_conj                        none
% 7.08/1.49  --large_theory_mode                     true
% 7.08/1.49  --prolific_symb_bound                   200
% 7.08/1.49  --lt_threshold                          2000
% 7.08/1.49  --clause_weak_htbl                      true
% 7.08/1.49  --gc_record_bc_elim                     false
% 7.08/1.49  
% 7.08/1.49  ------ Preprocessing Options
% 7.08/1.49  
% 7.08/1.49  --preprocessing_flag                    true
% 7.08/1.49  --time_out_prep_mult                    0.1
% 7.08/1.49  --splitting_mode                        input
% 7.08/1.49  --splitting_grd                         true
% 7.08/1.49  --splitting_cvd                         false
% 7.08/1.49  --splitting_cvd_svl                     false
% 7.08/1.49  --splitting_nvd                         32
% 7.08/1.49  --sub_typing                            true
% 7.08/1.49  --prep_gs_sim                           true
% 7.08/1.49  --prep_unflatten                        true
% 7.08/1.49  --prep_res_sim                          true
% 7.08/1.49  --prep_upred                            true
% 7.08/1.49  --prep_sem_filter                       exhaustive
% 7.08/1.49  --prep_sem_filter_out                   false
% 7.08/1.49  --pred_elim                             true
% 7.08/1.49  --res_sim_input                         true
% 7.08/1.49  --eq_ax_congr_red                       true
% 7.08/1.49  --pure_diseq_elim                       true
% 7.08/1.49  --brand_transform                       false
% 7.08/1.49  --non_eq_to_eq                          false
% 7.08/1.49  --prep_def_merge                        true
% 7.08/1.49  --prep_def_merge_prop_impl              false
% 7.08/1.49  --prep_def_merge_mbd                    true
% 7.08/1.49  --prep_def_merge_tr_red                 false
% 7.08/1.49  --prep_def_merge_tr_cl                  false
% 7.08/1.49  --smt_preprocessing                     true
% 7.08/1.49  --smt_ac_axioms                         fast
% 7.08/1.49  --preprocessed_out                      false
% 7.08/1.49  --preprocessed_stats                    false
% 7.08/1.49  
% 7.08/1.49  ------ Abstraction refinement Options
% 7.08/1.49  
% 7.08/1.49  --abstr_ref                             []
% 7.08/1.49  --abstr_ref_prep                        false
% 7.08/1.49  --abstr_ref_until_sat                   false
% 7.08/1.49  --abstr_ref_sig_restrict                funpre
% 7.08/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.08/1.49  --abstr_ref_under                       []
% 7.08/1.49  
% 7.08/1.49  ------ SAT Options
% 7.08/1.49  
% 7.08/1.49  --sat_mode                              false
% 7.08/1.49  --sat_fm_restart_options                ""
% 7.08/1.49  --sat_gr_def                            false
% 7.08/1.49  --sat_epr_types                         true
% 7.08/1.49  --sat_non_cyclic_types                  false
% 7.08/1.49  --sat_finite_models                     false
% 7.08/1.49  --sat_fm_lemmas                         false
% 7.08/1.49  --sat_fm_prep                           false
% 7.08/1.49  --sat_fm_uc_incr                        true
% 7.08/1.49  --sat_out_model                         small
% 7.08/1.49  --sat_out_clauses                       false
% 7.08/1.49  
% 7.08/1.49  ------ QBF Options
% 7.08/1.49  
% 7.08/1.49  --qbf_mode                              false
% 7.08/1.49  --qbf_elim_univ                         false
% 7.08/1.49  --qbf_dom_inst                          none
% 7.08/1.49  --qbf_dom_pre_inst                      false
% 7.08/1.49  --qbf_sk_in                             false
% 7.08/1.49  --qbf_pred_elim                         true
% 7.08/1.49  --qbf_split                             512
% 7.08/1.49  
% 7.08/1.49  ------ BMC1 Options
% 7.08/1.49  
% 7.08/1.49  --bmc1_incremental                      false
% 7.08/1.49  --bmc1_axioms                           reachable_all
% 7.08/1.49  --bmc1_min_bound                        0
% 7.08/1.49  --bmc1_max_bound                        -1
% 7.08/1.49  --bmc1_max_bound_default                -1
% 7.08/1.49  --bmc1_symbol_reachability              true
% 7.08/1.49  --bmc1_property_lemmas                  false
% 7.08/1.49  --bmc1_k_induction                      false
% 7.08/1.49  --bmc1_non_equiv_states                 false
% 7.08/1.49  --bmc1_deadlock                         false
% 7.08/1.49  --bmc1_ucm                              false
% 7.08/1.49  --bmc1_add_unsat_core                   none
% 7.08/1.49  --bmc1_unsat_core_children              false
% 7.08/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.08/1.49  --bmc1_out_stat                         full
% 7.08/1.49  --bmc1_ground_init                      false
% 7.08/1.49  --bmc1_pre_inst_next_state              false
% 7.08/1.49  --bmc1_pre_inst_state                   false
% 7.08/1.49  --bmc1_pre_inst_reach_state             false
% 7.08/1.49  --bmc1_out_unsat_core                   false
% 7.08/1.49  --bmc1_aig_witness_out                  false
% 7.08/1.49  --bmc1_verbose                          false
% 7.08/1.49  --bmc1_dump_clauses_tptp                false
% 7.08/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.08/1.49  --bmc1_dump_file                        -
% 7.08/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.08/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.08/1.49  --bmc1_ucm_extend_mode                  1
% 7.08/1.49  --bmc1_ucm_init_mode                    2
% 7.08/1.49  --bmc1_ucm_cone_mode                    none
% 7.08/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.08/1.49  --bmc1_ucm_relax_model                  4
% 7.08/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.08/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.08/1.49  --bmc1_ucm_layered_model                none
% 7.08/1.49  --bmc1_ucm_max_lemma_size               10
% 7.08/1.49  
% 7.08/1.49  ------ AIG Options
% 7.08/1.49  
% 7.08/1.49  --aig_mode                              false
% 7.08/1.49  
% 7.08/1.49  ------ Instantiation Options
% 7.08/1.49  
% 7.08/1.49  --instantiation_flag                    true
% 7.08/1.49  --inst_sos_flag                         false
% 7.08/1.49  --inst_sos_phase                        true
% 7.08/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.08/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.08/1.49  --inst_lit_sel_side                     num_symb
% 7.08/1.49  --inst_solver_per_active                1400
% 7.08/1.49  --inst_solver_calls_frac                1.
% 7.08/1.49  --inst_passive_queue_type               priority_queues
% 7.08/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.08/1.49  --inst_passive_queues_freq              [25;2]
% 7.08/1.49  --inst_dismatching                      true
% 7.08/1.49  --inst_eager_unprocessed_to_passive     true
% 7.08/1.49  --inst_prop_sim_given                   true
% 7.08/1.49  --inst_prop_sim_new                     false
% 7.08/1.49  --inst_subs_new                         false
% 7.08/1.49  --inst_eq_res_simp                      false
% 7.08/1.49  --inst_subs_given                       false
% 7.08/1.49  --inst_orphan_elimination               true
% 7.08/1.49  --inst_learning_loop_flag               true
% 7.08/1.49  --inst_learning_start                   3000
% 7.08/1.49  --inst_learning_factor                  2
% 7.08/1.49  --inst_start_prop_sim_after_learn       3
% 7.08/1.49  --inst_sel_renew                        solver
% 7.08/1.49  --inst_lit_activity_flag                true
% 7.08/1.49  --inst_restr_to_given                   false
% 7.08/1.49  --inst_activity_threshold               500
% 7.08/1.49  --inst_out_proof                        true
% 7.08/1.49  
% 7.08/1.49  ------ Resolution Options
% 7.08/1.49  
% 7.08/1.49  --resolution_flag                       true
% 7.08/1.49  --res_lit_sel                           adaptive
% 7.08/1.49  --res_lit_sel_side                      none
% 7.08/1.49  --res_ordering                          kbo
% 7.08/1.49  --res_to_prop_solver                    active
% 7.08/1.49  --res_prop_simpl_new                    false
% 7.08/1.49  --res_prop_simpl_given                  true
% 7.08/1.49  --res_passive_queue_type                priority_queues
% 7.08/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.08/1.49  --res_passive_queues_freq               [15;5]
% 7.08/1.49  --res_forward_subs                      full
% 7.08/1.49  --res_backward_subs                     full
% 7.08/1.49  --res_forward_subs_resolution           true
% 7.08/1.49  --res_backward_subs_resolution          true
% 7.08/1.49  --res_orphan_elimination                true
% 7.08/1.49  --res_time_limit                        2.
% 7.08/1.49  --res_out_proof                         true
% 7.08/1.49  
% 7.08/1.49  ------ Superposition Options
% 7.08/1.49  
% 7.08/1.49  --superposition_flag                    true
% 7.08/1.49  --sup_passive_queue_type                priority_queues
% 7.08/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.08/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.08/1.49  --demod_completeness_check              fast
% 7.08/1.49  --demod_use_ground                      true
% 7.08/1.49  --sup_to_prop_solver                    passive
% 7.08/1.49  --sup_prop_simpl_new                    true
% 7.08/1.49  --sup_prop_simpl_given                  true
% 7.08/1.49  --sup_fun_splitting                     false
% 7.08/1.49  --sup_smt_interval                      50000
% 7.08/1.49  
% 7.08/1.49  ------ Superposition Simplification Setup
% 7.08/1.49  
% 7.08/1.49  --sup_indices_passive                   []
% 7.08/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.08/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.49  --sup_full_bw                           [BwDemod]
% 7.08/1.49  --sup_immed_triv                        [TrivRules]
% 7.08/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.08/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.49  --sup_immed_bw_main                     []
% 7.08/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.08/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.49  
% 7.08/1.49  ------ Combination Options
% 7.08/1.49  
% 7.08/1.49  --comb_res_mult                         3
% 7.08/1.49  --comb_sup_mult                         2
% 7.08/1.49  --comb_inst_mult                        10
% 7.08/1.49  
% 7.08/1.49  ------ Debug Options
% 7.08/1.49  
% 7.08/1.49  --dbg_backtrace                         false
% 7.08/1.49  --dbg_dump_prop_clauses                 false
% 7.08/1.49  --dbg_dump_prop_clauses_file            -
% 7.08/1.49  --dbg_out_stat                          false
% 7.08/1.49  ------ Parsing...
% 7.08/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.08/1.49  
% 7.08/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.08/1.49  
% 7.08/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.08/1.49  
% 7.08/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.08/1.49  ------ Proving...
% 7.08/1.49  ------ Problem Properties 
% 7.08/1.49  
% 7.08/1.49  
% 7.08/1.49  clauses                                 8
% 7.08/1.49  conjectures                             0
% 7.08/1.49  EPR                                     0
% 7.08/1.49  Horn                                    8
% 7.08/1.49  unary                                   8
% 7.08/1.49  binary                                  0
% 7.08/1.49  lits                                    8
% 7.08/1.49  lits eq                                 8
% 7.08/1.49  fd_pure                                 0
% 7.08/1.49  fd_pseudo                               0
% 7.08/1.49  fd_cond                                 0
% 7.08/1.49  fd_pseudo_cond                          0
% 7.08/1.49  AC symbols                              0
% 7.08/1.49  
% 7.08/1.49  ------ Schedule UEQ
% 7.08/1.49  
% 7.08/1.49  ------ pure equality problem: resolution off 
% 7.08/1.49  
% 7.08/1.49  ------ Option_UEQ Time Limit: Unbounded
% 7.08/1.49  
% 7.08/1.49  
% 7.08/1.49  ------ 
% 7.08/1.49  Current options:
% 7.08/1.49  ------ 
% 7.08/1.49  
% 7.08/1.49  ------ Input Options
% 7.08/1.49  
% 7.08/1.49  --out_options                           all
% 7.08/1.49  --tptp_safe_out                         true
% 7.08/1.49  --problem_path                          ""
% 7.08/1.49  --include_path                          ""
% 7.08/1.49  --clausifier                            res/vclausify_rel
% 7.08/1.49  --clausifier_options                    --mode clausify
% 7.08/1.49  --stdin                                 false
% 7.08/1.49  --stats_out                             all
% 7.08/1.49  
% 7.08/1.49  ------ General Options
% 7.08/1.49  
% 7.08/1.49  --fof                                   false
% 7.08/1.49  --time_out_real                         305.
% 7.08/1.49  --time_out_virtual                      -1.
% 7.08/1.49  --symbol_type_check                     false
% 7.08/1.49  --clausify_out                          false
% 7.08/1.49  --sig_cnt_out                           false
% 7.08/1.49  --trig_cnt_out                          false
% 7.08/1.49  --trig_cnt_out_tolerance                1.
% 7.08/1.49  --trig_cnt_out_sk_spl                   false
% 7.08/1.49  --abstr_cl_out                          false
% 7.08/1.49  
% 7.08/1.49  ------ Global Options
% 7.08/1.49  
% 7.08/1.49  --schedule                              default
% 7.08/1.49  --add_important_lit                     false
% 7.08/1.49  --prop_solver_per_cl                    1000
% 7.08/1.49  --min_unsat_core                        false
% 7.08/1.49  --soft_assumptions                      false
% 7.08/1.49  --soft_lemma_size                       3
% 7.08/1.49  --prop_impl_unit_size                   0
% 7.08/1.49  --prop_impl_unit                        []
% 7.08/1.49  --share_sel_clauses                     true
% 7.08/1.49  --reset_solvers                         false
% 7.08/1.49  --bc_imp_inh                            [conj_cone]
% 7.08/1.49  --conj_cone_tolerance                   3.
% 7.08/1.49  --extra_neg_conj                        none
% 7.08/1.49  --large_theory_mode                     true
% 7.08/1.49  --prolific_symb_bound                   200
% 7.08/1.49  --lt_threshold                          2000
% 7.08/1.49  --clause_weak_htbl                      true
% 7.08/1.49  --gc_record_bc_elim                     false
% 7.08/1.49  
% 7.08/1.49  ------ Preprocessing Options
% 7.08/1.49  
% 7.08/1.49  --preprocessing_flag                    true
% 7.08/1.49  --time_out_prep_mult                    0.1
% 7.08/1.49  --splitting_mode                        input
% 7.08/1.49  --splitting_grd                         true
% 7.08/1.49  --splitting_cvd                         false
% 7.08/1.49  --splitting_cvd_svl                     false
% 7.08/1.49  --splitting_nvd                         32
% 7.08/1.49  --sub_typing                            true
% 7.08/1.49  --prep_gs_sim                           true
% 7.08/1.49  --prep_unflatten                        true
% 7.08/1.49  --prep_res_sim                          true
% 7.08/1.49  --prep_upred                            true
% 7.08/1.49  --prep_sem_filter                       exhaustive
% 7.08/1.49  --prep_sem_filter_out                   false
% 7.08/1.49  --pred_elim                             true
% 7.08/1.49  --res_sim_input                         true
% 7.08/1.49  --eq_ax_congr_red                       true
% 7.08/1.49  --pure_diseq_elim                       true
% 7.08/1.49  --brand_transform                       false
% 7.08/1.49  --non_eq_to_eq                          false
% 7.08/1.49  --prep_def_merge                        true
% 7.08/1.49  --prep_def_merge_prop_impl              false
% 7.08/1.49  --prep_def_merge_mbd                    true
% 7.08/1.49  --prep_def_merge_tr_red                 false
% 7.08/1.49  --prep_def_merge_tr_cl                  false
% 7.08/1.49  --smt_preprocessing                     true
% 7.08/1.49  --smt_ac_axioms                         fast
% 7.08/1.49  --preprocessed_out                      false
% 7.08/1.49  --preprocessed_stats                    false
% 7.08/1.49  
% 7.08/1.49  ------ Abstraction refinement Options
% 7.08/1.49  
% 7.08/1.49  --abstr_ref                             []
% 7.08/1.49  --abstr_ref_prep                        false
% 7.08/1.49  --abstr_ref_until_sat                   false
% 7.08/1.49  --abstr_ref_sig_restrict                funpre
% 7.08/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.08/1.49  --abstr_ref_under                       []
% 7.08/1.49  
% 7.08/1.49  ------ SAT Options
% 7.08/1.49  
% 7.08/1.49  --sat_mode                              false
% 7.08/1.49  --sat_fm_restart_options                ""
% 7.08/1.49  --sat_gr_def                            false
% 7.08/1.49  --sat_epr_types                         true
% 7.08/1.49  --sat_non_cyclic_types                  false
% 7.08/1.49  --sat_finite_models                     false
% 7.08/1.49  --sat_fm_lemmas                         false
% 7.08/1.49  --sat_fm_prep                           false
% 7.08/1.49  --sat_fm_uc_incr                        true
% 7.08/1.49  --sat_out_model                         small
% 7.08/1.49  --sat_out_clauses                       false
% 7.08/1.49  
% 7.08/1.49  ------ QBF Options
% 7.08/1.49  
% 7.08/1.49  --qbf_mode                              false
% 7.08/1.49  --qbf_elim_univ                         false
% 7.08/1.49  --qbf_dom_inst                          none
% 7.08/1.49  --qbf_dom_pre_inst                      false
% 7.08/1.49  --qbf_sk_in                             false
% 7.08/1.49  --qbf_pred_elim                         true
% 7.08/1.49  --qbf_split                             512
% 7.08/1.49  
% 7.08/1.49  ------ BMC1 Options
% 7.08/1.49  
% 7.08/1.49  --bmc1_incremental                      false
% 7.08/1.49  --bmc1_axioms                           reachable_all
% 7.08/1.49  --bmc1_min_bound                        0
% 7.08/1.49  --bmc1_max_bound                        -1
% 7.08/1.49  --bmc1_max_bound_default                -1
% 7.08/1.49  --bmc1_symbol_reachability              true
% 7.08/1.49  --bmc1_property_lemmas                  false
% 7.08/1.49  --bmc1_k_induction                      false
% 7.08/1.49  --bmc1_non_equiv_states                 false
% 7.08/1.49  --bmc1_deadlock                         false
% 7.08/1.49  --bmc1_ucm                              false
% 7.08/1.49  --bmc1_add_unsat_core                   none
% 7.08/1.49  --bmc1_unsat_core_children              false
% 7.08/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.08/1.49  --bmc1_out_stat                         full
% 7.08/1.49  --bmc1_ground_init                      false
% 7.08/1.49  --bmc1_pre_inst_next_state              false
% 7.08/1.49  --bmc1_pre_inst_state                   false
% 7.08/1.49  --bmc1_pre_inst_reach_state             false
% 7.08/1.49  --bmc1_out_unsat_core                   false
% 7.08/1.49  --bmc1_aig_witness_out                  false
% 7.08/1.49  --bmc1_verbose                          false
% 7.08/1.49  --bmc1_dump_clauses_tptp                false
% 7.08/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.08/1.49  --bmc1_dump_file                        -
% 7.08/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.08/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.08/1.49  --bmc1_ucm_extend_mode                  1
% 7.08/1.49  --bmc1_ucm_init_mode                    2
% 7.08/1.49  --bmc1_ucm_cone_mode                    none
% 7.08/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.08/1.49  --bmc1_ucm_relax_model                  4
% 7.08/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.08/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.08/1.49  --bmc1_ucm_layered_model                none
% 7.08/1.49  --bmc1_ucm_max_lemma_size               10
% 7.08/1.49  
% 7.08/1.49  ------ AIG Options
% 7.08/1.49  
% 7.08/1.49  --aig_mode                              false
% 7.08/1.49  
% 7.08/1.49  ------ Instantiation Options
% 7.08/1.49  
% 7.08/1.49  --instantiation_flag                    false
% 7.08/1.49  --inst_sos_flag                         false
% 7.08/1.49  --inst_sos_phase                        true
% 7.08/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.08/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.08/1.49  --inst_lit_sel_side                     num_symb
% 7.08/1.49  --inst_solver_per_active                1400
% 7.08/1.49  --inst_solver_calls_frac                1.
% 7.08/1.49  --inst_passive_queue_type               priority_queues
% 7.08/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.08/1.49  --inst_passive_queues_freq              [25;2]
% 7.08/1.49  --inst_dismatching                      true
% 7.08/1.49  --inst_eager_unprocessed_to_passive     true
% 7.08/1.49  --inst_prop_sim_given                   true
% 7.08/1.49  --inst_prop_sim_new                     false
% 7.08/1.49  --inst_subs_new                         false
% 7.08/1.49  --inst_eq_res_simp                      false
% 7.08/1.49  --inst_subs_given                       false
% 7.08/1.49  --inst_orphan_elimination               true
% 7.08/1.49  --inst_learning_loop_flag               true
% 7.08/1.49  --inst_learning_start                   3000
% 7.08/1.49  --inst_learning_factor                  2
% 7.08/1.49  --inst_start_prop_sim_after_learn       3
% 7.08/1.49  --inst_sel_renew                        solver
% 7.08/1.49  --inst_lit_activity_flag                true
% 7.08/1.49  --inst_restr_to_given                   false
% 7.08/1.49  --inst_activity_threshold               500
% 7.08/1.49  --inst_out_proof                        true
% 7.08/1.49  
% 7.08/1.49  ------ Resolution Options
% 7.08/1.49  
% 7.08/1.49  --resolution_flag                       false
% 7.08/1.49  --res_lit_sel                           adaptive
% 7.08/1.49  --res_lit_sel_side                      none
% 7.08/1.49  --res_ordering                          kbo
% 7.08/1.49  --res_to_prop_solver                    active
% 7.08/1.49  --res_prop_simpl_new                    false
% 7.08/1.49  --res_prop_simpl_given                  true
% 7.08/1.49  --res_passive_queue_type                priority_queues
% 7.08/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.08/1.49  --res_passive_queues_freq               [15;5]
% 7.08/1.49  --res_forward_subs                      full
% 7.08/1.49  --res_backward_subs                     full
% 7.08/1.49  --res_forward_subs_resolution           true
% 7.08/1.49  --res_backward_subs_resolution          true
% 7.08/1.49  --res_orphan_elimination                true
% 7.08/1.49  --res_time_limit                        2.
% 7.08/1.49  --res_out_proof                         true
% 7.08/1.49  
% 7.08/1.49  ------ Superposition Options
% 7.08/1.49  
% 7.08/1.49  --superposition_flag                    true
% 7.08/1.49  --sup_passive_queue_type                priority_queues
% 7.08/1.49  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.08/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.08/1.49  --demod_completeness_check              fast
% 7.08/1.49  --demod_use_ground                      true
% 7.08/1.49  --sup_to_prop_solver                    active
% 7.08/1.49  --sup_prop_simpl_new                    false
% 7.08/1.49  --sup_prop_simpl_given                  false
% 7.08/1.49  --sup_fun_splitting                     true
% 7.08/1.49  --sup_smt_interval                      10000
% 7.08/1.49  
% 7.08/1.49  ------ Superposition Simplification Setup
% 7.08/1.49  
% 7.08/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.08/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.08/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.49  --sup_full_triv                         [TrivRules]
% 7.08/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.08/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.08/1.49  --sup_immed_triv                        [TrivRules]
% 7.08/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.08/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.08/1.49  --sup_immed_bw_main                     []
% 7.08/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.08/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.08/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.08/1.49  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.08/1.49  
% 7.08/1.49  ------ Combination Options
% 7.08/1.49  
% 7.08/1.49  --comb_res_mult                         1
% 7.08/1.49  --comb_sup_mult                         1
% 7.08/1.49  --comb_inst_mult                        1000000
% 7.08/1.49  
% 7.08/1.49  ------ Debug Options
% 7.08/1.49  
% 7.08/1.49  --dbg_backtrace                         false
% 7.08/1.49  --dbg_dump_prop_clauses                 false
% 7.08/1.49  --dbg_dump_prop_clauses_file            -
% 7.08/1.49  --dbg_out_stat                          false
% 7.08/1.49  
% 7.08/1.49  
% 7.08/1.49  
% 7.08/1.49  
% 7.08/1.49  ------ Proving...
% 7.08/1.49  
% 7.08/1.49  
% 7.08/1.49  % SZS status Theorem for theBenchmark.p
% 7.08/1.49  
% 7.08/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.08/1.49  
% 7.08/1.49  fof(f2,axiom,(
% 7.08/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.49  
% 7.08/1.49  fof(f13,plain,(
% 7.08/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.08/1.49    inference(nnf_transformation,[],[f2])).
% 7.08/1.49  
% 7.08/1.49  fof(f17,plain,(
% 7.08/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.08/1.49    inference(cnf_transformation,[],[f13])).
% 7.08/1.49  
% 7.08/1.49  fof(f5,axiom,(
% 7.08/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.49  
% 7.08/1.49  fof(f21,plain,(
% 7.08/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.08/1.49    inference(cnf_transformation,[],[f5])).
% 7.08/1.49  
% 7.08/1.49  fof(f29,plain,(
% 7.08/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.08/1.49    inference(definition_unfolding,[],[f17,f21])).
% 7.08/1.49  
% 7.08/1.49  fof(f8,conjecture,(
% 7.08/1.49    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 7.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.49  
% 7.08/1.49  fof(f9,negated_conjecture,(
% 7.08/1.49    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 7.08/1.49    inference(negated_conjecture,[],[f8])).
% 7.08/1.49  
% 7.08/1.49  fof(f12,plain,(
% 7.08/1.49    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 7.08/1.49    inference(ennf_transformation,[],[f9])).
% 7.08/1.49  
% 7.08/1.49  fof(f14,plain,(
% 7.08/1.49    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 7.08/1.49    introduced(choice_axiom,[])).
% 7.08/1.49  
% 7.08/1.49  fof(f15,plain,(
% 7.08/1.49    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 7.08/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 7.08/1.49  
% 7.08/1.49  fof(f26,plain,(
% 7.08/1.49    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 7.08/1.49    inference(cnf_transformation,[],[f15])).
% 7.08/1.49  
% 7.08/1.49  fof(f32,plain,(
% 7.08/1.49    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 7.08/1.49    inference(definition_unfolding,[],[f26,f21])).
% 7.08/1.49  
% 7.08/1.49  fof(f7,axiom,(
% 7.08/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.49  
% 7.08/1.49  fof(f23,plain,(
% 7.08/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.08/1.49    inference(cnf_transformation,[],[f7])).
% 7.08/1.49  
% 7.08/1.49  fof(f31,plain,(
% 7.08/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 7.08/1.49    inference(definition_unfolding,[],[f23,f21,f21,f21])).
% 7.08/1.49  
% 7.08/1.49  fof(f6,axiom,(
% 7.08/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.49  
% 7.08/1.49  fof(f22,plain,(
% 7.08/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.08/1.49    inference(cnf_transformation,[],[f6])).
% 7.08/1.49  
% 7.08/1.49  fof(f30,plain,(
% 7.08/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.08/1.49    inference(definition_unfolding,[],[f22,f21,f21])).
% 7.08/1.49  
% 7.08/1.49  fof(f4,axiom,(
% 7.08/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.49  
% 7.08/1.49  fof(f20,plain,(
% 7.08/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.08/1.49    inference(cnf_transformation,[],[f4])).
% 7.08/1.49  
% 7.08/1.49  fof(f1,axiom,(
% 7.08/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.49  
% 7.08/1.49  fof(f16,plain,(
% 7.08/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.08/1.49    inference(cnf_transformation,[],[f1])).
% 7.08/1.49  
% 7.08/1.49  fof(f27,plain,(
% 7.08/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.08/1.49    inference(definition_unfolding,[],[f16,f21,f21])).
% 7.08/1.49  
% 7.08/1.49  fof(f3,axiom,(
% 7.08/1.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.49  
% 7.08/1.49  fof(f10,plain,(
% 7.08/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 7.08/1.49    inference(unused_predicate_definition_removal,[],[f3])).
% 7.08/1.49  
% 7.08/1.49  fof(f11,plain,(
% 7.08/1.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 7.08/1.49    inference(ennf_transformation,[],[f10])).
% 7.08/1.49  
% 7.08/1.49  fof(f19,plain,(
% 7.08/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.08/1.49    inference(cnf_transformation,[],[f11])).
% 7.08/1.49  
% 7.08/1.49  fof(f25,plain,(
% 7.08/1.49    r1_tarski(sK0,sK2)),
% 7.08/1.49    inference(cnf_transformation,[],[f15])).
% 7.08/1.49  
% 7.08/1.49  fof(f18,plain,(
% 7.08/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.08/1.49    inference(cnf_transformation,[],[f13])).
% 7.08/1.49  
% 7.08/1.49  fof(f28,plain,(
% 7.08/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.08/1.49    inference(definition_unfolding,[],[f18,f21])).
% 7.08/1.49  
% 7.08/1.49  fof(f24,plain,(
% 7.08/1.49    ~r1_xboole_0(sK0,sK1)),
% 7.08/1.49    inference(cnf_transformation,[],[f15])).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2,plain,
% 7.08/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.08/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.08/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_53,plain,
% 7.08/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.08/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.08/1.49      inference(prop_impl,[status(thm)],[c_2]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_7,negated_conjecture,
% 7.08/1.49      ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 7.08/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_101,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.08/1.49      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
% 7.08/1.49      | sK0 != X0 ),
% 7.08/1.49      inference(resolution_lifted,[status(thm)],[c_53,c_7]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_102,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 7.08/1.49      inference(unflattening,[status(thm)],[c_101]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_6,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.08/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_184,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_102,c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_5,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.08/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_153,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_102,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_4,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.08/1.49      inference(cnf_transformation,[],[f20]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_168,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0))) = k4_xboole_0(sK0,X0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_153,c_4]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_233,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_184,c_168]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_234,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_233,c_4]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_265,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_102,c_234]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_288,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK0 ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_265,c_4]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_0,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.08/1.49      inference(cnf_transformation,[],[f27]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_161,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_165,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_161,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_14482,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_288,c_165]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_160,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_15014,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))))))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_165,c_160]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_15019,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_165,c_160]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_7540,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_6,c_160]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_143,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_7724,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_160,c_143]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_7750,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_7724,c_5,c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_8144,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_7540,c_7750]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_205,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_8145,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_8144,c_205]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_15045,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_15019,c_8145]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_15018,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X0))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_165,c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_15046,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_15018,c_15045]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_15050,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_15014,c_15045,c_15046]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_489,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_143,c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_7438,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_0,c_160]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_466,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_143,c_0]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_522,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_466,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_8317,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_7438,c_6,c_522]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_15051,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_15050,c_489,c_8317]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_16178,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_14482,c_15051]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3,plain,
% 7.08/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.08/1.49      inference(cnf_transformation,[],[f19]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_8,negated_conjecture,
% 7.08/1.49      ( r1_tarski(sK0,sK2) ),
% 7.08/1.49      inference(cnf_transformation,[],[f25]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_94,plain,
% 7.08/1.49      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK2 != X1 | sK0 != X0 ),
% 7.08/1.49      inference(resolution_lifted,[status(thm)],[c_3,c_8]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_95,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 7.08/1.49      inference(unflattening,[status(thm)],[c_94]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_271,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_102,c_234]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_283,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_271,c_102]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_284,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_283,c_4]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_16179,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_16178,c_95,c_284]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_150,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_429,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK2) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_95,c_143]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_540,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK2) = k4_xboole_0(X0,X0) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_429,c_4]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_702,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),sK2) = k4_xboole_0(X0,X0) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_0,c_540]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1249,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),X1)),sK2) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_702,c_143]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_465,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1),X3) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_143,c_143]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_523,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X3) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X3),X2))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_465,c_522]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_524,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))),X2) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_523,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1256,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1249,c_5,c_524]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1257,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_1256,c_95]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1258,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1257,c_5,c_150]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1322,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_95,c_1258]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_131,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_147,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_131,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1240,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0)))),sK2) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_147,c_702]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_176,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_102,c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_146,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_102,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_170,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_146,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_242,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_176,c_5,c_170]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_318,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,sK2) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_95,c_242]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_335,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,sK2) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_318,c_4]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_341,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)) = k4_xboole_0(sK2,sK2) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_335,c_131]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_410,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(sK2,sK2)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_341,c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_340,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK2))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_335,c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_342,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(sK2,sK2)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK2))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_340,c_341]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_411,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,sK0) = k4_xboole_0(sK2,sK2) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_341,c_131]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_412,plain,
% 7.08/1.49      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_411,c_284]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_544,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0))) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_410,c_342,c_412]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_545,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_544,c_4,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1272,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),sK2) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_1240,c_545]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_177,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_131,c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_263,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,X0) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_0,c_234]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_964,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_263,c_147]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_152,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_95,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_169,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_152,c_4]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_314,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_169,c_242]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_967,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(sK2,X0)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_314,c_147]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_339,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_335,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_343,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK2,sK2),X0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_339,c_341]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_344,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0))) = k4_xboole_0(k4_xboole_0(sK2,sK2),X0) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_343,c_314]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1059,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK2,sK2),X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(sK2,X0)) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_967,c_344]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1060,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1059,c_4,c_314,c_412]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1064,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_964,c_1060]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_312,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_0,c_242]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1065,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_1064,c_284,c_312]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1005,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_147,c_0]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1017,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),sK0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_147,c_312]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1031,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1005,c_1017]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_360,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_170,c_234]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_361,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_360,c_170]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_907,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_131,c_361]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1034,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_1031,c_907]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1066,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1065,c_1034]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1013,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X0))),sK2) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_147,c_540]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1014,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_147,c_131]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1024,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X0))),sK2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1013,c_1014]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1025,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),sK2) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_1024,c_907]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1067,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),sK2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1066,c_1025]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1273,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1272,c_177,c_1067]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1274,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_1273,c_1066]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1422,plain,
% 7.08/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_1322,c_4,c_1274]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1323,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,sK0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_288,c_1258]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_180,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_241,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_180,c_150]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1421,plain,
% 7.08/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X0,X0),sK0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1323,c_5,c_6,c_241]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1423,plain,
% 7.08/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k4_xboole_0(X0,X0),sK0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1422,c_1421]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_4550,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_150,c_1423]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_438,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_284,c_143]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_538,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK0) = k4_xboole_0(X0,X0) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_438,c_4]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1146,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK0) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_361,c_538]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_5025,plain,
% 7.08/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK0),sK0) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_4550,c_1146]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1317,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(sK0,sK0))) = k4_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_361,c_1258]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_969,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_361,c_147]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1056,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_969,c_284]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1057,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1056,c_4,c_150]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1426,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_1317,c_284,c_1057]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1427,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK0) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_1426,c_4,c_522,c_1146]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2819,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X1),X2) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_150,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_5026,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.08/1.49      inference(demodulation,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_5025,c_4,c_150,c_1427,c_2819]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_909,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK0))) = k4_xboole_0(k1_xboole_0,sK2) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_335,c_361]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_931,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,sK2) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_909,c_361]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_709,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,sK0),sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_4,c_540]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_777,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_709,c_284,c_335]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_778,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_777,c_4]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_932,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_931,c_335,c_778]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2802,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X0),sK2) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_932,c_150]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_197,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_95,c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_221,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_197,c_4,c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_376,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK2)) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_221,c_242]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_571,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK2)) ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_376,c_242]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1570,plain,
% 7.08/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK0))) = k4_xboole_0(k4_xboole_0(X0,X0),sK2) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_571,c_147]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1631,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X0),sK2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_1570,c_545]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2948,plain,
% 7.08/1.49      ( k4_xboole_0(k4_xboole_0(X0,X0),sK2) = k4_xboole_0(X0,X0) ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_2802,c_4,c_1631]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_5586,plain,
% 7.08/1.49      ( k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_xboole_0,sK2) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_5026,c_2948]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_5588,plain,
% 7.08/1.49      ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_5586,c_932]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_16180,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_16179,c_4,c_5588]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1,plain,
% 7.08/1.49      ( r1_xboole_0(X0,X1)
% 7.08/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.08/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_51,plain,
% 7.08/1.49      ( r1_xboole_0(X0,X1)
% 7.08/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.08/1.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_9,negated_conjecture,
% 7.08/1.49      ( ~ r1_xboole_0(sK0,sK1) ),
% 7.08/1.49      inference(cnf_transformation,[],[f24]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_106,plain,
% 7.08/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 7.08/1.49      | sK1 != X1
% 7.08/1.49      | sK0 != X0 ),
% 7.08/1.49      inference(resolution_lifted,[status(thm)],[c_51,c_9]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_107,plain,
% 7.08/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 7.08/1.49      inference(unflattening,[status(thm)],[c_106]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(contradiction,plain,
% 7.08/1.49      ( $false ),
% 7.08/1.49      inference(minisat,[status(thm)],[c_16180,c_107]) ).
% 7.08/1.49  
% 7.08/1.49  
% 7.08/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.08/1.49  
% 7.08/1.49  ------                               Statistics
% 7.08/1.49  
% 7.08/1.49  ------ General
% 7.08/1.49  
% 7.08/1.49  abstr_ref_over_cycles:                  0
% 7.08/1.49  abstr_ref_under_cycles:                 0
% 7.08/1.49  gc_basic_clause_elim:                   0
% 7.08/1.49  forced_gc_time:                         0
% 7.08/1.49  parsing_time:                           0.012
% 7.08/1.49  unif_index_cands_time:                  0.
% 7.08/1.49  unif_index_add_time:                    0.
% 7.08/1.49  orderings_time:                         0.
% 7.08/1.49  out_proof_time:                         0.009
% 7.08/1.49  total_time:                             0.783
% 7.08/1.49  num_of_symbols:                         38
% 7.08/1.49  num_of_terms:                           49052
% 7.08/1.49  
% 7.08/1.49  ------ Preprocessing
% 7.08/1.49  
% 7.08/1.49  num_of_splits:                          0
% 7.08/1.49  num_of_split_atoms:                     0
% 7.08/1.49  num_of_reused_defs:                     0
% 7.08/1.49  num_eq_ax_congr_red:                    0
% 7.08/1.49  num_of_sem_filtered_clauses:            0
% 7.08/1.49  num_of_subtypes:                        0
% 7.08/1.49  monotx_restored_types:                  0
% 7.08/1.49  sat_num_of_epr_types:                   0
% 7.08/1.49  sat_num_of_non_cyclic_types:            0
% 7.08/1.49  sat_guarded_non_collapsed_types:        0
% 7.08/1.49  num_pure_diseq_elim:                    0
% 7.08/1.49  simp_replaced_by:                       0
% 7.08/1.49  res_preprocessed:                       29
% 7.08/1.49  prep_upred:                             0
% 7.08/1.49  prep_unflattend:                        6
% 7.08/1.49  smt_new_axioms:                         0
% 7.08/1.49  pred_elim_cands:                        0
% 7.08/1.49  pred_elim:                              2
% 7.08/1.49  pred_elim_cl:                           2
% 7.08/1.49  pred_elim_cycles:                       3
% 7.08/1.49  merged_defs:                            2
% 7.08/1.49  merged_defs_ncl:                        0
% 7.08/1.49  bin_hyper_res:                          2
% 7.08/1.49  prep_cycles:                            3
% 7.08/1.49  pred_elim_time:                         0.001
% 7.08/1.49  splitting_time:                         0.
% 7.08/1.49  sem_filter_time:                        0.
% 7.08/1.49  monotx_time:                            0.
% 7.08/1.49  subtype_inf_time:                       0.
% 7.08/1.49  
% 7.08/1.49  ------ Problem properties
% 7.08/1.49  
% 7.08/1.49  clauses:                                8
% 7.08/1.49  conjectures:                            0
% 7.08/1.49  epr:                                    0
% 7.08/1.49  horn:                                   8
% 7.08/1.49  ground:                                 4
% 7.08/1.49  unary:                                  8
% 7.08/1.49  binary:                                 0
% 7.08/1.49  lits:                                   8
% 7.08/1.49  lits_eq:                                8
% 7.08/1.49  fd_pure:                                0
% 7.08/1.49  fd_pseudo:                              0
% 7.08/1.49  fd_cond:                                0
% 7.08/1.49  fd_pseudo_cond:                         0
% 7.08/1.49  ac_symbols:                             0
% 7.08/1.49  
% 7.08/1.49  ------ Propositional Solver
% 7.08/1.49  
% 7.08/1.49  prop_solver_calls:                      17
% 7.08/1.49  prop_fast_solver_calls:                 77
% 7.08/1.49  smt_solver_calls:                       0
% 7.08/1.49  smt_fast_solver_calls:                  0
% 7.08/1.49  prop_num_of_clauses:                    224
% 7.08/1.49  prop_preprocess_simplified:             413
% 7.08/1.49  prop_fo_subsumed:                       0
% 7.08/1.49  prop_solver_time:                       0.
% 7.08/1.49  smt_solver_time:                        0.
% 7.08/1.49  smt_fast_solver_time:                   0.
% 7.08/1.49  prop_fast_solver_time:                  0.
% 7.08/1.49  prop_unsat_core_time:                   0.
% 7.08/1.49  
% 7.08/1.49  ------ QBF
% 7.08/1.49  
% 7.08/1.49  qbf_q_res:                              0
% 7.08/1.49  qbf_num_tautologies:                    0
% 7.08/1.49  qbf_prep_cycles:                        0
% 7.08/1.49  
% 7.08/1.49  ------ BMC1
% 7.08/1.49  
% 7.08/1.49  bmc1_current_bound:                     -1
% 7.08/1.49  bmc1_last_solved_bound:                 -1
% 7.08/1.49  bmc1_unsat_core_size:                   -1
% 7.08/1.49  bmc1_unsat_core_parents_size:           -1
% 7.08/1.49  bmc1_merge_next_fun:                    0
% 7.08/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.08/1.50  
% 7.08/1.50  ------ Instantiation
% 7.08/1.50  
% 7.08/1.50  inst_num_of_clauses:                    0
% 7.08/1.50  inst_num_in_passive:                    0
% 7.08/1.50  inst_num_in_active:                     0
% 7.08/1.50  inst_num_in_unprocessed:                0
% 7.08/1.50  inst_num_of_loops:                      0
% 7.08/1.50  inst_num_of_learning_restarts:          0
% 7.08/1.50  inst_num_moves_active_passive:          0
% 7.08/1.50  inst_lit_activity:                      0
% 7.08/1.50  inst_lit_activity_moves:                0
% 7.08/1.50  inst_num_tautologies:                   0
% 7.08/1.50  inst_num_prop_implied:                  0
% 7.08/1.50  inst_num_existing_simplified:           0
% 7.08/1.50  inst_num_eq_res_simplified:             0
% 7.08/1.50  inst_num_child_elim:                    0
% 7.08/1.50  inst_num_of_dismatching_blockings:      0
% 7.08/1.50  inst_num_of_non_proper_insts:           0
% 7.08/1.50  inst_num_of_duplicates:                 0
% 7.08/1.50  inst_inst_num_from_inst_to_res:         0
% 7.08/1.50  inst_dismatching_checking_time:         0.
% 7.08/1.50  
% 7.08/1.50  ------ Resolution
% 7.08/1.50  
% 7.08/1.50  res_num_of_clauses:                     0
% 7.08/1.50  res_num_in_passive:                     0
% 7.08/1.50  res_num_in_active:                      0
% 7.08/1.50  res_num_of_loops:                       32
% 7.08/1.50  res_forward_subset_subsumed:            0
% 7.08/1.50  res_backward_subset_subsumed:           0
% 7.08/1.50  res_forward_subsumed:                   0
% 7.08/1.50  res_backward_subsumed:                  0
% 7.08/1.50  res_forward_subsumption_resolution:     0
% 7.08/1.50  res_backward_subsumption_resolution:    0
% 7.08/1.50  res_clause_to_clause_subsumption:       42905
% 7.08/1.50  res_orphan_elimination:                 0
% 7.08/1.50  res_tautology_del:                      5
% 7.08/1.50  res_num_eq_res_simplified:              1
% 7.08/1.50  res_num_sel_changes:                    0
% 7.08/1.50  res_moves_from_active_to_pass:          0
% 7.08/1.50  
% 7.08/1.50  ------ Superposition
% 7.08/1.50  
% 7.08/1.50  sup_time_total:                         0.
% 7.08/1.50  sup_time_generating:                    0.
% 7.08/1.50  sup_time_sim_full:                      0.
% 7.08/1.50  sup_time_sim_immed:                     0.
% 7.08/1.50  
% 7.08/1.50  sup_num_of_clauses:                     2074
% 7.08/1.50  sup_num_in_active:                      92
% 7.08/1.50  sup_num_in_passive:                     1982
% 7.08/1.50  sup_num_of_loops:                       116
% 7.08/1.50  sup_fw_superposition:                   4145
% 7.08/1.50  sup_bw_superposition:                   2549
% 7.08/1.50  sup_immediate_simplified:               6480
% 7.08/1.50  sup_given_eliminated:                   12
% 7.08/1.50  comparisons_done:                       0
% 7.08/1.50  comparisons_avoided:                    0
% 7.08/1.50  
% 7.08/1.50  ------ Simplifications
% 7.08/1.50  
% 7.08/1.50  
% 7.08/1.50  sim_fw_subset_subsumed:                 0
% 7.08/1.50  sim_bw_subset_subsumed:                 0
% 7.08/1.50  sim_fw_subsumed:                        385
% 7.08/1.50  sim_bw_subsumed:                        41
% 7.08/1.50  sim_fw_subsumption_res:                 0
% 7.08/1.50  sim_bw_subsumption_res:                 0
% 7.08/1.50  sim_tautology_del:                      0
% 7.08/1.50  sim_eq_tautology_del:                   1675
% 7.08/1.50  sim_eq_res_simp:                        0
% 7.08/1.50  sim_fw_demodulated:                     5202
% 7.08/1.50  sim_bw_demodulated:                     219
% 7.08/1.50  sim_light_normalised:                   3989
% 7.08/1.50  sim_joinable_taut:                      0
% 7.08/1.50  sim_joinable_simp:                      0
% 7.08/1.50  sim_ac_normalised:                      0
% 7.08/1.50  sim_smt_subsumption:                    0
% 7.08/1.50  
%------------------------------------------------------------------------------
