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
% DateTime   : Thu Dec  3 11:26:02 EST 2020

% Result     : Theorem 8.18s
% Output     : CNFRefutation 8.18s
% Verified   : 
% Statistics : Number of formulae       :   91 (2637 expanded)
%              Number of clauses        :   64 ( 877 expanded)
%              Number of leaves         :   10 ( 733 expanded)
%              Depth                    :   24
%              Number of atoms          :  119 (3308 expanded)
%              Number of equality atoms :   84 (2474 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f23,f22,f22])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f28,f22])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_69,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_130,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_69,c_10])).

cnf(c_131,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_130])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_586,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_131,c_5])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_597,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_586,c_4])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_333,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_587,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_333,c_5])).

cnf(c_596,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_587,c_4])).

cnf(c_709,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_597,c_596])).

cnf(c_6,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_331,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_589,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_331])).

cnf(c_712,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_597,c_589])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_329,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_899,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_712,c_329])).

cnf(c_1697,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_709,c_899])).

cnf(c_1723,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_1697,c_709])).

cnf(c_705,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_596,c_597])).

cnf(c_800,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_705,c_709])).

cnf(c_801,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_800,c_596,c_709])).

cnf(c_1044,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),X1))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_801,c_5])).

cnf(c_710,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_597,c_5])).

cnf(c_926,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,X0),X1)) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,X0),X1)) ),
    inference(superposition,[status(thm)],[c_710,c_596])).

cnf(c_934,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_926,c_710])).

cnf(c_1053,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_1044,c_5,c_926,c_934])).

cnf(c_1054,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_1053,c_709])).

cnf(c_1724,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_1723,c_596,c_1054])).

cnf(c_16649,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1724,c_5])).

cnf(c_469,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_333,c_331])).

cnf(c_793,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_469,c_329])).

cnf(c_16698,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16649,c_5,c_333,c_793])).

cnf(c_19797,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_16698,c_5])).

cnf(c_918,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_333,c_710])).

cnf(c_1015,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_918,c_4,c_333])).

cnf(c_1367,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_709,c_1015])).

cnf(c_1649,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_596,c_1367])).

cnf(c_681,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_596,c_5])).

cnf(c_685,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_681,c_5])).

cnf(c_686,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_685,c_5])).

cnf(c_17598,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0))))))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0))))) ),
    inference(superposition,[status(thm)],[c_1649,c_686])).

cnf(c_18803,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0))))))) = k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_17598,c_1649])).

cnf(c_890,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_712])).

cnf(c_1125,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_890,c_329])).

cnf(c_18804,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),sK1)) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_18803,c_4,c_333,c_1125])).

cnf(c_19277,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_18804,c_5])).

cnf(c_20141,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19797,c_5,c_793,c_19277])).

cnf(c_24763,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20141,c_20141])).

cnf(c_24913,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24763,c_4,c_793,c_1054])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_67,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_125,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_67,c_9])).

cnf(c_126,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_125])).

cnf(c_376,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_126,c_5])).

cnf(c_26634,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24913,c_376])).

cnf(c_198,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_205,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26634,c_205])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.18/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.18/1.50  
% 8.18/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.18/1.50  
% 8.18/1.50  ------  iProver source info
% 8.18/1.50  
% 8.18/1.50  git: date: 2020-06-30 10:37:57 +0100
% 8.18/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.18/1.50  git: non_committed_changes: false
% 8.18/1.50  git: last_make_outside_of_git: false
% 8.18/1.50  
% 8.18/1.50  ------ 
% 8.18/1.50  
% 8.18/1.50  ------ Input Options
% 8.18/1.50  
% 8.18/1.50  --out_options                           all
% 8.18/1.50  --tptp_safe_out                         true
% 8.18/1.50  --problem_path                          ""
% 8.18/1.50  --include_path                          ""
% 8.18/1.50  --clausifier                            res/vclausify_rel
% 8.18/1.50  --clausifier_options                    ""
% 8.18/1.50  --stdin                                 false
% 8.18/1.50  --stats_out                             all
% 8.18/1.50  
% 8.18/1.50  ------ General Options
% 8.18/1.50  
% 8.18/1.50  --fof                                   false
% 8.18/1.50  --time_out_real                         305.
% 8.18/1.50  --time_out_virtual                      -1.
% 8.18/1.50  --symbol_type_check                     false
% 8.18/1.50  --clausify_out                          false
% 8.18/1.50  --sig_cnt_out                           false
% 8.18/1.50  --trig_cnt_out                          false
% 8.18/1.50  --trig_cnt_out_tolerance                1.
% 8.18/1.50  --trig_cnt_out_sk_spl                   false
% 8.18/1.50  --abstr_cl_out                          false
% 8.18/1.50  
% 8.18/1.50  ------ Global Options
% 8.18/1.50  
% 8.18/1.50  --schedule                              default
% 8.18/1.50  --add_important_lit                     false
% 8.18/1.50  --prop_solver_per_cl                    1000
% 8.18/1.50  --min_unsat_core                        false
% 8.18/1.50  --soft_assumptions                      false
% 8.18/1.50  --soft_lemma_size                       3
% 8.18/1.50  --prop_impl_unit_size                   0
% 8.18/1.50  --prop_impl_unit                        []
% 8.18/1.50  --share_sel_clauses                     true
% 8.18/1.50  --reset_solvers                         false
% 8.18/1.50  --bc_imp_inh                            [conj_cone]
% 8.18/1.50  --conj_cone_tolerance                   3.
% 8.18/1.50  --extra_neg_conj                        none
% 8.18/1.50  --large_theory_mode                     true
% 8.18/1.50  --prolific_symb_bound                   200
% 8.18/1.50  --lt_threshold                          2000
% 8.18/1.50  --clause_weak_htbl                      true
% 8.18/1.50  --gc_record_bc_elim                     false
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing Options
% 8.18/1.50  
% 8.18/1.50  --preprocessing_flag                    true
% 8.18/1.50  --time_out_prep_mult                    0.1
% 8.18/1.50  --splitting_mode                        input
% 8.18/1.50  --splitting_grd                         true
% 8.18/1.50  --splitting_cvd                         false
% 8.18/1.50  --splitting_cvd_svl                     false
% 8.18/1.50  --splitting_nvd                         32
% 8.18/1.50  --sub_typing                            true
% 8.18/1.50  --prep_gs_sim                           true
% 8.18/1.50  --prep_unflatten                        true
% 8.18/1.50  --prep_res_sim                          true
% 8.18/1.50  --prep_upred                            true
% 8.18/1.50  --prep_sem_filter                       exhaustive
% 8.18/1.50  --prep_sem_filter_out                   false
% 8.18/1.50  --pred_elim                             true
% 8.18/1.50  --res_sim_input                         true
% 8.18/1.50  --eq_ax_congr_red                       true
% 8.18/1.50  --pure_diseq_elim                       true
% 8.18/1.50  --brand_transform                       false
% 8.18/1.50  --non_eq_to_eq                          false
% 8.18/1.50  --prep_def_merge                        true
% 8.18/1.50  --prep_def_merge_prop_impl              false
% 8.18/1.50  --prep_def_merge_mbd                    true
% 8.18/1.50  --prep_def_merge_tr_red                 false
% 8.18/1.50  --prep_def_merge_tr_cl                  false
% 8.18/1.50  --smt_preprocessing                     true
% 8.18/1.50  --smt_ac_axioms                         fast
% 8.18/1.50  --preprocessed_out                      false
% 8.18/1.50  --preprocessed_stats                    false
% 8.18/1.50  
% 8.18/1.50  ------ Abstraction refinement Options
% 8.18/1.50  
% 8.18/1.50  --abstr_ref                             []
% 8.18/1.50  --abstr_ref_prep                        false
% 8.18/1.50  --abstr_ref_until_sat                   false
% 8.18/1.50  --abstr_ref_sig_restrict                funpre
% 8.18/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.18/1.50  --abstr_ref_under                       []
% 8.18/1.50  
% 8.18/1.50  ------ SAT Options
% 8.18/1.50  
% 8.18/1.50  --sat_mode                              false
% 8.18/1.50  --sat_fm_restart_options                ""
% 8.18/1.50  --sat_gr_def                            false
% 8.18/1.50  --sat_epr_types                         true
% 8.18/1.50  --sat_non_cyclic_types                  false
% 8.18/1.50  --sat_finite_models                     false
% 8.18/1.50  --sat_fm_lemmas                         false
% 8.18/1.50  --sat_fm_prep                           false
% 8.18/1.50  --sat_fm_uc_incr                        true
% 8.18/1.50  --sat_out_model                         small
% 8.18/1.50  --sat_out_clauses                       false
% 8.18/1.50  
% 8.18/1.50  ------ QBF Options
% 8.18/1.50  
% 8.18/1.50  --qbf_mode                              false
% 8.18/1.50  --qbf_elim_univ                         false
% 8.18/1.50  --qbf_dom_inst                          none
% 8.18/1.50  --qbf_dom_pre_inst                      false
% 8.18/1.50  --qbf_sk_in                             false
% 8.18/1.50  --qbf_pred_elim                         true
% 8.18/1.50  --qbf_split                             512
% 8.18/1.50  
% 8.18/1.50  ------ BMC1 Options
% 8.18/1.50  
% 8.18/1.50  --bmc1_incremental                      false
% 8.18/1.50  --bmc1_axioms                           reachable_all
% 8.18/1.50  --bmc1_min_bound                        0
% 8.18/1.50  --bmc1_max_bound                        -1
% 8.18/1.50  --bmc1_max_bound_default                -1
% 8.18/1.50  --bmc1_symbol_reachability              true
% 8.18/1.50  --bmc1_property_lemmas                  false
% 8.18/1.50  --bmc1_k_induction                      false
% 8.18/1.50  --bmc1_non_equiv_states                 false
% 8.18/1.50  --bmc1_deadlock                         false
% 8.18/1.50  --bmc1_ucm                              false
% 8.18/1.50  --bmc1_add_unsat_core                   none
% 8.18/1.50  --bmc1_unsat_core_children              false
% 8.18/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.18/1.50  --bmc1_out_stat                         full
% 8.18/1.50  --bmc1_ground_init                      false
% 8.18/1.50  --bmc1_pre_inst_next_state              false
% 8.18/1.50  --bmc1_pre_inst_state                   false
% 8.18/1.50  --bmc1_pre_inst_reach_state             false
% 8.18/1.50  --bmc1_out_unsat_core                   false
% 8.18/1.50  --bmc1_aig_witness_out                  false
% 8.18/1.50  --bmc1_verbose                          false
% 8.18/1.50  --bmc1_dump_clauses_tptp                false
% 8.18/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.18/1.50  --bmc1_dump_file                        -
% 8.18/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.18/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.18/1.50  --bmc1_ucm_extend_mode                  1
% 8.18/1.50  --bmc1_ucm_init_mode                    2
% 8.18/1.50  --bmc1_ucm_cone_mode                    none
% 8.18/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.18/1.50  --bmc1_ucm_relax_model                  4
% 8.18/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.18/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.18/1.50  --bmc1_ucm_layered_model                none
% 8.18/1.50  --bmc1_ucm_max_lemma_size               10
% 8.18/1.50  
% 8.18/1.50  ------ AIG Options
% 8.18/1.50  
% 8.18/1.50  --aig_mode                              false
% 8.18/1.50  
% 8.18/1.50  ------ Instantiation Options
% 8.18/1.50  
% 8.18/1.50  --instantiation_flag                    true
% 8.18/1.50  --inst_sos_flag                         true
% 8.18/1.50  --inst_sos_phase                        true
% 8.18/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.18/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.18/1.50  --inst_lit_sel_side                     num_symb
% 8.18/1.50  --inst_solver_per_active                1400
% 8.18/1.50  --inst_solver_calls_frac                1.
% 8.18/1.50  --inst_passive_queue_type               priority_queues
% 8.18/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.18/1.50  --inst_passive_queues_freq              [25;2]
% 8.18/1.50  --inst_dismatching                      true
% 8.18/1.50  --inst_eager_unprocessed_to_passive     true
% 8.18/1.50  --inst_prop_sim_given                   true
% 8.18/1.50  --inst_prop_sim_new                     false
% 8.18/1.50  --inst_subs_new                         false
% 8.18/1.50  --inst_eq_res_simp                      false
% 8.18/1.50  --inst_subs_given                       false
% 8.18/1.50  --inst_orphan_elimination               true
% 8.18/1.50  --inst_learning_loop_flag               true
% 8.18/1.50  --inst_learning_start                   3000
% 8.18/1.50  --inst_learning_factor                  2
% 8.18/1.50  --inst_start_prop_sim_after_learn       3
% 8.18/1.50  --inst_sel_renew                        solver
% 8.18/1.50  --inst_lit_activity_flag                true
% 8.18/1.50  --inst_restr_to_given                   false
% 8.18/1.50  --inst_activity_threshold               500
% 8.18/1.50  --inst_out_proof                        true
% 8.18/1.50  
% 8.18/1.50  ------ Resolution Options
% 8.18/1.50  
% 8.18/1.50  --resolution_flag                       true
% 8.18/1.50  --res_lit_sel                           adaptive
% 8.18/1.50  --res_lit_sel_side                      none
% 8.18/1.50  --res_ordering                          kbo
% 8.18/1.50  --res_to_prop_solver                    active
% 8.18/1.50  --res_prop_simpl_new                    false
% 8.18/1.50  --res_prop_simpl_given                  true
% 8.18/1.50  --res_passive_queue_type                priority_queues
% 8.18/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.18/1.50  --res_passive_queues_freq               [15;5]
% 8.18/1.50  --res_forward_subs                      full
% 8.18/1.50  --res_backward_subs                     full
% 8.18/1.50  --res_forward_subs_resolution           true
% 8.18/1.50  --res_backward_subs_resolution          true
% 8.18/1.50  --res_orphan_elimination                true
% 8.18/1.50  --res_time_limit                        2.
% 8.18/1.50  --res_out_proof                         true
% 8.18/1.50  
% 8.18/1.50  ------ Superposition Options
% 8.18/1.50  
% 8.18/1.50  --superposition_flag                    true
% 8.18/1.50  --sup_passive_queue_type                priority_queues
% 8.18/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.18/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.18/1.50  --demod_completeness_check              fast
% 8.18/1.50  --demod_use_ground                      true
% 8.18/1.50  --sup_to_prop_solver                    passive
% 8.18/1.50  --sup_prop_simpl_new                    true
% 8.18/1.50  --sup_prop_simpl_given                  true
% 8.18/1.50  --sup_fun_splitting                     true
% 8.18/1.50  --sup_smt_interval                      50000
% 8.18/1.50  
% 8.18/1.50  ------ Superposition Simplification Setup
% 8.18/1.50  
% 8.18/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.18/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.18/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.18/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.18/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.18/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.18/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.18/1.50  --sup_immed_triv                        [TrivRules]
% 8.18/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_immed_bw_main                     []
% 8.18/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.18/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.18/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_input_bw                          []
% 8.18/1.50  
% 8.18/1.50  ------ Combination Options
% 8.18/1.50  
% 8.18/1.50  --comb_res_mult                         3
% 8.18/1.50  --comb_sup_mult                         2
% 8.18/1.50  --comb_inst_mult                        10
% 8.18/1.50  
% 8.18/1.50  ------ Debug Options
% 8.18/1.50  
% 8.18/1.50  --dbg_backtrace                         false
% 8.18/1.50  --dbg_dump_prop_clauses                 false
% 8.18/1.50  --dbg_dump_prop_clauses_file            -
% 8.18/1.50  --dbg_out_stat                          false
% 8.18/1.50  ------ Parsing...
% 8.18/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.18/1.50  ------ Proving...
% 8.18/1.50  ------ Problem Properties 
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  clauses                                 10
% 8.18/1.50  conjectures                             0
% 8.18/1.50  EPR                                     1
% 8.18/1.50  Horn                                    10
% 8.18/1.50  unary                                   7
% 8.18/1.50  binary                                  3
% 8.18/1.50  lits                                    13
% 8.18/1.50  lits eq                                 8
% 8.18/1.50  fd_pure                                 0
% 8.18/1.50  fd_pseudo                               0
% 8.18/1.50  fd_cond                                 0
% 8.18/1.50  fd_pseudo_cond                          0
% 8.18/1.50  AC symbols                              0
% 8.18/1.50  
% 8.18/1.50  ------ Schedule dynamic 5 is on 
% 8.18/1.50  
% 8.18/1.50  ------ no conjectures: strip conj schedule 
% 8.18/1.50  
% 8.18/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  ------ 
% 8.18/1.50  Current options:
% 8.18/1.50  ------ 
% 8.18/1.50  
% 8.18/1.50  ------ Input Options
% 8.18/1.50  
% 8.18/1.50  --out_options                           all
% 8.18/1.50  --tptp_safe_out                         true
% 8.18/1.50  --problem_path                          ""
% 8.18/1.50  --include_path                          ""
% 8.18/1.50  --clausifier                            res/vclausify_rel
% 8.18/1.50  --clausifier_options                    ""
% 8.18/1.50  --stdin                                 false
% 8.18/1.50  --stats_out                             all
% 8.18/1.50  
% 8.18/1.50  ------ General Options
% 8.18/1.50  
% 8.18/1.50  --fof                                   false
% 8.18/1.50  --time_out_real                         305.
% 8.18/1.50  --time_out_virtual                      -1.
% 8.18/1.50  --symbol_type_check                     false
% 8.18/1.50  --clausify_out                          false
% 8.18/1.50  --sig_cnt_out                           false
% 8.18/1.50  --trig_cnt_out                          false
% 8.18/1.50  --trig_cnt_out_tolerance                1.
% 8.18/1.50  --trig_cnt_out_sk_spl                   false
% 8.18/1.50  --abstr_cl_out                          false
% 8.18/1.50  
% 8.18/1.50  ------ Global Options
% 8.18/1.50  
% 8.18/1.50  --schedule                              default
% 8.18/1.50  --add_important_lit                     false
% 8.18/1.50  --prop_solver_per_cl                    1000
% 8.18/1.50  --min_unsat_core                        false
% 8.18/1.50  --soft_assumptions                      false
% 8.18/1.50  --soft_lemma_size                       3
% 8.18/1.50  --prop_impl_unit_size                   0
% 8.18/1.50  --prop_impl_unit                        []
% 8.18/1.50  --share_sel_clauses                     true
% 8.18/1.50  --reset_solvers                         false
% 8.18/1.50  --bc_imp_inh                            [conj_cone]
% 8.18/1.50  --conj_cone_tolerance                   3.
% 8.18/1.50  --extra_neg_conj                        none
% 8.18/1.50  --large_theory_mode                     true
% 8.18/1.50  --prolific_symb_bound                   200
% 8.18/1.50  --lt_threshold                          2000
% 8.18/1.50  --clause_weak_htbl                      true
% 8.18/1.50  --gc_record_bc_elim                     false
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing Options
% 8.18/1.50  
% 8.18/1.50  --preprocessing_flag                    true
% 8.18/1.50  --time_out_prep_mult                    0.1
% 8.18/1.50  --splitting_mode                        input
% 8.18/1.50  --splitting_grd                         true
% 8.18/1.50  --splitting_cvd                         false
% 8.18/1.50  --splitting_cvd_svl                     false
% 8.18/1.50  --splitting_nvd                         32
% 8.18/1.50  --sub_typing                            true
% 8.18/1.50  --prep_gs_sim                           true
% 8.18/1.50  --prep_unflatten                        true
% 8.18/1.50  --prep_res_sim                          true
% 8.18/1.50  --prep_upred                            true
% 8.18/1.50  --prep_sem_filter                       exhaustive
% 8.18/1.50  --prep_sem_filter_out                   false
% 8.18/1.50  --pred_elim                             true
% 8.18/1.50  --res_sim_input                         true
% 8.18/1.50  --eq_ax_congr_red                       true
% 8.18/1.50  --pure_diseq_elim                       true
% 8.18/1.50  --brand_transform                       false
% 8.18/1.50  --non_eq_to_eq                          false
% 8.18/1.50  --prep_def_merge                        true
% 8.18/1.50  --prep_def_merge_prop_impl              false
% 8.18/1.50  --prep_def_merge_mbd                    true
% 8.18/1.50  --prep_def_merge_tr_red                 false
% 8.18/1.50  --prep_def_merge_tr_cl                  false
% 8.18/1.50  --smt_preprocessing                     true
% 8.18/1.50  --smt_ac_axioms                         fast
% 8.18/1.50  --preprocessed_out                      false
% 8.18/1.50  --preprocessed_stats                    false
% 8.18/1.50  
% 8.18/1.50  ------ Abstraction refinement Options
% 8.18/1.50  
% 8.18/1.50  --abstr_ref                             []
% 8.18/1.50  --abstr_ref_prep                        false
% 8.18/1.50  --abstr_ref_until_sat                   false
% 8.18/1.50  --abstr_ref_sig_restrict                funpre
% 8.18/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.18/1.50  --abstr_ref_under                       []
% 8.18/1.50  
% 8.18/1.50  ------ SAT Options
% 8.18/1.50  
% 8.18/1.50  --sat_mode                              false
% 8.18/1.50  --sat_fm_restart_options                ""
% 8.18/1.50  --sat_gr_def                            false
% 8.18/1.50  --sat_epr_types                         true
% 8.18/1.50  --sat_non_cyclic_types                  false
% 8.18/1.50  --sat_finite_models                     false
% 8.18/1.50  --sat_fm_lemmas                         false
% 8.18/1.50  --sat_fm_prep                           false
% 8.18/1.50  --sat_fm_uc_incr                        true
% 8.18/1.50  --sat_out_model                         small
% 8.18/1.50  --sat_out_clauses                       false
% 8.18/1.50  
% 8.18/1.50  ------ QBF Options
% 8.18/1.50  
% 8.18/1.50  --qbf_mode                              false
% 8.18/1.50  --qbf_elim_univ                         false
% 8.18/1.50  --qbf_dom_inst                          none
% 8.18/1.50  --qbf_dom_pre_inst                      false
% 8.18/1.50  --qbf_sk_in                             false
% 8.18/1.50  --qbf_pred_elim                         true
% 8.18/1.50  --qbf_split                             512
% 8.18/1.50  
% 8.18/1.50  ------ BMC1 Options
% 8.18/1.50  
% 8.18/1.50  --bmc1_incremental                      false
% 8.18/1.50  --bmc1_axioms                           reachable_all
% 8.18/1.50  --bmc1_min_bound                        0
% 8.18/1.50  --bmc1_max_bound                        -1
% 8.18/1.50  --bmc1_max_bound_default                -1
% 8.18/1.50  --bmc1_symbol_reachability              true
% 8.18/1.50  --bmc1_property_lemmas                  false
% 8.18/1.50  --bmc1_k_induction                      false
% 8.18/1.50  --bmc1_non_equiv_states                 false
% 8.18/1.50  --bmc1_deadlock                         false
% 8.18/1.50  --bmc1_ucm                              false
% 8.18/1.50  --bmc1_add_unsat_core                   none
% 8.18/1.50  --bmc1_unsat_core_children              false
% 8.18/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.18/1.50  --bmc1_out_stat                         full
% 8.18/1.50  --bmc1_ground_init                      false
% 8.18/1.50  --bmc1_pre_inst_next_state              false
% 8.18/1.50  --bmc1_pre_inst_state                   false
% 8.18/1.50  --bmc1_pre_inst_reach_state             false
% 8.18/1.50  --bmc1_out_unsat_core                   false
% 8.18/1.50  --bmc1_aig_witness_out                  false
% 8.18/1.50  --bmc1_verbose                          false
% 8.18/1.50  --bmc1_dump_clauses_tptp                false
% 8.18/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.18/1.50  --bmc1_dump_file                        -
% 8.18/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.18/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.18/1.50  --bmc1_ucm_extend_mode                  1
% 8.18/1.50  --bmc1_ucm_init_mode                    2
% 8.18/1.50  --bmc1_ucm_cone_mode                    none
% 8.18/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.18/1.50  --bmc1_ucm_relax_model                  4
% 8.18/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.18/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.18/1.50  --bmc1_ucm_layered_model                none
% 8.18/1.50  --bmc1_ucm_max_lemma_size               10
% 8.18/1.50  
% 8.18/1.50  ------ AIG Options
% 8.18/1.50  
% 8.18/1.50  --aig_mode                              false
% 8.18/1.50  
% 8.18/1.50  ------ Instantiation Options
% 8.18/1.50  
% 8.18/1.50  --instantiation_flag                    true
% 8.18/1.50  --inst_sos_flag                         true
% 8.18/1.50  --inst_sos_phase                        true
% 8.18/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.18/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.18/1.50  --inst_lit_sel_side                     none
% 8.18/1.50  --inst_solver_per_active                1400
% 8.18/1.50  --inst_solver_calls_frac                1.
% 8.18/1.50  --inst_passive_queue_type               priority_queues
% 8.18/1.50  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 8.18/1.50  --inst_passive_queues_freq              [25;2]
% 8.18/1.50  --inst_dismatching                      true
% 8.18/1.50  --inst_eager_unprocessed_to_passive     true
% 8.18/1.50  --inst_prop_sim_given                   true
% 8.18/1.50  --inst_prop_sim_new                     false
% 8.18/1.50  --inst_subs_new                         false
% 8.18/1.50  --inst_eq_res_simp                      false
% 8.18/1.50  --inst_subs_given                       false
% 8.18/1.50  --inst_orphan_elimination               true
% 8.18/1.50  --inst_learning_loop_flag               true
% 8.18/1.50  --inst_learning_start                   3000
% 8.18/1.50  --inst_learning_factor                  2
% 8.18/1.50  --inst_start_prop_sim_after_learn       3
% 8.18/1.50  --inst_sel_renew                        solver
% 8.18/1.50  --inst_lit_activity_flag                true
% 8.18/1.50  --inst_restr_to_given                   false
% 8.18/1.50  --inst_activity_threshold               500
% 8.18/1.50  --inst_out_proof                        true
% 8.18/1.50  
% 8.18/1.50  ------ Resolution Options
% 8.18/1.50  
% 8.18/1.50  --resolution_flag                       false
% 8.18/1.50  --res_lit_sel                           adaptive
% 8.18/1.50  --res_lit_sel_side                      none
% 8.18/1.50  --res_ordering                          kbo
% 8.18/1.50  --res_to_prop_solver                    active
% 8.18/1.50  --res_prop_simpl_new                    false
% 8.18/1.50  --res_prop_simpl_given                  true
% 8.18/1.50  --res_passive_queue_type                priority_queues
% 8.18/1.50  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 8.18/1.50  --res_passive_queues_freq               [15;5]
% 8.18/1.50  --res_forward_subs                      full
% 8.18/1.50  --res_backward_subs                     full
% 8.18/1.50  --res_forward_subs_resolution           true
% 8.18/1.50  --res_backward_subs_resolution          true
% 8.18/1.50  --res_orphan_elimination                true
% 8.18/1.50  --res_time_limit                        2.
% 8.18/1.50  --res_out_proof                         true
% 8.18/1.50  
% 8.18/1.50  ------ Superposition Options
% 8.18/1.50  
% 8.18/1.50  --superposition_flag                    true
% 8.18/1.50  --sup_passive_queue_type                priority_queues
% 8.18/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.18/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.18/1.50  --demod_completeness_check              fast
% 8.18/1.50  --demod_use_ground                      true
% 8.18/1.50  --sup_to_prop_solver                    passive
% 8.18/1.50  --sup_prop_simpl_new                    true
% 8.18/1.50  --sup_prop_simpl_given                  true
% 8.18/1.50  --sup_fun_splitting                     true
% 8.18/1.50  --sup_smt_interval                      50000
% 8.18/1.50  
% 8.18/1.50  ------ Superposition Simplification Setup
% 8.18/1.50  
% 8.18/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.18/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.18/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.18/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.18/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.18/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.18/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.18/1.50  --sup_immed_triv                        [TrivRules]
% 8.18/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_immed_bw_main                     []
% 8.18/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.18/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.18/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_input_bw                          []
% 8.18/1.50  
% 8.18/1.50  ------ Combination Options
% 8.18/1.50  
% 8.18/1.50  --comb_res_mult                         3
% 8.18/1.50  --comb_sup_mult                         2
% 8.18/1.50  --comb_inst_mult                        10
% 8.18/1.50  
% 8.18/1.50  ------ Debug Options
% 8.18/1.50  
% 8.18/1.50  --dbg_backtrace                         false
% 8.18/1.50  --dbg_dump_prop_clauses                 false
% 8.18/1.50  --dbg_dump_prop_clauses_file            -
% 8.18/1.50  --dbg_out_stat                          false
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  ------ Proving...
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  % SZS status Theorem for theBenchmark.p
% 8.18/1.50  
% 8.18/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 8.18/1.50  
% 8.18/1.50  fof(f2,axiom,(
% 8.18/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f13,plain,(
% 8.18/1.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 8.18/1.50    inference(nnf_transformation,[],[f2])).
% 8.18/1.50  
% 8.18/1.50  fof(f19,plain,(
% 8.18/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f13])).
% 8.18/1.50  
% 8.18/1.50  fof(f9,conjecture,(
% 8.18/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f10,negated_conjecture,(
% 8.18/1.50    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 8.18/1.50    inference(negated_conjecture,[],[f9])).
% 8.18/1.50  
% 8.18/1.50  fof(f12,plain,(
% 8.18/1.50    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 8.18/1.50    inference(ennf_transformation,[],[f10])).
% 8.18/1.50  
% 8.18/1.50  fof(f15,plain,(
% 8.18/1.50    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 8.18/1.50    introduced(choice_axiom,[])).
% 8.18/1.50  
% 8.18/1.50  fof(f16,plain,(
% 8.18/1.50    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 8.18/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 8.18/1.50  
% 8.18/1.50  fof(f27,plain,(
% 8.18/1.50    r1_tarski(sK0,sK1)),
% 8.18/1.50    inference(cnf_transformation,[],[f16])).
% 8.18/1.50  
% 8.18/1.50  fof(f6,axiom,(
% 8.18/1.50    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f23,plain,(
% 8.18/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 8.18/1.50    inference(cnf_transformation,[],[f6])).
% 8.18/1.50  
% 8.18/1.50  fof(f5,axiom,(
% 8.18/1.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f22,plain,(
% 8.18/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f5])).
% 8.18/1.50  
% 8.18/1.50  fof(f30,plain,(
% 8.18/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 8.18/1.50    inference(definition_unfolding,[],[f23,f22,f22])).
% 8.18/1.50  
% 8.18/1.50  fof(f4,axiom,(
% 8.18/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f21,plain,(
% 8.18/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.18/1.50    inference(cnf_transformation,[],[f4])).
% 8.18/1.50  
% 8.18/1.50  fof(f3,axiom,(
% 8.18/1.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f20,plain,(
% 8.18/1.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f3])).
% 8.18/1.50  
% 8.18/1.50  fof(f29,plain,(
% 8.18/1.50    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 8.18/1.50    inference(definition_unfolding,[],[f20,f22])).
% 8.18/1.50  
% 8.18/1.50  fof(f7,axiom,(
% 8.18/1.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f24,plain,(
% 8.18/1.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f7])).
% 8.18/1.50  
% 8.18/1.50  fof(f8,axiom,(
% 8.18/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f14,plain,(
% 8.18/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 8.18/1.50    inference(nnf_transformation,[],[f8])).
% 8.18/1.50  
% 8.18/1.50  fof(f25,plain,(
% 8.18/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f14])).
% 8.18/1.50  
% 8.18/1.50  fof(f18,plain,(
% 8.18/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 8.18/1.50    inference(cnf_transformation,[],[f13])).
% 8.18/1.50  
% 8.18/1.50  fof(f28,plain,(
% 8.18/1.50    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 8.18/1.50    inference(cnf_transformation,[],[f16])).
% 8.18/1.50  
% 8.18/1.50  fof(f31,plain,(
% 8.18/1.50    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1)),
% 8.18/1.50    inference(definition_unfolding,[],[f28,f22])).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1,plain,
% 8.18/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 8.18/1.50      inference(cnf_transformation,[],[f19]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_69,plain,
% 8.18/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 8.18/1.50      inference(prop_impl,[status(thm)],[c_1]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_10,negated_conjecture,
% 8.18/1.50      ( r1_tarski(sK0,sK1) ),
% 8.18/1.50      inference(cnf_transformation,[],[f27]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_130,plain,
% 8.18/1.50      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 8.18/1.50      inference(resolution_lifted,[status(thm)],[c_69,c_10]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_131,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 8.18/1.50      inference(unflattening,[status(thm)],[c_130]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 8.18/1.50      inference(cnf_transformation,[],[f30]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_586,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_131,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_4,plain,
% 8.18/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.18/1.50      inference(cnf_transformation,[],[f21]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_597,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_586,c_4]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_3,plain,
% 8.18/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 8.18/1.50      inference(cnf_transformation,[],[f29]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_333,plain,
% 8.18/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_587,plain,
% 8.18/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_333,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_596,plain,
% 8.18/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_587,c_4]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_709,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_597,c_596]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_6,plain,
% 8.18/1.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 8.18/1.50      inference(cnf_transformation,[],[f24]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_331,plain,
% 8.18/1.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_589,plain,
% 8.18/1.50      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_5,c_331]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_712,plain,
% 8.18/1.50      ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK1,X0)) = iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_597,c_589]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_8,plain,
% 8.18/1.50      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 8.18/1.50      inference(cnf_transformation,[],[f25]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_329,plain,
% 8.18/1.50      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_899,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_712,c_329]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1697,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_709,c_899]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1723,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_1697,c_709]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_705,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_596,c_597]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_800,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_705,c_709]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_801,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_800,c_596,c_709]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1044,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),X1))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),X1) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_801,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_710,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_597,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_926,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,X0),X1)) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,X0),X1)) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_710,c_596]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_934,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_926,c_710]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1053,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_1044,c_5,c_926,c_934]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1054,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),X1) ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_1053,c_709]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1724,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_1723,c_596,c_1054]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_16649,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0)),X1) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_1724,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_469,plain,
% 8.18/1.50      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_333,c_331]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_793,plain,
% 8.18/1.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_469,c_329]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_16698,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_16649,c_5,c_333,c_793]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_19797,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k1_xboole_0,X2) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_16698,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_918,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_333,c_710]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1015,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X0)) = k1_xboole_0 ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_918,c_4,c_333]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1367,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k1_xboole_0 ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_709,c_1015]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1649,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0)))) = k1_xboole_0 ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_596,c_1367]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_681,plain,
% 8.18/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_596,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_685,plain,
% 8.18/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_681,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_686,plain,
% 8.18/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_685,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_17598,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0))))))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0))))) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_1649,c_686]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_18803,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0))))))) = k4_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_17598,c_1649]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_890,plain,
% 8.18/1.50      ( r1_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) = iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_596,c_712]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1125,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_890,c_329]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_18804,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),sK1)) = k4_xboole_0(sK0,X0) ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_18803,c_4,c_333,c_1125]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_19277,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_18804,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_20141,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_19797,c_5,c_793,c_19277]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_24763,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_20141,c_20141]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_24913,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,sK1))) = k1_xboole_0 ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_24763,c_4,c_793,c_1054]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2,plain,
% 8.18/1.50      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 8.18/1.50      inference(cnf_transformation,[],[f18]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_67,plain,
% 8.18/1.50      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 8.18/1.50      inference(prop_impl,[status(thm)],[c_2]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_9,negated_conjecture,
% 8.18/1.50      ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1) ),
% 8.18/1.50      inference(cnf_transformation,[],[f31]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_125,plain,
% 8.18/1.50      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 8.18/1.50      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
% 8.18/1.50      | sK1 != X1 ),
% 8.18/1.50      inference(resolution_lifted,[status(thm)],[c_67,c_9]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_126,plain,
% 8.18/1.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1) != k1_xboole_0 ),
% 8.18/1.50      inference(unflattening,[status(thm)],[c_125]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_376,plain,
% 8.18/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))) != k1_xboole_0 ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_126,c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_26634,plain,
% 8.18/1.50      ( k1_xboole_0 != k1_xboole_0 ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_24913,c_376]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_198,plain,( X0 = X0 ),theory(equality) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_205,plain,
% 8.18/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_198]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(contradiction,plain,
% 8.18/1.50      ( $false ),
% 8.18/1.50      inference(minisat,[status(thm)],[c_26634,c_205]) ).
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 8.18/1.50  
% 8.18/1.50  ------                               Statistics
% 8.18/1.50  
% 8.18/1.50  ------ General
% 8.18/1.50  
% 8.18/1.50  abstr_ref_over_cycles:                  0
% 8.18/1.50  abstr_ref_under_cycles:                 0
% 8.18/1.50  gc_basic_clause_elim:                   0
% 8.18/1.50  forced_gc_time:                         0
% 8.18/1.50  parsing_time:                           0.008
% 8.18/1.50  unif_index_cands_time:                  0.
% 8.18/1.50  unif_index_add_time:                    0.
% 8.18/1.50  orderings_time:                         0.
% 8.18/1.50  out_proof_time:                         0.008
% 8.18/1.50  total_time:                             0.961
% 8.18/1.50  num_of_symbols:                         38
% 8.18/1.50  num_of_terms:                           49335
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing
% 8.18/1.50  
% 8.18/1.50  num_of_splits:                          0
% 8.18/1.50  num_of_split_atoms:                     0
% 8.18/1.50  num_of_reused_defs:                     0
% 8.18/1.50  num_eq_ax_congr_red:                    3
% 8.18/1.50  num_of_sem_filtered_clauses:            1
% 8.18/1.50  num_of_subtypes:                        0
% 8.18/1.50  monotx_restored_types:                  0
% 8.18/1.50  sat_num_of_epr_types:                   0
% 8.18/1.50  sat_num_of_non_cyclic_types:            0
% 8.18/1.50  sat_guarded_non_collapsed_types:        0
% 8.18/1.50  num_pure_diseq_elim:                    0
% 8.18/1.50  simp_replaced_by:                       0
% 8.18/1.50  res_preprocessed:                       50
% 8.18/1.50  prep_upred:                             0
% 8.18/1.50  prep_unflattend:                        4
% 8.18/1.50  smt_new_axioms:                         0
% 8.18/1.50  pred_elim_cands:                        1
% 8.18/1.50  pred_elim:                              1
% 8.18/1.50  pred_elim_cl:                           1
% 8.18/1.50  pred_elim_cycles:                       3
% 8.18/1.50  merged_defs:                            10
% 8.18/1.50  merged_defs_ncl:                        0
% 8.18/1.50  bin_hyper_res:                          10
% 8.18/1.50  prep_cycles:                            4
% 8.18/1.50  pred_elim_time:                         0.
% 8.18/1.50  splitting_time:                         0.
% 8.18/1.50  sem_filter_time:                        0.
% 8.18/1.50  monotx_time:                            0.
% 8.18/1.50  subtype_inf_time:                       0.
% 8.18/1.50  
% 8.18/1.50  ------ Problem properties
% 8.18/1.50  
% 8.18/1.50  clauses:                                10
% 8.18/1.50  conjectures:                            0
% 8.18/1.50  epr:                                    1
% 8.18/1.50  horn:                                   10
% 8.18/1.50  ground:                                 3
% 8.18/1.50  unary:                                  7
% 8.18/1.50  binary:                                 3
% 8.18/1.50  lits:                                   13
% 8.18/1.50  lits_eq:                                8
% 8.18/1.50  fd_pure:                                0
% 8.18/1.50  fd_pseudo:                              0
% 8.18/1.50  fd_cond:                                0
% 8.18/1.50  fd_pseudo_cond:                         0
% 8.18/1.50  ac_symbols:                             0
% 8.18/1.50  
% 8.18/1.50  ------ Propositional Solver
% 8.18/1.50  
% 8.18/1.50  prop_solver_calls:                      33
% 8.18/1.50  prop_fast_solver_calls:                 308
% 8.18/1.50  smt_solver_calls:                       0
% 8.18/1.50  smt_fast_solver_calls:                  0
% 8.18/1.50  prop_num_of_clauses:                    6399
% 8.18/1.50  prop_preprocess_simplified:             5515
% 8.18/1.50  prop_fo_subsumed:                       0
% 8.18/1.50  prop_solver_time:                       0.
% 8.18/1.50  smt_solver_time:                        0.
% 8.18/1.50  smt_fast_solver_time:                   0.
% 8.18/1.50  prop_fast_solver_time:                  0.
% 8.18/1.50  prop_unsat_core_time:                   0.
% 8.18/1.50  
% 8.18/1.50  ------ QBF
% 8.18/1.50  
% 8.18/1.50  qbf_q_res:                              0
% 8.18/1.50  qbf_num_tautologies:                    0
% 8.18/1.50  qbf_prep_cycles:                        0
% 8.18/1.50  
% 8.18/1.50  ------ BMC1
% 8.18/1.50  
% 8.18/1.50  bmc1_current_bound:                     -1
% 8.18/1.50  bmc1_last_solved_bound:                 -1
% 8.18/1.50  bmc1_unsat_core_size:                   -1
% 8.18/1.50  bmc1_unsat_core_parents_size:           -1
% 8.18/1.50  bmc1_merge_next_fun:                    0
% 8.18/1.50  bmc1_unsat_core_clauses_time:           0.
% 8.18/1.50  
% 8.18/1.50  ------ Instantiation
% 8.18/1.50  
% 8.18/1.50  inst_num_of_clauses:                    1116
% 8.18/1.50  inst_num_in_passive:                    146
% 8.18/1.50  inst_num_in_active:                     585
% 8.18/1.50  inst_num_in_unprocessed:                385
% 8.18/1.50  inst_num_of_loops:                      650
% 8.18/1.50  inst_num_of_learning_restarts:          0
% 8.18/1.50  inst_num_moves_active_passive:          59
% 8.18/1.50  inst_lit_activity:                      0
% 8.18/1.50  inst_lit_activity_moves:                0
% 8.18/1.50  inst_num_tautologies:                   0
% 8.18/1.50  inst_num_prop_implied:                  0
% 8.18/1.50  inst_num_existing_simplified:           0
% 8.18/1.50  inst_num_eq_res_simplified:             0
% 8.18/1.50  inst_num_child_elim:                    0
% 8.18/1.50  inst_num_of_dismatching_blockings:      936
% 8.18/1.50  inst_num_of_non_proper_insts:           1888
% 8.18/1.50  inst_num_of_duplicates:                 0
% 8.18/1.50  inst_inst_num_from_inst_to_res:         0
% 8.18/1.50  inst_dismatching_checking_time:         0.
% 8.18/1.50  
% 8.18/1.50  ------ Resolution
% 8.18/1.50  
% 8.18/1.50  res_num_of_clauses:                     0
% 8.18/1.50  res_num_in_passive:                     0
% 8.18/1.50  res_num_in_active:                      0
% 8.18/1.50  res_num_of_loops:                       54
% 8.18/1.50  res_forward_subset_subsumed:            279
% 8.18/1.50  res_backward_subset_subsumed:           4
% 8.18/1.50  res_forward_subsumed:                   0
% 8.18/1.50  res_backward_subsumed:                  0
% 8.18/1.50  res_forward_subsumption_resolution:     0
% 8.18/1.50  res_backward_subsumption_resolution:    0
% 8.18/1.50  res_clause_to_clause_subsumption:       22154
% 8.18/1.50  res_orphan_elimination:                 0
% 8.18/1.50  res_tautology_del:                      156
% 8.18/1.50  res_num_eq_res_simplified:              1
% 8.18/1.50  res_num_sel_changes:                    0
% 8.18/1.50  res_moves_from_active_to_pass:          0
% 8.18/1.50  
% 8.18/1.50  ------ Superposition
% 8.18/1.50  
% 8.18/1.50  sup_time_total:                         0.
% 8.18/1.50  sup_time_generating:                    0.
% 8.18/1.50  sup_time_sim_full:                      0.
% 8.18/1.50  sup_time_sim_immed:                     0.
% 8.18/1.50  
% 8.18/1.50  sup_num_of_clauses:                     1341
% 8.18/1.50  sup_num_in_active:                      94
% 8.18/1.50  sup_num_in_passive:                     1247
% 8.18/1.50  sup_num_of_loops:                       128
% 8.18/1.50  sup_fw_superposition:                   4676
% 8.18/1.50  sup_bw_superposition:                   3429
% 8.18/1.50  sup_immediate_simplified:               5119
% 8.18/1.50  sup_given_eliminated:                   23
% 8.18/1.50  comparisons_done:                       0
% 8.18/1.50  comparisons_avoided:                    0
% 8.18/1.50  
% 8.18/1.50  ------ Simplifications
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  sim_fw_subset_subsumed:                 2
% 8.18/1.50  sim_bw_subset_subsumed:                 0
% 8.18/1.50  sim_fw_subsumed:                        1359
% 8.18/1.50  sim_bw_subsumed:                        74
% 8.18/1.50  sim_fw_subsumption_res:                 0
% 8.18/1.50  sim_bw_subsumption_res:                 0
% 8.18/1.50  sim_tautology_del:                      0
% 8.18/1.50  sim_eq_tautology_del:                   1397
% 8.18/1.50  sim_eq_res_simp:                        3
% 8.18/1.50  sim_fw_demodulated:                     7033
% 8.18/1.50  sim_bw_demodulated:                     258
% 8.18/1.50  sim_light_normalised:                   1986
% 8.18/1.50  sim_joinable_taut:                      0
% 8.18/1.50  sim_joinable_simp:                      0
% 8.18/1.50  sim_ac_normalised:                      0
% 8.18/1.50  sim_smt_subsumption:                    0
% 8.18/1.50  
%------------------------------------------------------------------------------
