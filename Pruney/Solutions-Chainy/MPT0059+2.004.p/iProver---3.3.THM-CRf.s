%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:58 EST 2020

% Result     : Theorem 43.28s
% Output     : CNFRefutation 43.28s
% Verified   : 
% Statistics : Number of formulae       :  141 (14089 expanded)
%              Number of clauses        :  112 (4499 expanded)
%              Number of leaves         :   10 (3943 expanded)
%              Depth                    :   34
%              Number of atoms          :  149 (17135 expanded)
%              Number of equality atoms :  140 (13654 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f22,f22])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f18,f22,f22,f22,f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f23,f22,f22,f22])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f24,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f24,f22])).

cnf(c_1,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_40,plain,
    ( X0 != X1
    | k4_xboole_0(X1,X2) != X3
    | k4_xboole_0(X3,X0) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_41,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_40])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_73,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_41,c_0])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_81,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_73,c_5])).

cnf(c_163,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_1,c_81])).

cnf(c_166,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_41])).

cnf(c_601,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_166,c_0])).

cnf(c_611,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_601,c_5])).

cnf(c_108,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_81])).

cnf(c_505,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_108,c_108])).

cnf(c_77,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_41])).

cnf(c_532,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_505,c_77])).

cnf(c_2,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4190,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),X2)) ),
    inference(superposition,[status(thm)],[c_532,c_2])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_213,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_262,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_213,c_108])).

cnf(c_307,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_302,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_6,c_2])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_81,c_1])).

cnf(c_375,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(light_normalisation,[status(thm)],[c_302,c_148])).

cnf(c_2735,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_148,c_6])).

cnf(c_2764,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))))) ),
    inference(light_normalisation,[status(thm)],[c_2735,c_307])).

cnf(c_59,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_41])).

cnf(c_139,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_59,c_1])).

cnf(c_187,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_139,c_81])).

cnf(c_221,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_81,c_6])).

cnf(c_253,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_221,c_6])).

cnf(c_2765,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_2764,c_41,c_81,c_187,c_253])).

cnf(c_333,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_77])).

cnf(c_2276,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0))),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_41,c_333])).

cnf(c_2406,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2276,c_5])).

cnf(c_2444,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_41,c_2406])).

cnf(c_2592,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2444,c_5])).

cnf(c_3003,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k4_xboole_0(X0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),X3)) ),
    inference(superposition,[status(thm)],[c_2592,c_2])).

cnf(c_3005,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3))) ),
    inference(superposition,[status(thm)],[c_2592,c_6])).

cnf(c_137,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_41,c_1])).

cnf(c_191,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_137,c_187])).

cnf(c_3089,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
    inference(demodulation,[status(thm)],[c_3005,c_5,c_191])).

cnf(c_3090,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3)) ),
    inference(demodulation,[status(thm)],[c_3003,c_3089])).

cnf(c_3091,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3)) ),
    inference(demodulation,[status(thm)],[c_3090,c_5])).

cnf(c_4325,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(X0,X2)))) ),
    inference(demodulation,[status(thm)],[c_4190,c_262,c_307,c_375,c_2765,c_3091])).

cnf(c_2743,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_148,c_148])).

cnf(c_141,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_1234,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_1,c_141])).

cnf(c_1394,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_1234,c_5,c_41])).

cnf(c_2758,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2743,c_1394])).

cnf(c_4326,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_4325,c_5,c_81,c_307,c_2758])).

cnf(c_6870,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_163,c_611,c_4326])).

cnf(c_7195,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_6870,c_81])).

cnf(c_7221,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6870,c_1])).

cnf(c_151,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_7264,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6870,c_151])).

cnf(c_7302,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_7264,c_81])).

cnf(c_7362,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_7221,c_7302])).

cnf(c_7394,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_7195,c_7362])).

cnf(c_7,negated_conjecture,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_134,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_1,c_7])).

cnf(c_119609,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_7394,c_134])).

cnf(c_1305,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_141,c_81])).

cnf(c_1320,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1305,c_59])).

cnf(c_13722,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_1320,c_141])).

cnf(c_6925,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_6870])).

cnf(c_512,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_108,c_6])).

cnf(c_527,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_512,c_6])).

cnf(c_7631,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_6925,c_527])).

cnf(c_7632,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_7631,c_81])).

cnf(c_13800,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_13722,c_7632])).

cnf(c_220,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_59,c_6])).

cnf(c_254,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_220,c_5])).

cnf(c_255,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_254,c_41])).

cnf(c_136,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_62,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_41,c_5])).

cnf(c_192,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_136,c_5,c_62])).

cnf(c_397,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_192])).

cnf(c_674,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_255,c_397])).

cnf(c_696,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_674,c_5])).

cnf(c_157,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_177,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(light_normalisation,[status(thm)],[c_157,c_5])).

cnf(c_178,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_177,c_5,c_59])).

cnf(c_697,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_696,c_178])).

cnf(c_741,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_697,c_1])).

cnf(c_750,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_741,c_178])).

cnf(c_737,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_697,c_1])).

cnf(c_754,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_737,c_5,c_59])).

cnf(c_1467,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_754])).

cnf(c_7181,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_6870,c_1467])).

cnf(c_7249,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_6870,c_141])).

cnf(c_7326,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_7249,c_253])).

cnf(c_7327,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_7326,c_81])).

cnf(c_7415,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = X0 ),
    inference(demodulation,[status(thm)],[c_7181,c_7327,c_7362])).

cnf(c_145,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_41,c_1])).

cnf(c_147,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_59,c_1])).

cnf(c_180,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_147,c_108])).

cnf(c_184,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_145,c_180])).

cnf(c_7416,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),X2)) = X0 ),
    inference(demodulation,[status(thm)],[c_7415,c_184])).

cnf(c_8591,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_750,c_7416])).

cnf(c_9068,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8591,c_6870])).

cnf(c_9127,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_9068,c_81])).

cnf(c_9128,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_9127,c_81])).

cnf(c_9478,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X0))))) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9128,c_151])).

cnf(c_9560,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X0))))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9128,c_1])).

cnf(c_9644,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X0))))) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_9560,c_7302])).

cnf(c_9657,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_9478,c_9644])).

cnf(c_13801,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_13800,c_187,c_9657])).

cnf(c_119610,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_119609,c_13801])).

cnf(c_119611,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_119610])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 43.28/6.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.28/6.02  
% 43.28/6.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.28/6.02  
% 43.28/6.02  ------  iProver source info
% 43.28/6.02  
% 43.28/6.02  git: date: 2020-06-30 10:37:57 +0100
% 43.28/6.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.28/6.02  git: non_committed_changes: false
% 43.28/6.02  git: last_make_outside_of_git: false
% 43.28/6.02  
% 43.28/6.02  ------ 
% 43.28/6.02  
% 43.28/6.02  ------ Input Options
% 43.28/6.02  
% 43.28/6.02  --out_options                           all
% 43.28/6.02  --tptp_safe_out                         true
% 43.28/6.02  --problem_path                          ""
% 43.28/6.02  --include_path                          ""
% 43.28/6.02  --clausifier                            res/vclausify_rel
% 43.28/6.02  --clausifier_options                    --mode clausify
% 43.28/6.02  --stdin                                 false
% 43.28/6.02  --stats_out                             all
% 43.28/6.02  
% 43.28/6.02  ------ General Options
% 43.28/6.02  
% 43.28/6.02  --fof                                   false
% 43.28/6.02  --time_out_real                         305.
% 43.28/6.02  --time_out_virtual                      -1.
% 43.28/6.02  --symbol_type_check                     false
% 43.28/6.02  --clausify_out                          false
% 43.28/6.02  --sig_cnt_out                           false
% 43.28/6.02  --trig_cnt_out                          false
% 43.28/6.02  --trig_cnt_out_tolerance                1.
% 43.28/6.02  --trig_cnt_out_sk_spl                   false
% 43.28/6.02  --abstr_cl_out                          false
% 43.28/6.02  
% 43.28/6.02  ------ Global Options
% 43.28/6.02  
% 43.28/6.02  --schedule                              default
% 43.28/6.02  --add_important_lit                     false
% 43.28/6.02  --prop_solver_per_cl                    1000
% 43.28/6.02  --min_unsat_core                        false
% 43.28/6.02  --soft_assumptions                      false
% 43.28/6.02  --soft_lemma_size                       3
% 43.28/6.02  --prop_impl_unit_size                   0
% 43.28/6.02  --prop_impl_unit                        []
% 43.28/6.02  --share_sel_clauses                     true
% 43.28/6.02  --reset_solvers                         false
% 43.28/6.02  --bc_imp_inh                            [conj_cone]
% 43.28/6.02  --conj_cone_tolerance                   3.
% 43.28/6.02  --extra_neg_conj                        none
% 43.28/6.02  --large_theory_mode                     true
% 43.28/6.02  --prolific_symb_bound                   200
% 43.28/6.02  --lt_threshold                          2000
% 43.28/6.02  --clause_weak_htbl                      true
% 43.28/6.02  --gc_record_bc_elim                     false
% 43.28/6.02  
% 43.28/6.02  ------ Preprocessing Options
% 43.28/6.02  
% 43.28/6.02  --preprocessing_flag                    true
% 43.28/6.02  --time_out_prep_mult                    0.1
% 43.28/6.02  --splitting_mode                        input
% 43.28/6.02  --splitting_grd                         true
% 43.28/6.02  --splitting_cvd                         false
% 43.28/6.02  --splitting_cvd_svl                     false
% 43.28/6.02  --splitting_nvd                         32
% 43.28/6.02  --sub_typing                            true
% 43.28/6.02  --prep_gs_sim                           true
% 43.28/6.02  --prep_unflatten                        true
% 43.28/6.02  --prep_res_sim                          true
% 43.28/6.02  --prep_upred                            true
% 43.28/6.02  --prep_sem_filter                       exhaustive
% 43.28/6.02  --prep_sem_filter_out                   false
% 43.28/6.02  --pred_elim                             true
% 43.28/6.02  --res_sim_input                         true
% 43.28/6.02  --eq_ax_congr_red                       true
% 43.28/6.02  --pure_diseq_elim                       true
% 43.28/6.02  --brand_transform                       false
% 43.28/6.02  --non_eq_to_eq                          false
% 43.28/6.02  --prep_def_merge                        true
% 43.28/6.02  --prep_def_merge_prop_impl              false
% 43.28/6.02  --prep_def_merge_mbd                    true
% 43.28/6.02  --prep_def_merge_tr_red                 false
% 43.28/6.02  --prep_def_merge_tr_cl                  false
% 43.28/6.02  --smt_preprocessing                     true
% 43.28/6.02  --smt_ac_axioms                         fast
% 43.28/6.02  --preprocessed_out                      false
% 43.28/6.02  --preprocessed_stats                    false
% 43.28/6.02  
% 43.28/6.02  ------ Abstraction refinement Options
% 43.28/6.02  
% 43.28/6.02  --abstr_ref                             []
% 43.28/6.02  --abstr_ref_prep                        false
% 43.28/6.02  --abstr_ref_until_sat                   false
% 43.28/6.02  --abstr_ref_sig_restrict                funpre
% 43.28/6.02  --abstr_ref_af_restrict_to_split_sk     false
% 43.28/6.02  --abstr_ref_under                       []
% 43.28/6.02  
% 43.28/6.02  ------ SAT Options
% 43.28/6.02  
% 43.28/6.02  --sat_mode                              false
% 43.28/6.02  --sat_fm_restart_options                ""
% 43.28/6.02  --sat_gr_def                            false
% 43.28/6.02  --sat_epr_types                         true
% 43.28/6.02  --sat_non_cyclic_types                  false
% 43.28/6.02  --sat_finite_models                     false
% 43.28/6.02  --sat_fm_lemmas                         false
% 43.28/6.02  --sat_fm_prep                           false
% 43.28/6.02  --sat_fm_uc_incr                        true
% 43.28/6.02  --sat_out_model                         small
% 43.28/6.02  --sat_out_clauses                       false
% 43.28/6.02  
% 43.28/6.02  ------ QBF Options
% 43.28/6.02  
% 43.28/6.02  --qbf_mode                              false
% 43.28/6.02  --qbf_elim_univ                         false
% 43.28/6.02  --qbf_dom_inst                          none
% 43.28/6.02  --qbf_dom_pre_inst                      false
% 43.28/6.02  --qbf_sk_in                             false
% 43.28/6.02  --qbf_pred_elim                         true
% 43.28/6.02  --qbf_split                             512
% 43.28/6.02  
% 43.28/6.02  ------ BMC1 Options
% 43.28/6.02  
% 43.28/6.02  --bmc1_incremental                      false
% 43.28/6.02  --bmc1_axioms                           reachable_all
% 43.28/6.02  --bmc1_min_bound                        0
% 43.28/6.02  --bmc1_max_bound                        -1
% 43.28/6.02  --bmc1_max_bound_default                -1
% 43.28/6.02  --bmc1_symbol_reachability              true
% 43.28/6.02  --bmc1_property_lemmas                  false
% 43.28/6.02  --bmc1_k_induction                      false
% 43.28/6.02  --bmc1_non_equiv_states                 false
% 43.28/6.02  --bmc1_deadlock                         false
% 43.28/6.02  --bmc1_ucm                              false
% 43.28/6.02  --bmc1_add_unsat_core                   none
% 43.28/6.02  --bmc1_unsat_core_children              false
% 43.28/6.02  --bmc1_unsat_core_extrapolate_axioms    false
% 43.28/6.02  --bmc1_out_stat                         full
% 43.28/6.02  --bmc1_ground_init                      false
% 43.28/6.02  --bmc1_pre_inst_next_state              false
% 43.28/6.02  --bmc1_pre_inst_state                   false
% 43.28/6.02  --bmc1_pre_inst_reach_state             false
% 43.28/6.02  --bmc1_out_unsat_core                   false
% 43.28/6.02  --bmc1_aig_witness_out                  false
% 43.28/6.02  --bmc1_verbose                          false
% 43.28/6.02  --bmc1_dump_clauses_tptp                false
% 43.28/6.02  --bmc1_dump_unsat_core_tptp             false
% 43.28/6.02  --bmc1_dump_file                        -
% 43.28/6.02  --bmc1_ucm_expand_uc_limit              128
% 43.28/6.02  --bmc1_ucm_n_expand_iterations          6
% 43.28/6.02  --bmc1_ucm_extend_mode                  1
% 43.28/6.02  --bmc1_ucm_init_mode                    2
% 43.28/6.02  --bmc1_ucm_cone_mode                    none
% 43.28/6.02  --bmc1_ucm_reduced_relation_type        0
% 43.28/6.02  --bmc1_ucm_relax_model                  4
% 43.28/6.02  --bmc1_ucm_full_tr_after_sat            true
% 43.28/6.02  --bmc1_ucm_expand_neg_assumptions       false
% 43.28/6.02  --bmc1_ucm_layered_model                none
% 43.28/6.02  --bmc1_ucm_max_lemma_size               10
% 43.28/6.02  
% 43.28/6.02  ------ AIG Options
% 43.28/6.02  
% 43.28/6.02  --aig_mode                              false
% 43.28/6.02  
% 43.28/6.02  ------ Instantiation Options
% 43.28/6.02  
% 43.28/6.02  --instantiation_flag                    true
% 43.28/6.02  --inst_sos_flag                         false
% 43.28/6.02  --inst_sos_phase                        true
% 43.28/6.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.28/6.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.28/6.02  --inst_lit_sel_side                     num_symb
% 43.28/6.02  --inst_solver_per_active                1400
% 43.28/6.02  --inst_solver_calls_frac                1.
% 43.28/6.02  --inst_passive_queue_type               priority_queues
% 43.28/6.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.28/6.02  --inst_passive_queues_freq              [25;2]
% 43.28/6.02  --inst_dismatching                      true
% 43.28/6.02  --inst_eager_unprocessed_to_passive     true
% 43.28/6.02  --inst_prop_sim_given                   true
% 43.28/6.02  --inst_prop_sim_new                     false
% 43.28/6.02  --inst_subs_new                         false
% 43.28/6.02  --inst_eq_res_simp                      false
% 43.28/6.02  --inst_subs_given                       false
% 43.28/6.02  --inst_orphan_elimination               true
% 43.28/6.02  --inst_learning_loop_flag               true
% 43.28/6.02  --inst_learning_start                   3000
% 43.28/6.02  --inst_learning_factor                  2
% 43.28/6.02  --inst_start_prop_sim_after_learn       3
% 43.28/6.02  --inst_sel_renew                        solver
% 43.28/6.02  --inst_lit_activity_flag                true
% 43.28/6.02  --inst_restr_to_given                   false
% 43.28/6.02  --inst_activity_threshold               500
% 43.28/6.02  --inst_out_proof                        true
% 43.28/6.02  
% 43.28/6.02  ------ Resolution Options
% 43.28/6.02  
% 43.28/6.02  --resolution_flag                       true
% 43.28/6.02  --res_lit_sel                           adaptive
% 43.28/6.02  --res_lit_sel_side                      none
% 43.28/6.02  --res_ordering                          kbo
% 43.28/6.02  --res_to_prop_solver                    active
% 43.28/6.02  --res_prop_simpl_new                    false
% 43.28/6.02  --res_prop_simpl_given                  true
% 43.28/6.02  --res_passive_queue_type                priority_queues
% 43.28/6.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.28/6.02  --res_passive_queues_freq               [15;5]
% 43.28/6.02  --res_forward_subs                      full
% 43.28/6.02  --res_backward_subs                     full
% 43.28/6.02  --res_forward_subs_resolution           true
% 43.28/6.02  --res_backward_subs_resolution          true
% 43.28/6.02  --res_orphan_elimination                true
% 43.28/6.02  --res_time_limit                        2.
% 43.28/6.02  --res_out_proof                         true
% 43.28/6.02  
% 43.28/6.02  ------ Superposition Options
% 43.28/6.02  
% 43.28/6.02  --superposition_flag                    true
% 43.28/6.02  --sup_passive_queue_type                priority_queues
% 43.28/6.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.28/6.02  --sup_passive_queues_freq               [8;1;4]
% 43.28/6.02  --demod_completeness_check              fast
% 43.28/6.02  --demod_use_ground                      true
% 43.28/6.02  --sup_to_prop_solver                    passive
% 43.28/6.02  --sup_prop_simpl_new                    true
% 43.28/6.02  --sup_prop_simpl_given                  true
% 43.28/6.02  --sup_fun_splitting                     false
% 43.28/6.02  --sup_smt_interval                      50000
% 43.28/6.02  
% 43.28/6.02  ------ Superposition Simplification Setup
% 43.28/6.02  
% 43.28/6.02  --sup_indices_passive                   []
% 43.28/6.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.28/6.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.28/6.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.28/6.02  --sup_full_triv                         [TrivRules;PropSubs]
% 43.28/6.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.28/6.02  --sup_full_bw                           [BwDemod]
% 43.28/6.02  --sup_immed_triv                        [TrivRules]
% 43.28/6.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.28/6.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.28/6.02  --sup_immed_bw_main                     []
% 43.28/6.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.28/6.02  --sup_input_triv                        [Unflattening;TrivRules]
% 43.28/6.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.28/6.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.28/6.02  
% 43.28/6.02  ------ Combination Options
% 43.28/6.02  
% 43.28/6.02  --comb_res_mult                         3
% 43.28/6.02  --comb_sup_mult                         2
% 43.28/6.02  --comb_inst_mult                        10
% 43.28/6.02  
% 43.28/6.02  ------ Debug Options
% 43.28/6.02  
% 43.28/6.02  --dbg_backtrace                         false
% 43.28/6.02  --dbg_dump_prop_clauses                 false
% 43.28/6.02  --dbg_dump_prop_clauses_file            -
% 43.28/6.02  --dbg_out_stat                          false
% 43.28/6.02  ------ Parsing...
% 43.28/6.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.28/6.02  
% 43.28/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 43.28/6.02  
% 43.28/6.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.28/6.02  
% 43.28/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.28/6.02  ------ Proving...
% 43.28/6.02  ------ Problem Properties 
% 43.28/6.02  
% 43.28/6.02  
% 43.28/6.02  clauses                                 7
% 43.28/6.02  conjectures                             1
% 43.28/6.02  EPR                                     0
% 43.28/6.02  Horn                                    7
% 43.28/6.02  unary                                   7
% 43.28/6.02  binary                                  0
% 43.28/6.02  lits                                    7
% 43.28/6.02  lits eq                                 7
% 43.28/6.02  fd_pure                                 0
% 43.28/6.02  fd_pseudo                               0
% 43.28/6.02  fd_cond                                 0
% 43.28/6.02  fd_pseudo_cond                          0
% 43.28/6.02  AC symbols                              0
% 43.28/6.02  
% 43.28/6.02  ------ Schedule UEQ
% 43.28/6.02  
% 43.28/6.02  ------ pure equality problem: resolution off 
% 43.28/6.02  
% 43.28/6.02  ------ Option_UEQ Time Limit: Unbounded
% 43.28/6.02  
% 43.28/6.02  
% 43.28/6.02  ------ 
% 43.28/6.02  Current options:
% 43.28/6.02  ------ 
% 43.28/6.02  
% 43.28/6.02  ------ Input Options
% 43.28/6.02  
% 43.28/6.02  --out_options                           all
% 43.28/6.02  --tptp_safe_out                         true
% 43.28/6.02  --problem_path                          ""
% 43.28/6.02  --include_path                          ""
% 43.28/6.02  --clausifier                            res/vclausify_rel
% 43.28/6.02  --clausifier_options                    --mode clausify
% 43.28/6.02  --stdin                                 false
% 43.28/6.02  --stats_out                             all
% 43.28/6.02  
% 43.28/6.02  ------ General Options
% 43.28/6.02  
% 43.28/6.02  --fof                                   false
% 43.28/6.02  --time_out_real                         305.
% 43.28/6.02  --time_out_virtual                      -1.
% 43.28/6.02  --symbol_type_check                     false
% 43.28/6.02  --clausify_out                          false
% 43.28/6.02  --sig_cnt_out                           false
% 43.28/6.02  --trig_cnt_out                          false
% 43.28/6.02  --trig_cnt_out_tolerance                1.
% 43.28/6.02  --trig_cnt_out_sk_spl                   false
% 43.28/6.02  --abstr_cl_out                          false
% 43.28/6.02  
% 43.28/6.02  ------ Global Options
% 43.28/6.02  
% 43.28/6.02  --schedule                              default
% 43.28/6.02  --add_important_lit                     false
% 43.28/6.02  --prop_solver_per_cl                    1000
% 43.28/6.02  --min_unsat_core                        false
% 43.28/6.02  --soft_assumptions                      false
% 43.28/6.02  --soft_lemma_size                       3
% 43.28/6.02  --prop_impl_unit_size                   0
% 43.28/6.02  --prop_impl_unit                        []
% 43.28/6.02  --share_sel_clauses                     true
% 43.28/6.02  --reset_solvers                         false
% 43.28/6.02  --bc_imp_inh                            [conj_cone]
% 43.28/6.02  --conj_cone_tolerance                   3.
% 43.28/6.02  --extra_neg_conj                        none
% 43.28/6.02  --large_theory_mode                     true
% 43.28/6.02  --prolific_symb_bound                   200
% 43.28/6.02  --lt_threshold                          2000
% 43.28/6.02  --clause_weak_htbl                      true
% 43.28/6.02  --gc_record_bc_elim                     false
% 43.28/6.02  
% 43.28/6.02  ------ Preprocessing Options
% 43.28/6.02  
% 43.28/6.02  --preprocessing_flag                    true
% 43.28/6.02  --time_out_prep_mult                    0.1
% 43.28/6.02  --splitting_mode                        input
% 43.28/6.02  --splitting_grd                         true
% 43.28/6.02  --splitting_cvd                         false
% 43.28/6.02  --splitting_cvd_svl                     false
% 43.28/6.02  --splitting_nvd                         32
% 43.28/6.02  --sub_typing                            true
% 43.28/6.02  --prep_gs_sim                           true
% 43.28/6.02  --prep_unflatten                        true
% 43.28/6.02  --prep_res_sim                          true
% 43.28/6.02  --prep_upred                            true
% 43.28/6.02  --prep_sem_filter                       exhaustive
% 43.28/6.02  --prep_sem_filter_out                   false
% 43.28/6.02  --pred_elim                             true
% 43.28/6.02  --res_sim_input                         true
% 43.28/6.02  --eq_ax_congr_red                       true
% 43.28/6.02  --pure_diseq_elim                       true
% 43.28/6.02  --brand_transform                       false
% 43.28/6.02  --non_eq_to_eq                          false
% 43.28/6.02  --prep_def_merge                        true
% 43.28/6.02  --prep_def_merge_prop_impl              false
% 43.28/6.02  --prep_def_merge_mbd                    true
% 43.28/6.02  --prep_def_merge_tr_red                 false
% 43.28/6.02  --prep_def_merge_tr_cl                  false
% 43.28/6.02  --smt_preprocessing                     true
% 43.28/6.02  --smt_ac_axioms                         fast
% 43.28/6.02  --preprocessed_out                      false
% 43.28/6.02  --preprocessed_stats                    false
% 43.28/6.02  
% 43.28/6.02  ------ Abstraction refinement Options
% 43.28/6.02  
% 43.28/6.02  --abstr_ref                             []
% 43.28/6.02  --abstr_ref_prep                        false
% 43.28/6.02  --abstr_ref_until_sat                   false
% 43.28/6.02  --abstr_ref_sig_restrict                funpre
% 43.28/6.02  --abstr_ref_af_restrict_to_split_sk     false
% 43.28/6.02  --abstr_ref_under                       []
% 43.28/6.02  
% 43.28/6.02  ------ SAT Options
% 43.28/6.02  
% 43.28/6.02  --sat_mode                              false
% 43.28/6.02  --sat_fm_restart_options                ""
% 43.28/6.02  --sat_gr_def                            false
% 43.28/6.02  --sat_epr_types                         true
% 43.28/6.02  --sat_non_cyclic_types                  false
% 43.28/6.02  --sat_finite_models                     false
% 43.28/6.02  --sat_fm_lemmas                         false
% 43.28/6.02  --sat_fm_prep                           false
% 43.28/6.02  --sat_fm_uc_incr                        true
% 43.28/6.02  --sat_out_model                         small
% 43.28/6.02  --sat_out_clauses                       false
% 43.28/6.02  
% 43.28/6.02  ------ QBF Options
% 43.28/6.02  
% 43.28/6.02  --qbf_mode                              false
% 43.28/6.02  --qbf_elim_univ                         false
% 43.28/6.02  --qbf_dom_inst                          none
% 43.28/6.02  --qbf_dom_pre_inst                      false
% 43.28/6.02  --qbf_sk_in                             false
% 43.28/6.02  --qbf_pred_elim                         true
% 43.28/6.02  --qbf_split                             512
% 43.28/6.02  
% 43.28/6.02  ------ BMC1 Options
% 43.28/6.02  
% 43.28/6.02  --bmc1_incremental                      false
% 43.28/6.02  --bmc1_axioms                           reachable_all
% 43.28/6.02  --bmc1_min_bound                        0
% 43.28/6.02  --bmc1_max_bound                        -1
% 43.28/6.02  --bmc1_max_bound_default                -1
% 43.28/6.02  --bmc1_symbol_reachability              true
% 43.28/6.02  --bmc1_property_lemmas                  false
% 43.28/6.02  --bmc1_k_induction                      false
% 43.28/6.02  --bmc1_non_equiv_states                 false
% 43.28/6.02  --bmc1_deadlock                         false
% 43.28/6.02  --bmc1_ucm                              false
% 43.28/6.02  --bmc1_add_unsat_core                   none
% 43.28/6.02  --bmc1_unsat_core_children              false
% 43.28/6.02  --bmc1_unsat_core_extrapolate_axioms    false
% 43.28/6.02  --bmc1_out_stat                         full
% 43.28/6.02  --bmc1_ground_init                      false
% 43.28/6.02  --bmc1_pre_inst_next_state              false
% 43.28/6.02  --bmc1_pre_inst_state                   false
% 43.28/6.02  --bmc1_pre_inst_reach_state             false
% 43.28/6.02  --bmc1_out_unsat_core                   false
% 43.28/6.02  --bmc1_aig_witness_out                  false
% 43.28/6.02  --bmc1_verbose                          false
% 43.28/6.02  --bmc1_dump_clauses_tptp                false
% 43.28/6.02  --bmc1_dump_unsat_core_tptp             false
% 43.28/6.02  --bmc1_dump_file                        -
% 43.28/6.02  --bmc1_ucm_expand_uc_limit              128
% 43.28/6.02  --bmc1_ucm_n_expand_iterations          6
% 43.28/6.02  --bmc1_ucm_extend_mode                  1
% 43.28/6.02  --bmc1_ucm_init_mode                    2
% 43.28/6.02  --bmc1_ucm_cone_mode                    none
% 43.28/6.02  --bmc1_ucm_reduced_relation_type        0
% 43.28/6.02  --bmc1_ucm_relax_model                  4
% 43.28/6.02  --bmc1_ucm_full_tr_after_sat            true
% 43.28/6.02  --bmc1_ucm_expand_neg_assumptions       false
% 43.28/6.02  --bmc1_ucm_layered_model                none
% 43.28/6.02  --bmc1_ucm_max_lemma_size               10
% 43.28/6.02  
% 43.28/6.02  ------ AIG Options
% 43.28/6.02  
% 43.28/6.02  --aig_mode                              false
% 43.28/6.02  
% 43.28/6.02  ------ Instantiation Options
% 43.28/6.02  
% 43.28/6.02  --instantiation_flag                    false
% 43.28/6.02  --inst_sos_flag                         false
% 43.28/6.02  --inst_sos_phase                        true
% 43.28/6.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.28/6.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.28/6.02  --inst_lit_sel_side                     num_symb
% 43.28/6.02  --inst_solver_per_active                1400
% 43.28/6.02  --inst_solver_calls_frac                1.
% 43.28/6.02  --inst_passive_queue_type               priority_queues
% 43.28/6.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.28/6.02  --inst_passive_queues_freq              [25;2]
% 43.28/6.02  --inst_dismatching                      true
% 43.28/6.02  --inst_eager_unprocessed_to_passive     true
% 43.28/6.02  --inst_prop_sim_given                   true
% 43.28/6.02  --inst_prop_sim_new                     false
% 43.28/6.02  --inst_subs_new                         false
% 43.28/6.02  --inst_eq_res_simp                      false
% 43.28/6.02  --inst_subs_given                       false
% 43.28/6.02  --inst_orphan_elimination               true
% 43.28/6.02  --inst_learning_loop_flag               true
% 43.28/6.02  --inst_learning_start                   3000
% 43.28/6.02  --inst_learning_factor                  2
% 43.28/6.02  --inst_start_prop_sim_after_learn       3
% 43.28/6.02  --inst_sel_renew                        solver
% 43.28/6.02  --inst_lit_activity_flag                true
% 43.28/6.02  --inst_restr_to_given                   false
% 43.28/6.02  --inst_activity_threshold               500
% 43.28/6.02  --inst_out_proof                        true
% 43.28/6.02  
% 43.28/6.02  ------ Resolution Options
% 43.28/6.02  
% 43.28/6.02  --resolution_flag                       false
% 43.28/6.02  --res_lit_sel                           adaptive
% 43.28/6.02  --res_lit_sel_side                      none
% 43.28/6.02  --res_ordering                          kbo
% 43.28/6.02  --res_to_prop_solver                    active
% 43.28/6.02  --res_prop_simpl_new                    false
% 43.28/6.02  --res_prop_simpl_given                  true
% 43.28/6.02  --res_passive_queue_type                priority_queues
% 43.28/6.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.28/6.02  --res_passive_queues_freq               [15;5]
% 43.28/6.02  --res_forward_subs                      full
% 43.28/6.02  --res_backward_subs                     full
% 43.28/6.02  --res_forward_subs_resolution           true
% 43.28/6.02  --res_backward_subs_resolution          true
% 43.28/6.02  --res_orphan_elimination                true
% 43.28/6.02  --res_time_limit                        2.
% 43.28/6.02  --res_out_proof                         true
% 43.28/6.02  
% 43.28/6.02  ------ Superposition Options
% 43.28/6.02  
% 43.28/6.02  --superposition_flag                    true
% 43.28/6.02  --sup_passive_queue_type                priority_queues
% 43.28/6.02  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.28/6.02  --sup_passive_queues_freq               [8;1;4]
% 43.28/6.02  --demod_completeness_check              fast
% 43.28/6.02  --demod_use_ground                      true
% 43.28/6.02  --sup_to_prop_solver                    active
% 43.28/6.02  --sup_prop_simpl_new                    false
% 43.28/6.02  --sup_prop_simpl_given                  false
% 43.28/6.02  --sup_fun_splitting                     true
% 43.28/6.02  --sup_smt_interval                      10000
% 43.28/6.02  
% 43.28/6.02  ------ Superposition Simplification Setup
% 43.28/6.02  
% 43.28/6.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.28/6.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.28/6.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.28/6.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.28/6.02  --sup_full_triv                         [TrivRules]
% 43.28/6.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.28/6.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.28/6.02  --sup_immed_triv                        [TrivRules]
% 43.28/6.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.28/6.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.28/6.02  --sup_immed_bw_main                     []
% 43.28/6.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.28/6.02  --sup_input_triv                        [Unflattening;TrivRules]
% 43.28/6.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.28/6.02  --sup_input_bw                          [BwDemod;BwSubsumption]
% 43.28/6.02  
% 43.28/6.02  ------ Combination Options
% 43.28/6.02  
% 43.28/6.02  --comb_res_mult                         1
% 43.28/6.02  --comb_sup_mult                         1
% 43.28/6.02  --comb_inst_mult                        1000000
% 43.28/6.02  
% 43.28/6.02  ------ Debug Options
% 43.28/6.02  
% 43.28/6.02  --dbg_backtrace                         false
% 43.28/6.02  --dbg_dump_prop_clauses                 false
% 43.28/6.02  --dbg_dump_prop_clauses_file            -
% 43.28/6.02  --dbg_out_stat                          false
% 43.28/6.02  
% 43.28/6.02  
% 43.28/6.02  
% 43.28/6.02  
% 43.28/6.02  ------ Proving...
% 43.28/6.02  
% 43.28/6.02  
% 43.28/6.02  % SZS status Theorem for theBenchmark.p
% 43.28/6.02  
% 43.28/6.02   Resolution empty clause
% 43.28/6.02  
% 43.28/6.02  % SZS output start CNFRefutation for theBenchmark.p
% 43.28/6.02  
% 43.28/6.02  fof(f2,axiom,(
% 43.28/6.02    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 43.28/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.28/6.02  
% 43.28/6.02  fof(f17,plain,(
% 43.28/6.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 43.28/6.02    inference(cnf_transformation,[],[f2])).
% 43.28/6.02  
% 43.28/6.02  fof(f7,axiom,(
% 43.28/6.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.28/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.28/6.02  
% 43.28/6.02  fof(f22,plain,(
% 43.28/6.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.28/6.02    inference(cnf_transformation,[],[f7])).
% 43.28/6.02  
% 43.28/6.02  fof(f26,plain,(
% 43.28/6.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 43.28/6.02    inference(definition_unfolding,[],[f17,f22])).
% 43.28/6.02  
% 43.28/6.02  fof(f4,axiom,(
% 43.28/6.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 43.28/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.28/6.02  
% 43.28/6.02  fof(f19,plain,(
% 43.28/6.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 43.28/6.02    inference(cnf_transformation,[],[f4])).
% 43.28/6.02  
% 43.28/6.02  fof(f5,axiom,(
% 43.28/6.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 43.28/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.28/6.02  
% 43.28/6.02  fof(f11,plain,(
% 43.28/6.02    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 43.28/6.02    inference(unused_predicate_definition_removal,[],[f5])).
% 43.28/6.02  
% 43.28/6.02  fof(f12,plain,(
% 43.28/6.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 43.28/6.02    inference(ennf_transformation,[],[f11])).
% 43.28/6.02  
% 43.28/6.02  fof(f20,plain,(
% 43.28/6.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 43.28/6.02    inference(cnf_transformation,[],[f12])).
% 43.28/6.02  
% 43.28/6.02  fof(f1,axiom,(
% 43.28/6.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.28/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.28/6.02  
% 43.28/6.02  fof(f16,plain,(
% 43.28/6.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.28/6.02    inference(cnf_transformation,[],[f1])).
% 43.28/6.02  
% 43.28/6.02  fof(f25,plain,(
% 43.28/6.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 43.28/6.02    inference(definition_unfolding,[],[f16,f22,f22])).
% 43.28/6.02  
% 43.28/6.02  fof(f6,axiom,(
% 43.28/6.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 43.28/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.28/6.02  
% 43.28/6.02  fof(f21,plain,(
% 43.28/6.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 43.28/6.02    inference(cnf_transformation,[],[f6])).
% 43.28/6.02  
% 43.28/6.02  fof(f3,axiom,(
% 43.28/6.02    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 43.28/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.28/6.02  
% 43.28/6.02  fof(f18,plain,(
% 43.28/6.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 43.28/6.02    inference(cnf_transformation,[],[f3])).
% 43.28/6.02  
% 43.28/6.02  fof(f27,plain,(
% 43.28/6.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 43.28/6.02    inference(definition_unfolding,[],[f18,f22,f22,f22,f22])).
% 43.28/6.02  
% 43.28/6.02  fof(f8,axiom,(
% 43.28/6.02    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 43.28/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.28/6.02  
% 43.28/6.02  fof(f23,plain,(
% 43.28/6.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 43.28/6.02    inference(cnf_transformation,[],[f8])).
% 43.28/6.02  
% 43.28/6.02  fof(f28,plain,(
% 43.28/6.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 43.28/6.02    inference(definition_unfolding,[],[f23,f22,f22,f22])).
% 43.28/6.02  
% 43.28/6.02  fof(f9,conjecture,(
% 43.28/6.02    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 43.28/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.28/6.02  
% 43.28/6.02  fof(f10,negated_conjecture,(
% 43.28/6.02    ~! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 43.28/6.02    inference(negated_conjecture,[],[f9])).
% 43.28/6.02  
% 43.28/6.02  fof(f13,plain,(
% 43.28/6.02    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 43.28/6.02    inference(ennf_transformation,[],[f10])).
% 43.28/6.02  
% 43.28/6.02  fof(f14,plain,(
% 43.28/6.02    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 43.28/6.02    introduced(choice_axiom,[])).
% 43.28/6.02  
% 43.28/6.02  fof(f15,plain,(
% 43.28/6.02    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 43.28/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 43.28/6.02  
% 43.28/6.02  fof(f24,plain,(
% 43.28/6.02    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 43.28/6.02    inference(cnf_transformation,[],[f15])).
% 43.28/6.02  
% 43.28/6.02  fof(f29,plain,(
% 43.28/6.02    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 43.28/6.02    inference(definition_unfolding,[],[f24,f22])).
% 43.28/6.02  
% 43.28/6.02  cnf(c_1,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 43.28/6.02      inference(cnf_transformation,[],[f26]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_3,plain,
% 43.28/6.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 43.28/6.02      inference(cnf_transformation,[],[f19]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_4,plain,
% 43.28/6.02      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 43.28/6.02      inference(cnf_transformation,[],[f20]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_40,plain,
% 43.28/6.02      ( X0 != X1
% 43.28/6.02      | k4_xboole_0(X1,X2) != X3
% 43.28/6.02      | k4_xboole_0(X3,X0) = k1_xboole_0 ),
% 43.28/6.02      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_41,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 43.28/6.02      inference(unflattening,[status(thm)],[c_40]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_0,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 43.28/6.02      inference(cnf_transformation,[],[f25]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_73,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_41,c_0]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_5,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.28/6.02      inference(cnf_transformation,[],[f21]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_81,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_73,c_5]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_163,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_1,c_81]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_166,plain,
% 43.28/6.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),X0) = k1_xboole_0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_1,c_41]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_601,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k1_xboole_0) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_166,c_0]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_611,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_601,c_5]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_108,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_0,c_81]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_505,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_108,c_108]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_77,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_0,c_41]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_532,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_505,c_77]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_2,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 43.28/6.02      inference(cnf_transformation,[],[f27]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_4190,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),X2)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_532,c_2]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_6,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 43.28/6.02      inference(cnf_transformation,[],[f28]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_213,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_262,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_213,c_108]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_307,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_302,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_6,c_2]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_148,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_81,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_375,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_302,c_148]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_2735,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_148,c_6]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_2764,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))))) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_2735,c_307]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_59,plain,
% 43.28/6.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_5,c_41]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_139,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_59,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_187,plain,
% 43.28/6.02      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_139,c_81]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_221,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_81,c_6]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_253,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_221,c_6]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_2765,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_2764,c_41,c_81,c_187,c_253]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_333,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = k1_xboole_0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_2,c_77]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_2276,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0))),X1) = k1_xboole_0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_41,c_333]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_2406,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X1) = k1_xboole_0 ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_2276,c_5]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_2444,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),X0) = k1_xboole_0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_41,c_2406]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_2592,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_2444,c_5]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_3003,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k4_xboole_0(X0,X3)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),X3)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_2592,c_2]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_3005,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_2592,c_6]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_137,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_41,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_191,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_137,c_187]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_3089,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_3005,c_5,c_191]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_3090,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_3003,c_3089]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_3091,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_3090,c_5]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_4325,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(X0,X2)))) ),
% 43.28/6.02      inference(demodulation,
% 43.28/6.02                [status(thm)],
% 43.28/6.02                [c_4190,c_262,c_307,c_375,c_2765,c_3091]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_2743,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X2)))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_148,c_148]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_141,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_1234,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X2)))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_1,c_141]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_1394,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_1234,c_5,c_41]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_2758,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_2743,c_1394]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_4326,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_4325,c_5,c_81,c_307,c_2758]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_6870,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_163,c_611,c_4326]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7195,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_6870,c_81]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7221,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_6870,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_151,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7264,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_6870,c_151]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7302,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_7264,c_81]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7362,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_7221,c_7302]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7394,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_7195,c_7362]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7,negated_conjecture,
% 43.28/6.02      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
% 43.28/6.02      inference(cnf_transformation,[],[f29]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_134,plain,
% 43.28/6.02      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_1,c_7]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_119609,plain,
% 43.28/6.02      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_7394,c_134]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_1305,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_141,c_81]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_1320,plain,
% 43.28/6.02      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_1305,c_59]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_13722,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_1320,c_141]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_6925,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_0,c_6870]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_512,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_108,c_6]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_527,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_512,c_6]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7631,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_6925,c_527]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7632,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_7631,c_81]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_13800,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_13722,c_7632]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_220,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_59,c_6]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_254,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_220,c_5]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_255,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_254,c_41]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_136,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_62,plain,
% 43.28/6.02      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_41,c_5]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_192,plain,
% 43.28/6.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_136,c_5,c_62]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_397,plain,
% 43.28/6.02      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_0,c_192]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_674,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_255,c_397]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_696,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_674,c_5]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_157,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_177,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_157,c_5]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_178,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_177,c_5,c_59]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_697,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_696,c_178]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_741,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_697,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_750,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_741,c_178]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_737,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_697,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_754,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = X0 ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_737,c_5,c_59]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_1467,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_0,c_754]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7181,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0))) = X0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_6870,c_1467]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7249,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_6870,c_141]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7326,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_7249,c_253]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7327,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_7326,c_81]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7415,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = X0 ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_7181,c_7327,c_7362]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_145,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_41,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_147,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_59,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_180,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_147,c_108]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_184,plain,
% 43.28/6.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_145,c_180]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_7416,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),X2)) = X0 ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_7415,c_184]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_8591,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = X0 ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_750,c_7416]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_9068,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_8591,c_6870]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_9127,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,X1) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_9068,c_81]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_9128,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_9127,c_81]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_9478,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X0))))) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_9128,c_151]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_9560,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X0))))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 43.28/6.02      inference(superposition,[status(thm)],[c_9128,c_1]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_9644,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X0))))) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 43.28/6.02      inference(light_normalisation,[status(thm)],[c_9560,c_7302]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_9657,plain,
% 43.28/6.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_9478,c_9644]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_13801,plain,
% 43.28/6.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_13800,c_187,c_9657]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_119610,plain,
% 43.28/6.02      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 43.28/6.02      inference(demodulation,[status(thm)],[c_119609,c_13801]) ).
% 43.28/6.02  
% 43.28/6.02  cnf(c_119611,plain,
% 43.28/6.02      ( $false ),
% 43.28/6.02      inference(equality_resolution_simp,[status(thm)],[c_119610]) ).
% 43.28/6.02  
% 43.28/6.02  
% 43.28/6.02  % SZS output end CNFRefutation for theBenchmark.p
% 43.28/6.02  
% 43.28/6.02  ------                               Statistics
% 43.28/6.02  
% 43.28/6.02  ------ General
% 43.28/6.02  
% 43.28/6.02  abstr_ref_over_cycles:                  0
% 43.28/6.02  abstr_ref_under_cycles:                 0
% 43.28/6.02  gc_basic_clause_elim:                   0
% 43.28/6.02  forced_gc_time:                         0
% 43.28/6.02  parsing_time:                           0.007
% 43.28/6.02  unif_index_cands_time:                  0.
% 43.28/6.02  unif_index_add_time:                    0.
% 43.28/6.02  orderings_time:                         0.
% 43.28/6.02  out_proof_time:                         0.011
% 43.28/6.02  total_time:                             5.182
% 43.28/6.02  num_of_symbols:                         40
% 43.28/6.02  num_of_terms:                           316696
% 43.28/6.02  
% 43.28/6.02  ------ Preprocessing
% 43.28/6.02  
% 43.28/6.02  num_of_splits:                          0
% 43.28/6.02  num_of_split_atoms:                     2
% 43.28/6.02  num_of_reused_defs:                     12
% 43.28/6.02  num_eq_ax_congr_red:                    1
% 43.28/6.02  num_of_sem_filtered_clauses:            0
% 43.28/6.02  num_of_subtypes:                        0
% 43.28/6.02  monotx_restored_types:                  0
% 43.28/6.02  sat_num_of_epr_types:                   0
% 43.28/6.02  sat_num_of_non_cyclic_types:            0
% 43.28/6.02  sat_guarded_non_collapsed_types:        0
% 43.28/6.02  num_pure_diseq_elim:                    0
% 43.28/6.02  simp_replaced_by:                       0
% 43.28/6.02  res_preprocessed:                       26
% 43.28/6.02  prep_upred:                             0
% 43.28/6.02  prep_unflattend:                        2
% 43.28/6.02  smt_new_axioms:                         0
% 43.28/6.02  pred_elim_cands:                        0
% 43.28/6.02  pred_elim:                              1
% 43.28/6.02  pred_elim_cl:                           1
% 43.28/6.02  pred_elim_cycles:                       2
% 43.28/6.02  merged_defs:                            0
% 43.28/6.02  merged_defs_ncl:                        0
% 43.28/6.02  bin_hyper_res:                          0
% 43.28/6.02  prep_cycles:                            3
% 43.28/6.02  pred_elim_time:                         0.
% 43.28/6.02  splitting_time:                         0.
% 43.28/6.02  sem_filter_time:                        0.
% 43.28/6.02  monotx_time:                            0.
% 43.28/6.02  subtype_inf_time:                       0.
% 43.28/6.02  
% 43.28/6.02  ------ Problem properties
% 43.28/6.02  
% 43.28/6.02  clauses:                                7
% 43.28/6.02  conjectures:                            1
% 43.28/6.02  epr:                                    0
% 43.28/6.02  horn:                                   7
% 43.28/6.02  ground:                                 1
% 43.28/6.02  unary:                                  7
% 43.28/6.02  binary:                                 0
% 43.28/6.02  lits:                                   7
% 43.28/6.02  lits_eq:                                7
% 43.28/6.02  fd_pure:                                0
% 43.28/6.02  fd_pseudo:                              0
% 43.28/6.02  fd_cond:                                0
% 43.28/6.02  fd_pseudo_cond:                         0
% 43.28/6.02  ac_symbols:                             0
% 43.28/6.02  
% 43.28/6.02  ------ Propositional Solver
% 43.28/6.02  
% 43.28/6.02  prop_solver_calls:                      17
% 43.28/6.02  prop_fast_solver_calls:                 67
% 43.28/6.02  smt_solver_calls:                       0
% 43.28/6.02  smt_fast_solver_calls:                  0
% 43.28/6.02  prop_num_of_clauses:                    352
% 43.28/6.02  prop_preprocess_simplified:             416
% 43.28/6.02  prop_fo_subsumed:                       0
% 43.28/6.02  prop_solver_time:                       0.
% 43.28/6.02  smt_solver_time:                        0.
% 43.28/6.02  smt_fast_solver_time:                   0.
% 43.28/6.02  prop_fast_solver_time:                  0.
% 43.28/6.02  prop_unsat_core_time:                   0.
% 43.28/6.02  
% 43.28/6.02  ------ QBF
% 43.28/6.02  
% 43.28/6.02  qbf_q_res:                              0
% 43.28/6.02  qbf_num_tautologies:                    0
% 43.28/6.02  qbf_prep_cycles:                        0
% 43.28/6.02  
% 43.28/6.02  ------ BMC1
% 43.28/6.02  
% 43.28/6.02  bmc1_current_bound:                     -1
% 43.28/6.02  bmc1_last_solved_bound:                 -1
% 43.28/6.02  bmc1_unsat_core_size:                   -1
% 43.28/6.02  bmc1_unsat_core_parents_size:           -1
% 43.28/6.02  bmc1_merge_next_fun:                    0
% 43.28/6.02  bmc1_unsat_core_clauses_time:           0.
% 43.28/6.02  
% 43.28/6.02  ------ Instantiation
% 43.28/6.02  
% 43.28/6.02  inst_num_of_clauses:                    0
% 43.28/6.02  inst_num_in_passive:                    0
% 43.28/6.02  inst_num_in_active:                     0
% 43.28/6.02  inst_num_in_unprocessed:                0
% 43.28/6.02  inst_num_of_loops:                      0
% 43.28/6.02  inst_num_of_learning_restarts:          0
% 43.28/6.02  inst_num_moves_active_passive:          0
% 43.28/6.02  inst_lit_activity:                      0
% 43.28/6.02  inst_lit_activity_moves:                0
% 43.28/6.02  inst_num_tautologies:                   0
% 43.28/6.02  inst_num_prop_implied:                  0
% 43.28/6.02  inst_num_existing_simplified:           0
% 43.28/6.02  inst_num_eq_res_simplified:             0
% 43.28/6.02  inst_num_child_elim:                    0
% 43.28/6.02  inst_num_of_dismatching_blockings:      0
% 43.28/6.02  inst_num_of_non_proper_insts:           0
% 43.28/6.02  inst_num_of_duplicates:                 0
% 43.28/6.02  inst_inst_num_from_inst_to_res:         0
% 43.28/6.02  inst_dismatching_checking_time:         0.
% 43.28/6.02  
% 43.28/6.02  ------ Resolution
% 43.28/6.02  
% 43.28/6.02  res_num_of_clauses:                     0
% 43.28/6.02  res_num_in_passive:                     0
% 43.28/6.02  res_num_in_active:                      0
% 43.28/6.02  res_num_of_loops:                       29
% 43.28/6.02  res_forward_subset_subsumed:            0
% 43.28/6.02  res_backward_subset_subsumed:           0
% 43.28/6.02  res_forward_subsumed:                   0
% 43.28/6.02  res_backward_subsumed:                  0
% 43.28/6.02  res_forward_subsumption_resolution:     0
% 43.28/6.02  res_backward_subsumption_resolution:    0
% 43.28/6.02  res_clause_to_clause_subsumption:       666630
% 43.28/6.02  res_orphan_elimination:                 0
% 43.28/6.02  res_tautology_del:                      0
% 43.28/6.02  res_num_eq_res_simplified:              0
% 43.28/6.02  res_num_sel_changes:                    0
% 43.28/6.02  res_moves_from_active_to_pass:          0
% 43.28/6.02  
% 43.28/6.02  ------ Superposition
% 43.28/6.02  
% 43.28/6.02  sup_time_total:                         0.
% 43.28/6.02  sup_time_generating:                    0.
% 43.28/6.02  sup_time_sim_full:                      0.
% 43.28/6.02  sup_time_sim_immed:                     0.
% 43.28/6.02  
% 43.28/6.02  sup_num_of_clauses:                     8575
% 43.28/6.02  sup_num_in_active:                      169
% 43.28/6.02  sup_num_in_passive:                     8406
% 43.28/6.02  sup_num_of_loops:                       192
% 43.28/6.02  sup_fw_superposition:                   36380
% 43.28/6.02  sup_bw_superposition:                   28670
% 43.28/6.02  sup_immediate_simplified:               36131
% 43.28/6.02  sup_given_eliminated:                   6
% 43.28/6.02  comparisons_done:                       0
% 43.28/6.02  comparisons_avoided:                    0
% 43.28/6.02  
% 43.28/6.02  ------ Simplifications
% 43.28/6.02  
% 43.28/6.02  
% 43.28/6.02  sim_fw_subset_subsumed:                 0
% 43.28/6.02  sim_bw_subset_subsumed:                 0
% 43.28/6.02  sim_fw_subsumed:                        3259
% 43.28/6.02  sim_bw_subsumed:                        110
% 43.28/6.02  sim_fw_subsumption_res:                 0
% 43.28/6.02  sim_bw_subsumption_res:                 0
% 43.28/6.02  sim_tautology_del:                      0
% 43.28/6.02  sim_eq_tautology_del:                   15122
% 43.28/6.02  sim_eq_res_simp:                        0
% 43.28/6.02  sim_fw_demodulated:                     40203
% 43.28/6.02  sim_bw_demodulated:                     358
% 43.28/6.02  sim_light_normalised:                   13787
% 43.28/6.02  sim_joinable_taut:                      0
% 43.28/6.02  sim_joinable_simp:                      0
% 43.28/6.02  sim_ac_normalised:                      0
% 43.28/6.02  sim_smt_subsumption:                    0
% 43.28/6.02  
%------------------------------------------------------------------------------
