%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:05 EST 2020

% Result     : Theorem 19.58s
% Output     : CNFRefutation 19.58s
% Verified   : 
% Statistics : Number of formulae       :  183 (152439 expanded)
%              Number of clauses        :  126 (45720 expanded)
%              Number of leaves         :   19 (38592 expanded)
%              Depth                    :   40
%              Number of atoms          :  211 (219556 expanded)
%              Number of equality atoms :  175 (136057 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f35,f35])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f36,f35,f35])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26])).

fof(f47,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f32,f35,f35,f35,f35])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f39,f35])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f49,f51])).

fof(f48,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(definition_unfolding,[],[f48,f49,f52,f52])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_497,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_498,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_707,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_497,c_498])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_500,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1498,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_497,c_500])).

cnf(c_3803,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_707,c_707,c_1498])).

cnf(c_3806,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_3803])).

cnf(c_5670,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_3806,c_1])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_715,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_1376,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_715])).

cnf(c_2067,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1376,c_0])).

cnf(c_2128,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2067,c_1376])).

cnf(c_2129,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_2128,c_2067])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_128,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_129,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_495,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_129])).

cnf(c_1500,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_495,c_500])).

cnf(c_709,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_495,c_498])).

cnf(c_656,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_497])).

cnf(c_967,plain,
    ( r1_tarski(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_656])).

cnf(c_1502,plain,
    ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_967,c_500])).

cnf(c_970,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_497])).

cnf(c_1503,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_970,c_500])).

cnf(c_1504,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1502,c_1503])).

cnf(c_1505,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1500,c_1504])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_501,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_4,c_7])).

cnf(c_1782,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_1505,c_501])).

cnf(c_1812,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_1782,c_1505])).

cnf(c_4266,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1,c_1812])).

cnf(c_4274,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1812,c_3803])).

cnf(c_4305,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_4274,c_1812])).

cnf(c_1501,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_656,c_500])).

cnf(c_4306,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4305,c_1501])).

cnf(c_4389,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4266,c_2129,c_4306])).

cnf(c_4273,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3803,c_1812])).

cnf(c_3831,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3803,c_1])).

cnf(c_3838,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3831,c_2129])).

cnf(c_4379,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_4273,c_3803,c_3838])).

cnf(c_4390,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4389,c_4379])).

cnf(c_4287,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))))) ),
    inference(superposition,[status(thm)],[c_1812,c_501])).

cnf(c_655,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_2862,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_501,c_655])).

cnf(c_925,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_656,c_498])).

cnf(c_926,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_925,c_7,c_501])).

cnf(c_1788,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_501,c_0])).

cnf(c_1801,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_1788,c_501])).

cnf(c_2910,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_2862,c_7,c_926,c_1501,c_1801])).

cnf(c_4367,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4287,c_1505,c_2129,c_2910,c_4306])).

cnf(c_4368,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_4367,c_2129,c_3803])).

cnf(c_4391,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4390,c_4368])).

cnf(c_4392,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4391,c_1505])).

cnf(c_5782,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5670,c_7,c_2129,c_4392])).

cnf(c_798,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_7921,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5782,c_798])).

cnf(c_5674,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_3806,c_3806])).

cnf(c_5774,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_5674,c_1498])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_827,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_8,c_11])).

cnf(c_838,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_11,c_9])).

cnf(c_657,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_840,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_838,c_657])).

cnf(c_942,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_827,c_0,c_840])).

cnf(c_4401,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4392,c_942])).

cnf(c_4403,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4401,c_8])).

cnf(c_5775,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5774,c_7,c_4403])).

cnf(c_5776,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_5775,c_4403])).

cnf(c_8285,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7921,c_5776])).

cnf(c_8286,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_8285,c_7,c_4403])).

cnf(c_24560,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_8286])).

cnf(c_43699,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2) ),
    inference(superposition,[status(thm)],[c_24560,c_798])).

cnf(c_4765,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_4403,c_501])).

cnf(c_4772,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) ),
    inference(demodulation,[status(thm)],[c_4765,c_4403])).

cnf(c_4426,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4392,c_1])).

cnf(c_4450,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4426,c_4392])).

cnf(c_4451,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4450,c_4306,c_4403])).

cnf(c_4773,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4772,c_7,c_4403,c_4451])).

cnf(c_8014,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) ),
    inference(superposition,[status(thm)],[c_798,c_1])).

cnf(c_8204,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_8014,c_7])).

cnf(c_43857,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))),X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_43699,c_7,c_4392,c_4773,c_8204])).

cnf(c_801,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_10761,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_801,c_5776])).

cnf(c_10769,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X3))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X3) ),
    inference(superposition,[status(thm)],[c_798,c_10761])).

cnf(c_11037,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X3) ),
    inference(light_normalisation,[status(thm)],[c_10769,c_7])).

cnf(c_1751,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_1,c_501])).

cnf(c_7993,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_798,c_497])).

cnf(c_8233,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7993,c_7])).

cnf(c_8645,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_8233,c_498])).

cnf(c_8646,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_8645,c_7,c_501])).

cnf(c_8647,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_8646,c_8204])).

cnf(c_11038,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))) ),
    inference(demodulation,[status(thm)],[c_11037,c_7,c_1751,c_8647])).

cnf(c_43858,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_43857,c_7,c_11038])).

cnf(c_8003,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_798,c_0])).

cnf(c_8222,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_8003,c_7])).

cnf(c_44590,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X3),X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_43858,c_8222])).

cnf(c_1487,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_657,c_715])).

cnf(c_45150,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X3),X0)))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_44590,c_1487])).

cnf(c_44549,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),X0)) ),
    inference(superposition,[status(thm)],[c_43858,c_655])).

cnf(c_44921,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),X0)) ),
    inference(light_normalisation,[status(thm)],[c_44549,c_4403])).

cnf(c_23423,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_10761,c_8222])).

cnf(c_44922,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_44921,c_4403,c_4451,c_8204,c_23423,c_43858])).

cnf(c_45151,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_45150,c_8,c_4392,c_44922])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_651,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_1,c_13])).

cnf(c_710,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_9,c_651])).

cnf(c_711,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_710,c_0])).

cnf(c_48561,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != sK1 ),
    inference(demodulation,[status(thm)],[c_45151,c_711])).

cnf(c_975,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_709,c_1])).

cnf(c_841,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_840,c_11])).

cnf(c_14404,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_975,c_841])).

cnf(c_1132,plain,
    ( k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_975,c_0])).

cnf(c_14536,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_14404,c_1132,c_1500])).

cnf(c_4192,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0) ),
    inference(superposition,[status(thm)],[c_1132,c_9])).

cnf(c_14537,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_14536,c_8,c_4192])).

cnf(c_48566,plain,
    ( sK1 != sK1 ),
    inference(light_normalisation,[status(thm)],[c_48561,c_14537])).

cnf(c_48567,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_48566])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:22:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.58/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.58/2.99  
% 19.58/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.58/2.99  
% 19.58/2.99  ------  iProver source info
% 19.58/2.99  
% 19.58/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.58/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.58/2.99  git: non_committed_changes: false
% 19.58/2.99  git: last_make_outside_of_git: false
% 19.58/2.99  
% 19.58/2.99  ------ 
% 19.58/2.99  
% 19.58/2.99  ------ Input Options
% 19.58/2.99  
% 19.58/2.99  --out_options                           all
% 19.58/2.99  --tptp_safe_out                         true
% 19.58/2.99  --problem_path                          ""
% 19.58/2.99  --include_path                          ""
% 19.58/2.99  --clausifier                            res/vclausify_rel
% 19.58/2.99  --clausifier_options                    ""
% 19.58/2.99  --stdin                                 false
% 19.58/2.99  --stats_out                             all
% 19.58/2.99  
% 19.58/2.99  ------ General Options
% 19.58/2.99  
% 19.58/2.99  --fof                                   false
% 19.58/2.99  --time_out_real                         305.
% 19.58/2.99  --time_out_virtual                      -1.
% 19.58/2.99  --symbol_type_check                     false
% 19.58/2.99  --clausify_out                          false
% 19.58/2.99  --sig_cnt_out                           false
% 19.58/2.99  --trig_cnt_out                          false
% 19.58/2.99  --trig_cnt_out_tolerance                1.
% 19.58/2.99  --trig_cnt_out_sk_spl                   false
% 19.58/2.99  --abstr_cl_out                          false
% 19.58/2.99  
% 19.58/2.99  ------ Global Options
% 19.58/2.99  
% 19.58/2.99  --schedule                              default
% 19.58/2.99  --add_important_lit                     false
% 19.58/2.99  --prop_solver_per_cl                    1000
% 19.58/2.99  --min_unsat_core                        false
% 19.58/2.99  --soft_assumptions                      false
% 19.58/2.99  --soft_lemma_size                       3
% 19.58/2.99  --prop_impl_unit_size                   0
% 19.58/2.99  --prop_impl_unit                        []
% 19.58/2.99  --share_sel_clauses                     true
% 19.58/2.99  --reset_solvers                         false
% 19.58/2.99  --bc_imp_inh                            [conj_cone]
% 19.58/2.99  --conj_cone_tolerance                   3.
% 19.58/2.99  --extra_neg_conj                        none
% 19.58/2.99  --large_theory_mode                     true
% 19.58/2.99  --prolific_symb_bound                   200
% 19.58/2.99  --lt_threshold                          2000
% 19.58/2.99  --clause_weak_htbl                      true
% 19.58/2.99  --gc_record_bc_elim                     false
% 19.58/2.99  
% 19.58/2.99  ------ Preprocessing Options
% 19.58/2.99  
% 19.58/2.99  --preprocessing_flag                    true
% 19.58/2.99  --time_out_prep_mult                    0.1
% 19.58/2.99  --splitting_mode                        input
% 19.58/2.99  --splitting_grd                         true
% 19.58/2.99  --splitting_cvd                         false
% 19.58/2.99  --splitting_cvd_svl                     false
% 19.58/2.99  --splitting_nvd                         32
% 19.58/2.99  --sub_typing                            true
% 19.58/2.99  --prep_gs_sim                           true
% 19.58/2.99  --prep_unflatten                        true
% 19.58/2.99  --prep_res_sim                          true
% 19.58/2.99  --prep_upred                            true
% 19.58/2.99  --prep_sem_filter                       exhaustive
% 19.58/2.99  --prep_sem_filter_out                   false
% 19.58/2.99  --pred_elim                             true
% 19.58/2.99  --res_sim_input                         true
% 19.58/2.99  --eq_ax_congr_red                       true
% 19.58/2.99  --pure_diseq_elim                       true
% 19.58/2.99  --brand_transform                       false
% 19.58/2.99  --non_eq_to_eq                          false
% 19.58/2.99  --prep_def_merge                        true
% 19.58/2.99  --prep_def_merge_prop_impl              false
% 19.58/2.99  --prep_def_merge_mbd                    true
% 19.58/2.99  --prep_def_merge_tr_red                 false
% 19.58/2.99  --prep_def_merge_tr_cl                  false
% 19.58/2.99  --smt_preprocessing                     true
% 19.58/2.99  --smt_ac_axioms                         fast
% 19.58/2.99  --preprocessed_out                      false
% 19.58/2.99  --preprocessed_stats                    false
% 19.58/2.99  
% 19.58/2.99  ------ Abstraction refinement Options
% 19.58/2.99  
% 19.58/2.99  --abstr_ref                             []
% 19.58/2.99  --abstr_ref_prep                        false
% 19.58/2.99  --abstr_ref_until_sat                   false
% 19.58/2.99  --abstr_ref_sig_restrict                funpre
% 19.58/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.58/2.99  --abstr_ref_under                       []
% 19.58/2.99  
% 19.58/2.99  ------ SAT Options
% 19.58/2.99  
% 19.58/2.99  --sat_mode                              false
% 19.58/2.99  --sat_fm_restart_options                ""
% 19.58/2.99  --sat_gr_def                            false
% 19.58/2.99  --sat_epr_types                         true
% 19.58/2.99  --sat_non_cyclic_types                  false
% 19.58/2.99  --sat_finite_models                     false
% 19.58/2.99  --sat_fm_lemmas                         false
% 19.58/2.99  --sat_fm_prep                           false
% 19.58/2.99  --sat_fm_uc_incr                        true
% 19.58/2.99  --sat_out_model                         small
% 19.58/2.99  --sat_out_clauses                       false
% 19.58/2.99  
% 19.58/2.99  ------ QBF Options
% 19.58/2.99  
% 19.58/2.99  --qbf_mode                              false
% 19.58/2.99  --qbf_elim_univ                         false
% 19.58/2.99  --qbf_dom_inst                          none
% 19.58/2.99  --qbf_dom_pre_inst                      false
% 19.58/2.99  --qbf_sk_in                             false
% 19.58/2.99  --qbf_pred_elim                         true
% 19.58/2.99  --qbf_split                             512
% 19.58/2.99  
% 19.58/2.99  ------ BMC1 Options
% 19.58/2.99  
% 19.58/2.99  --bmc1_incremental                      false
% 19.58/2.99  --bmc1_axioms                           reachable_all
% 19.58/2.99  --bmc1_min_bound                        0
% 19.58/2.99  --bmc1_max_bound                        -1
% 19.58/2.99  --bmc1_max_bound_default                -1
% 19.58/2.99  --bmc1_symbol_reachability              true
% 19.58/2.99  --bmc1_property_lemmas                  false
% 19.58/2.99  --bmc1_k_induction                      false
% 19.58/2.99  --bmc1_non_equiv_states                 false
% 19.58/2.99  --bmc1_deadlock                         false
% 19.58/2.99  --bmc1_ucm                              false
% 19.58/2.99  --bmc1_add_unsat_core                   none
% 19.58/2.99  --bmc1_unsat_core_children              false
% 19.58/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.58/2.99  --bmc1_out_stat                         full
% 19.58/2.99  --bmc1_ground_init                      false
% 19.58/2.99  --bmc1_pre_inst_next_state              false
% 19.58/2.99  --bmc1_pre_inst_state                   false
% 19.58/2.99  --bmc1_pre_inst_reach_state             false
% 19.58/2.99  --bmc1_out_unsat_core                   false
% 19.58/2.99  --bmc1_aig_witness_out                  false
% 19.58/2.99  --bmc1_verbose                          false
% 19.58/2.99  --bmc1_dump_clauses_tptp                false
% 19.58/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.58/2.99  --bmc1_dump_file                        -
% 19.58/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.58/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.58/2.99  --bmc1_ucm_extend_mode                  1
% 19.58/2.99  --bmc1_ucm_init_mode                    2
% 19.58/2.99  --bmc1_ucm_cone_mode                    none
% 19.58/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.58/2.99  --bmc1_ucm_relax_model                  4
% 19.58/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.58/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.58/2.99  --bmc1_ucm_layered_model                none
% 19.58/2.99  --bmc1_ucm_max_lemma_size               10
% 19.58/2.99  
% 19.58/2.99  ------ AIG Options
% 19.58/2.99  
% 19.58/2.99  --aig_mode                              false
% 19.58/2.99  
% 19.58/2.99  ------ Instantiation Options
% 19.58/2.99  
% 19.58/2.99  --instantiation_flag                    true
% 19.58/2.99  --inst_sos_flag                         true
% 19.58/2.99  --inst_sos_phase                        true
% 19.58/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.58/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.58/2.99  --inst_lit_sel_side                     num_symb
% 19.58/2.99  --inst_solver_per_active                1400
% 19.58/2.99  --inst_solver_calls_frac                1.
% 19.58/2.99  --inst_passive_queue_type               priority_queues
% 19.58/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.58/2.99  --inst_passive_queues_freq              [25;2]
% 19.58/2.99  --inst_dismatching                      true
% 19.58/2.99  --inst_eager_unprocessed_to_passive     true
% 19.58/2.99  --inst_prop_sim_given                   true
% 19.58/2.99  --inst_prop_sim_new                     false
% 19.58/2.99  --inst_subs_new                         false
% 19.58/2.99  --inst_eq_res_simp                      false
% 19.58/2.99  --inst_subs_given                       false
% 19.58/2.99  --inst_orphan_elimination               true
% 19.58/2.99  --inst_learning_loop_flag               true
% 19.58/2.99  --inst_learning_start                   3000
% 19.58/2.99  --inst_learning_factor                  2
% 19.58/2.99  --inst_start_prop_sim_after_learn       3
% 19.58/2.99  --inst_sel_renew                        solver
% 19.58/2.99  --inst_lit_activity_flag                true
% 19.58/2.99  --inst_restr_to_given                   false
% 19.58/2.99  --inst_activity_threshold               500
% 19.58/2.99  --inst_out_proof                        true
% 19.58/2.99  
% 19.58/2.99  ------ Resolution Options
% 19.58/2.99  
% 19.58/2.99  --resolution_flag                       true
% 19.58/2.99  --res_lit_sel                           adaptive
% 19.58/2.99  --res_lit_sel_side                      none
% 19.58/2.99  --res_ordering                          kbo
% 19.58/2.99  --res_to_prop_solver                    active
% 19.58/2.99  --res_prop_simpl_new                    false
% 19.58/2.99  --res_prop_simpl_given                  true
% 19.58/2.99  --res_passive_queue_type                priority_queues
% 19.58/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.58/2.99  --res_passive_queues_freq               [15;5]
% 19.58/2.99  --res_forward_subs                      full
% 19.58/2.99  --res_backward_subs                     full
% 19.58/2.99  --res_forward_subs_resolution           true
% 19.58/2.99  --res_backward_subs_resolution          true
% 19.58/2.99  --res_orphan_elimination                true
% 19.58/2.99  --res_time_limit                        2.
% 19.58/2.99  --res_out_proof                         true
% 19.58/2.99  
% 19.58/2.99  ------ Superposition Options
% 19.58/2.99  
% 19.58/2.99  --superposition_flag                    true
% 19.58/2.99  --sup_passive_queue_type                priority_queues
% 19.58/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.58/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.58/2.99  --demod_completeness_check              fast
% 19.58/2.99  --demod_use_ground                      true
% 19.58/2.99  --sup_to_prop_solver                    passive
% 19.58/2.99  --sup_prop_simpl_new                    true
% 19.58/2.99  --sup_prop_simpl_given                  true
% 19.58/2.99  --sup_fun_splitting                     true
% 19.58/2.99  --sup_smt_interval                      50000
% 19.58/2.99  
% 19.58/2.99  ------ Superposition Simplification Setup
% 19.58/2.99  
% 19.58/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.58/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.58/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.58/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.58/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.58/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.58/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.58/2.99  --sup_immed_triv                        [TrivRules]
% 19.58/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.58/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.58/2.99  --sup_immed_bw_main                     []
% 19.58/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.58/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.58/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.58/2.99  --sup_input_bw                          []
% 19.58/2.99  
% 19.58/2.99  ------ Combination Options
% 19.58/2.99  
% 19.58/2.99  --comb_res_mult                         3
% 19.58/2.99  --comb_sup_mult                         2
% 19.58/2.99  --comb_inst_mult                        10
% 19.58/2.99  
% 19.58/2.99  ------ Debug Options
% 19.58/2.99  
% 19.58/2.99  --dbg_backtrace                         false
% 19.58/2.99  --dbg_dump_prop_clauses                 false
% 19.58/2.99  --dbg_dump_prop_clauses_file            -
% 19.58/2.99  --dbg_out_stat                          false
% 19.58/2.99  ------ Parsing...
% 19.58/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.58/2.99  
% 19.58/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.58/2.99  
% 19.58/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.58/2.99  
% 19.58/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.58/2.99  ------ Proving...
% 19.58/2.99  ------ Problem Properties 
% 19.58/2.99  
% 19.58/2.99  
% 19.58/2.99  clauses                                 14
% 19.58/2.99  conjectures                             1
% 19.58/2.99  EPR                                     0
% 19.58/2.99  Horn                                    14
% 19.58/2.99  unary                                   11
% 19.58/2.99  binary                                  3
% 19.58/2.99  lits                                    17
% 19.58/2.99  lits eq                                 11
% 19.58/2.99  fd_pure                                 0
% 19.58/2.99  fd_pseudo                               0
% 19.58/2.99  fd_cond                                 0
% 19.58/2.99  fd_pseudo_cond                          0
% 19.58/2.99  AC symbols                              0
% 19.58/2.99  
% 19.58/2.99  ------ Schedule dynamic 5 is on 
% 19.58/2.99  
% 19.58/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.58/2.99  
% 19.58/2.99  
% 19.58/2.99  ------ 
% 19.58/2.99  Current options:
% 19.58/2.99  ------ 
% 19.58/2.99  
% 19.58/2.99  ------ Input Options
% 19.58/2.99  
% 19.58/2.99  --out_options                           all
% 19.58/2.99  --tptp_safe_out                         true
% 19.58/2.99  --problem_path                          ""
% 19.58/2.99  --include_path                          ""
% 19.58/2.99  --clausifier                            res/vclausify_rel
% 19.58/2.99  --clausifier_options                    ""
% 19.58/2.99  --stdin                                 false
% 19.58/2.99  --stats_out                             all
% 19.58/2.99  
% 19.58/2.99  ------ General Options
% 19.58/2.99  
% 19.58/2.99  --fof                                   false
% 19.58/2.99  --time_out_real                         305.
% 19.58/2.99  --time_out_virtual                      -1.
% 19.58/2.99  --symbol_type_check                     false
% 19.58/2.99  --clausify_out                          false
% 19.58/2.99  --sig_cnt_out                           false
% 19.58/2.99  --trig_cnt_out                          false
% 19.58/2.99  --trig_cnt_out_tolerance                1.
% 19.58/2.99  --trig_cnt_out_sk_spl                   false
% 19.58/2.99  --abstr_cl_out                          false
% 19.58/2.99  
% 19.58/2.99  ------ Global Options
% 19.58/2.99  
% 19.58/2.99  --schedule                              default
% 19.58/2.99  --add_important_lit                     false
% 19.58/2.99  --prop_solver_per_cl                    1000
% 19.58/2.99  --min_unsat_core                        false
% 19.58/2.99  --soft_assumptions                      false
% 19.58/2.99  --soft_lemma_size                       3
% 19.58/2.99  --prop_impl_unit_size                   0
% 19.58/2.99  --prop_impl_unit                        []
% 19.58/2.99  --share_sel_clauses                     true
% 19.58/2.99  --reset_solvers                         false
% 19.58/2.99  --bc_imp_inh                            [conj_cone]
% 19.58/2.99  --conj_cone_tolerance                   3.
% 19.58/2.99  --extra_neg_conj                        none
% 19.58/2.99  --large_theory_mode                     true
% 19.58/2.99  --prolific_symb_bound                   200
% 19.58/2.99  --lt_threshold                          2000
% 19.58/2.99  --clause_weak_htbl                      true
% 19.58/2.99  --gc_record_bc_elim                     false
% 19.58/2.99  
% 19.58/2.99  ------ Preprocessing Options
% 19.58/2.99  
% 19.58/2.99  --preprocessing_flag                    true
% 19.58/2.99  --time_out_prep_mult                    0.1
% 19.58/2.99  --splitting_mode                        input
% 19.58/2.99  --splitting_grd                         true
% 19.58/2.99  --splitting_cvd                         false
% 19.58/2.99  --splitting_cvd_svl                     false
% 19.58/2.99  --splitting_nvd                         32
% 19.58/2.99  --sub_typing                            true
% 19.58/2.99  --prep_gs_sim                           true
% 19.58/2.99  --prep_unflatten                        true
% 19.58/2.99  --prep_res_sim                          true
% 19.58/2.99  --prep_upred                            true
% 19.58/2.99  --prep_sem_filter                       exhaustive
% 19.58/2.99  --prep_sem_filter_out                   false
% 19.58/2.99  --pred_elim                             true
% 19.58/2.99  --res_sim_input                         true
% 19.58/2.99  --eq_ax_congr_red                       true
% 19.58/2.99  --pure_diseq_elim                       true
% 19.58/2.99  --brand_transform                       false
% 19.58/2.99  --non_eq_to_eq                          false
% 19.58/2.99  --prep_def_merge                        true
% 19.58/2.99  --prep_def_merge_prop_impl              false
% 19.58/2.99  --prep_def_merge_mbd                    true
% 19.58/2.99  --prep_def_merge_tr_red                 false
% 19.58/2.99  --prep_def_merge_tr_cl                  false
% 19.58/2.99  --smt_preprocessing                     true
% 19.58/2.99  --smt_ac_axioms                         fast
% 19.58/2.99  --preprocessed_out                      false
% 19.58/2.99  --preprocessed_stats                    false
% 19.58/2.99  
% 19.58/2.99  ------ Abstraction refinement Options
% 19.58/2.99  
% 19.58/2.99  --abstr_ref                             []
% 19.58/2.99  --abstr_ref_prep                        false
% 19.58/2.99  --abstr_ref_until_sat                   false
% 19.58/2.99  --abstr_ref_sig_restrict                funpre
% 19.58/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.58/2.99  --abstr_ref_under                       []
% 19.58/2.99  
% 19.58/2.99  ------ SAT Options
% 19.58/2.99  
% 19.58/2.99  --sat_mode                              false
% 19.58/2.99  --sat_fm_restart_options                ""
% 19.58/2.99  --sat_gr_def                            false
% 19.58/2.99  --sat_epr_types                         true
% 19.58/2.99  --sat_non_cyclic_types                  false
% 19.58/2.99  --sat_finite_models                     false
% 19.58/2.99  --sat_fm_lemmas                         false
% 19.58/2.99  --sat_fm_prep                           false
% 19.58/2.99  --sat_fm_uc_incr                        true
% 19.58/2.99  --sat_out_model                         small
% 19.58/2.99  --sat_out_clauses                       false
% 19.58/2.99  
% 19.58/2.99  ------ QBF Options
% 19.58/2.99  
% 19.58/2.99  --qbf_mode                              false
% 19.58/2.99  --qbf_elim_univ                         false
% 19.58/2.99  --qbf_dom_inst                          none
% 19.58/2.99  --qbf_dom_pre_inst                      false
% 19.58/2.99  --qbf_sk_in                             false
% 19.58/2.99  --qbf_pred_elim                         true
% 19.58/2.99  --qbf_split                             512
% 19.58/2.99  
% 19.58/2.99  ------ BMC1 Options
% 19.58/2.99  
% 19.58/2.99  --bmc1_incremental                      false
% 19.58/2.99  --bmc1_axioms                           reachable_all
% 19.58/2.99  --bmc1_min_bound                        0
% 19.58/2.99  --bmc1_max_bound                        -1
% 19.58/2.99  --bmc1_max_bound_default                -1
% 19.58/2.99  --bmc1_symbol_reachability              true
% 19.58/2.99  --bmc1_property_lemmas                  false
% 19.58/2.99  --bmc1_k_induction                      false
% 19.58/2.99  --bmc1_non_equiv_states                 false
% 19.58/2.99  --bmc1_deadlock                         false
% 19.58/2.99  --bmc1_ucm                              false
% 19.58/2.99  --bmc1_add_unsat_core                   none
% 19.58/2.99  --bmc1_unsat_core_children              false
% 19.58/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.58/2.99  --bmc1_out_stat                         full
% 19.58/2.99  --bmc1_ground_init                      false
% 19.58/2.99  --bmc1_pre_inst_next_state              false
% 19.58/2.99  --bmc1_pre_inst_state                   false
% 19.58/2.99  --bmc1_pre_inst_reach_state             false
% 19.58/2.99  --bmc1_out_unsat_core                   false
% 19.58/2.99  --bmc1_aig_witness_out                  false
% 19.58/2.99  --bmc1_verbose                          false
% 19.58/2.99  --bmc1_dump_clauses_tptp                false
% 19.58/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.58/2.99  --bmc1_dump_file                        -
% 19.58/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.58/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.58/2.99  --bmc1_ucm_extend_mode                  1
% 19.58/2.99  --bmc1_ucm_init_mode                    2
% 19.58/2.99  --bmc1_ucm_cone_mode                    none
% 19.58/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.58/2.99  --bmc1_ucm_relax_model                  4
% 19.58/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.58/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.58/2.99  --bmc1_ucm_layered_model                none
% 19.58/2.99  --bmc1_ucm_max_lemma_size               10
% 19.58/2.99  
% 19.58/2.99  ------ AIG Options
% 19.58/2.99  
% 19.58/2.99  --aig_mode                              false
% 19.58/2.99  
% 19.58/2.99  ------ Instantiation Options
% 19.58/2.99  
% 19.58/2.99  --instantiation_flag                    true
% 19.58/2.99  --inst_sos_flag                         true
% 19.58/2.99  --inst_sos_phase                        true
% 19.58/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.58/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.58/2.99  --inst_lit_sel_side                     none
% 19.58/2.99  --inst_solver_per_active                1400
% 19.58/2.99  --inst_solver_calls_frac                1.
% 19.58/2.99  --inst_passive_queue_type               priority_queues
% 19.58/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.58/2.99  --inst_passive_queues_freq              [25;2]
% 19.58/2.99  --inst_dismatching                      true
% 19.58/2.99  --inst_eager_unprocessed_to_passive     true
% 19.58/2.99  --inst_prop_sim_given                   true
% 19.58/2.99  --inst_prop_sim_new                     false
% 19.58/2.99  --inst_subs_new                         false
% 19.58/2.99  --inst_eq_res_simp                      false
% 19.58/2.99  --inst_subs_given                       false
% 19.58/2.99  --inst_orphan_elimination               true
% 19.58/2.99  --inst_learning_loop_flag               true
% 19.58/2.99  --inst_learning_start                   3000
% 19.58/2.99  --inst_learning_factor                  2
% 19.58/2.99  --inst_start_prop_sim_after_learn       3
% 19.58/2.99  --inst_sel_renew                        solver
% 19.58/2.99  --inst_lit_activity_flag                true
% 19.58/2.99  --inst_restr_to_given                   false
% 19.58/2.99  --inst_activity_threshold               500
% 19.58/2.99  --inst_out_proof                        true
% 19.58/2.99  
% 19.58/2.99  ------ Resolution Options
% 19.58/2.99  
% 19.58/2.99  --resolution_flag                       false
% 19.58/2.99  --res_lit_sel                           adaptive
% 19.58/2.99  --res_lit_sel_side                      none
% 19.58/2.99  --res_ordering                          kbo
% 19.58/2.99  --res_to_prop_solver                    active
% 19.58/2.99  --res_prop_simpl_new                    false
% 19.58/2.99  --res_prop_simpl_given                  true
% 19.58/2.99  --res_passive_queue_type                priority_queues
% 19.58/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.58/2.99  --res_passive_queues_freq               [15;5]
% 19.58/2.99  --res_forward_subs                      full
% 19.58/2.99  --res_backward_subs                     full
% 19.58/2.99  --res_forward_subs_resolution           true
% 19.58/2.99  --res_backward_subs_resolution          true
% 19.58/2.99  --res_orphan_elimination                true
% 19.58/2.99  --res_time_limit                        2.
% 19.58/2.99  --res_out_proof                         true
% 19.58/2.99  
% 19.58/2.99  ------ Superposition Options
% 19.58/2.99  
% 19.58/2.99  --superposition_flag                    true
% 19.58/2.99  --sup_passive_queue_type                priority_queues
% 19.58/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.58/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.58/2.99  --demod_completeness_check              fast
% 19.58/2.99  --demod_use_ground                      true
% 19.58/2.99  --sup_to_prop_solver                    passive
% 19.58/2.99  --sup_prop_simpl_new                    true
% 19.58/2.99  --sup_prop_simpl_given                  true
% 19.58/2.99  --sup_fun_splitting                     true
% 19.58/2.99  --sup_smt_interval                      50000
% 19.58/2.99  
% 19.58/2.99  ------ Superposition Simplification Setup
% 19.58/2.99  
% 19.58/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.58/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.58/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.58/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.58/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.58/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.58/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.58/2.99  --sup_immed_triv                        [TrivRules]
% 19.58/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.58/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.58/2.99  --sup_immed_bw_main                     []
% 19.58/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.58/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.58/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.58/2.99  --sup_input_bw                          []
% 19.58/2.99  
% 19.58/2.99  ------ Combination Options
% 19.58/2.99  
% 19.58/2.99  --comb_res_mult                         3
% 19.58/2.99  --comb_sup_mult                         2
% 19.58/2.99  --comb_inst_mult                        10
% 19.58/2.99  
% 19.58/2.99  ------ Debug Options
% 19.58/2.99  
% 19.58/2.99  --dbg_backtrace                         false
% 19.58/2.99  --dbg_dump_prop_clauses                 false
% 19.58/2.99  --dbg_dump_prop_clauses_file            -
% 19.58/2.99  --dbg_out_stat                          false
% 19.58/2.99  
% 19.58/2.99  
% 19.58/2.99  
% 19.58/2.99  
% 19.58/2.99  ------ Proving...
% 19.58/2.99  
% 19.58/2.99  
% 19.58/2.99  % SZS status Theorem for theBenchmark.p
% 19.58/2.99  
% 19.58/2.99   Resolution empty clause
% 19.58/2.99  
% 19.58/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.58/2.99  
% 19.58/2.99  fof(f1,axiom,(
% 19.58/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f28,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f1])).
% 19.58/2.99  
% 19.58/2.99  fof(f7,axiom,(
% 19.58/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f35,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.58/2.99    inference(cnf_transformation,[],[f7])).
% 19.58/2.99  
% 19.58/2.99  fof(f54,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 19.58/2.99    inference(definition_unfolding,[],[f28,f35,f35])).
% 19.58/2.99  
% 19.58/2.99  fof(f6,axiom,(
% 19.58/2.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f34,plain,(
% 19.58/2.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f6])).
% 19.58/2.99  
% 19.58/2.99  fof(f5,axiom,(
% 19.58/2.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f22,plain,(
% 19.58/2.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.58/2.99    inference(ennf_transformation,[],[f5])).
% 19.58/2.99  
% 19.58/2.99  fof(f33,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f22])).
% 19.58/2.99  
% 19.58/2.99  fof(f56,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 19.58/2.99    inference(definition_unfolding,[],[f33,f35])).
% 19.58/2.99  
% 19.58/2.99  fof(f2,axiom,(
% 19.58/2.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f25,plain,(
% 19.58/2.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 19.58/2.99    inference(nnf_transformation,[],[f2])).
% 19.58/2.99  
% 19.58/2.99  fof(f30,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f25])).
% 19.58/2.99  
% 19.58/2.99  fof(f8,axiom,(
% 19.58/2.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f36,plain,(
% 19.58/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f8])).
% 19.58/2.99  
% 19.58/2.99  fof(f57,plain,(
% 19.58/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 19.58/2.99    inference(definition_unfolding,[],[f36,f35,f35])).
% 19.58/2.99  
% 19.58/2.99  fof(f3,axiom,(
% 19.58/2.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f31,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.58/2.99    inference(cnf_transformation,[],[f3])).
% 19.58/2.99  
% 19.58/2.99  fof(f53,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 19.58/2.99    inference(definition_unfolding,[],[f31,f35])).
% 19.58/2.99  
% 19.58/2.99  fof(f9,axiom,(
% 19.58/2.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f37,plain,(
% 19.58/2.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.58/2.99    inference(cnf_transformation,[],[f9])).
% 19.58/2.99  
% 19.58/2.99  fof(f10,axiom,(
% 19.58/2.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f38,plain,(
% 19.58/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f10])).
% 19.58/2.99  
% 19.58/2.99  fof(f16,axiom,(
% 19.58/2.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f21,plain,(
% 19.58/2.99    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 19.58/2.99    inference(unused_predicate_definition_removal,[],[f16])).
% 19.58/2.99  
% 19.58/2.99  fof(f23,plain,(
% 19.58/2.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 19.58/2.99    inference(ennf_transformation,[],[f21])).
% 19.58/2.99  
% 19.58/2.99  fof(f44,plain,(
% 19.58/2.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f23])).
% 19.58/2.99  
% 19.58/2.99  fof(f12,axiom,(
% 19.58/2.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f40,plain,(
% 19.58/2.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f12])).
% 19.58/2.99  
% 19.58/2.99  fof(f13,axiom,(
% 19.58/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f41,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f13])).
% 19.58/2.99  
% 19.58/2.99  fof(f14,axiom,(
% 19.58/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f42,plain,(
% 19.58/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f14])).
% 19.58/2.99  
% 19.58/2.99  fof(f15,axiom,(
% 19.58/2.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f43,plain,(
% 19.58/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f15])).
% 19.58/2.99  
% 19.58/2.99  fof(f50,plain,(
% 19.58/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 19.58/2.99    inference(definition_unfolding,[],[f42,f43])).
% 19.58/2.99  
% 19.58/2.99  fof(f51,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 19.58/2.99    inference(definition_unfolding,[],[f41,f50])).
% 19.58/2.99  
% 19.58/2.99  fof(f52,plain,(
% 19.58/2.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 19.58/2.99    inference(definition_unfolding,[],[f40,f51])).
% 19.58/2.99  
% 19.58/2.99  fof(f58,plain,(
% 19.58/2.99    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 19.58/2.99    inference(definition_unfolding,[],[f44,f52])).
% 19.58/2.99  
% 19.58/2.99  fof(f19,conjecture,(
% 19.58/2.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f20,negated_conjecture,(
% 19.58/2.99    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 19.58/2.99    inference(negated_conjecture,[],[f19])).
% 19.58/2.99  
% 19.58/2.99  fof(f24,plain,(
% 19.58/2.99    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 19.58/2.99    inference(ennf_transformation,[],[f20])).
% 19.58/2.99  
% 19.58/2.99  fof(f26,plain,(
% 19.58/2.99    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1))),
% 19.58/2.99    introduced(choice_axiom,[])).
% 19.58/2.99  
% 19.58/2.99  fof(f27,plain,(
% 19.58/2.99    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1)),
% 19.58/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26])).
% 19.58/2.99  
% 19.58/2.99  fof(f47,plain,(
% 19.58/2.99    r2_hidden(sK0,sK1)),
% 19.58/2.99    inference(cnf_transformation,[],[f27])).
% 19.58/2.99  
% 19.58/2.99  fof(f4,axiom,(
% 19.58/2.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f32,plain,(
% 19.58/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f4])).
% 19.58/2.99  
% 19.58/2.99  fof(f55,plain,(
% 19.58/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 19.58/2.99    inference(definition_unfolding,[],[f32,f35,f35,f35,f35])).
% 19.58/2.99  
% 19.58/2.99  fof(f17,axiom,(
% 19.58/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f45,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.58/2.99    inference(cnf_transformation,[],[f17])).
% 19.58/2.99  
% 19.58/2.99  fof(f11,axiom,(
% 19.58/2.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 19.58/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.58/2.99  
% 19.58/2.99  fof(f39,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 19.58/2.99    inference(cnf_transformation,[],[f11])).
% 19.58/2.99  
% 19.58/2.99  fof(f49,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 19.58/2.99    inference(definition_unfolding,[],[f39,f35])).
% 19.58/2.99  
% 19.58/2.99  fof(f59,plain,(
% 19.58/2.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 19.58/2.99    inference(definition_unfolding,[],[f45,f49,f51])).
% 19.58/2.99  
% 19.58/2.99  fof(f48,plain,(
% 19.58/2.99    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1),
% 19.58/2.99    inference(cnf_transformation,[],[f27])).
% 19.58/2.99  
% 19.58/2.99  fof(f60,plain,(
% 19.58/2.99    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1),
% 19.58/2.99    inference(definition_unfolding,[],[f48,f49,f52,f52])).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.58/2.99      inference(cnf_transformation,[],[f54]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_6,plain,
% 19.58/2.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 19.58/2.99      inference(cnf_transformation,[],[f34]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_497,plain,
% 19.58/2.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 19.58/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_5,plain,
% 19.58/2.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 19.58/2.99      inference(cnf_transformation,[],[f56]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_498,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 19.58/2.99      | r1_tarski(X0,X1) != iProver_top ),
% 19.58/2.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_707,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_497,c_498]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_2,plain,
% 19.58/2.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 19.58/2.99      inference(cnf_transformation,[],[f30]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_500,plain,
% 19.58/2.99      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 19.58/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1498,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_497,c_500]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_3803,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_707,c_707,c_1498]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_3806,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1,c_3803]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_5670,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_3806,c_1]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_7,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 19.58/2.99      inference(cnf_transformation,[],[f57]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_0,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.58/2.99      inference(cnf_transformation,[],[f53]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.58/2.99      inference(cnf_transformation,[],[f37]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_9,plain,
% 19.58/2.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.58/2.99      inference(cnf_transformation,[],[f38]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_715,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1376,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_0,c_715]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_2067,plain,
% 19.58/2.99      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1376,c_0]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_2128,plain,
% 19.58/2.99      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_2067,c_1376]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_2129,plain,
% 19.58/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_2128,c_2067]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_10,plain,
% 19.58/2.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 19.58/2.99      inference(cnf_transformation,[],[f58]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_14,negated_conjecture,
% 19.58/2.99      ( r2_hidden(sK0,sK1) ),
% 19.58/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_128,plain,
% 19.58/2.99      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | sK0 != X0 | sK1 != X1 ),
% 19.58/2.99      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_129,plain,
% 19.58/2.99      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 19.58/2.99      inference(unflattening,[status(thm)],[c_128]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_495,plain,
% 19.58/2.99      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 19.58/2.99      inference(predicate_to_equality,[status(thm)],[c_129]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1500,plain,
% 19.58/2.99      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k1_xboole_0 ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_495,c_500]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_709,plain,
% 19.58/2.99      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_495,c_498]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_656,plain,
% 19.58/2.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1,c_497]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_967,plain,
% 19.58/2.99      ( r1_tarski(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_709,c_656]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1502,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_967,c_500]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_970,plain,
% 19.58/2.99      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_709,c_497]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1503,plain,
% 19.58/2.99      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_970,c_500]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1504,plain,
% 19.58/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_1502,c_1503]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1505,plain,
% 19.58/2.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_1500,c_1504]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 19.58/2.99      inference(cnf_transformation,[],[f55]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_501,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_4,c_7]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1782,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1505,c_501]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1812,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_1782,c_1505]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4266,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1,c_1812]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4274,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1812,c_3803]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4305,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_4274,c_1812]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1501,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_656,c_500]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4306,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_4305,c_1501]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4389,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_4266,c_2129,c_4306]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4273,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_3803,c_1812]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_3831,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_3803,c_1]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_3838,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_3831,c_2129]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4379,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_4273,c_3803,c_3838]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4390,plain,
% 19.58/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_4389,c_4379]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4287,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))))) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1812,c_501]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_655,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_2862,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),X0)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_501,c_655]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_925,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_656,c_498]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_926,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_925,c_7,c_501]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1788,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_501,c_0]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1801,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_1788,c_501]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_2910,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_2862,c_7,c_926,c_1501,c_1801]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4367,plain,
% 19.58/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 19.58/2.99      inference(light_normalisation,
% 19.58/2.99                [status(thm)],
% 19.58/2.99                [c_4287,c_1505,c_2129,c_2910,c_4306]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4368,plain,
% 19.58/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(k1_xboole_0,X0) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_4367,c_2129,c_3803]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4391,plain,
% 19.58/2.99      ( k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_4390,c_4368]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4392,plain,
% 19.58/2.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_4391,c_1505]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_5782,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_5670,c_7,c_2129,c_4392]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_798,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_7921,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_5782,c_798]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_5674,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_3806,c_3806]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_5774,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_5674,c_1498]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_11,plain,
% 19.58/2.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 19.58/2.99      inference(cnf_transformation,[],[f59]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_827,plain,
% 19.58/2.99      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_8,c_11]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_838,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_11,c_9]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_657,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_840,plain,
% 19.58/2.99      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_838,c_657]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_942,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_827,c_0,c_840]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4401,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_4392,c_942]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4403,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_4401,c_8]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_5775,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)))) = k4_xboole_0(X0,X1) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_5774,c_7,c_4403]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_5776,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_5775,c_4403]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8285,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_7921,c_5776]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8286,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_8285,c_7,c_4403]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_24560,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1,c_8286]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_43699,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_24560,c_798]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4765,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_4403,c_501]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4772,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_4765,c_4403]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4426,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_4392,c_1]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4450,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_4426,c_4392]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4451,plain,
% 19.58/2.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_4450,c_4306,c_4403]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4773,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_4772,c_7,c_4403,c_4451]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8014,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_798,c_1]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8204,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_8014,c_7]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_43857,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))),X1))) = k1_xboole_0 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_43699,c_7,c_4392,c_4773,c_8204]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_801,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_10761,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_801,c_5776]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_10769,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X3))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X3) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_798,c_10761]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_11037,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X3) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_10769,c_7]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1751,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1,c_501]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_7993,plain,
% 19.58/2.99      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = iProver_top ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_798,c_497]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8233,plain,
% 19.58/2.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X1) = iProver_top ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_7993,c_7]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8645,plain,
% 19.58/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_8233,c_498]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8646,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_8645,c_7,c_501]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8647,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_8646,c_8204]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_11038,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_11037,c_7,c_1751,c_8647]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_43858,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0))) = k1_xboole_0 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_43857,c_7,c_11038]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8003,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_798,c_0]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_8222,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_8003,c_7]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_44590,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X3),X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_43858,c_8222]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1487,plain,
% 19.58/2.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_657,c_715]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_45150,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X3),X0)))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_44590,c_1487]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_44549,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),X0)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_43858,c_655]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_44921,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)),X0)) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_44549,c_4403]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_23423,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_10761,c_8222]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_44922,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)) = X0 ),
% 19.58/2.99      inference(demodulation,
% 19.58/2.99                [status(thm)],
% 19.58/2.99                [c_44921,c_4403,c_4451,c_8204,c_23423,c_43858]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_45151,plain,
% 19.58/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_45150,c_8,c_4392,c_44922]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_13,negated_conjecture,
% 19.58/2.99      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 19.58/2.99      inference(cnf_transformation,[],[f60]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_651,plain,
% 19.58/2.99      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_1,c_13]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_710,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) != sK1 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_9,c_651]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_711,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_710,c_0]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_48561,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != sK1 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_45151,c_711]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_975,plain,
% 19.58/2.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_709,c_1]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_841,plain,
% 19.58/2.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_840,c_11]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_14404,plain,
% 19.58/2.99      ( k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_975,c_841]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_1132,plain,
% 19.58/2.99      ( k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_975,c_0]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_14536,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k1_xboole_0) ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_14404,c_1132,c_1500]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_4192,plain,
% 19.58/2.99      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0) ),
% 19.58/2.99      inference(superposition,[status(thm)],[c_1132,c_9]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_14537,plain,
% 19.58/2.99      ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = sK1 ),
% 19.58/2.99      inference(demodulation,[status(thm)],[c_14536,c_8,c_4192]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_48566,plain,
% 19.58/2.99      ( sK1 != sK1 ),
% 19.58/2.99      inference(light_normalisation,[status(thm)],[c_48561,c_14537]) ).
% 19.58/2.99  
% 19.58/2.99  cnf(c_48567,plain,
% 19.58/2.99      ( $false ),
% 19.58/2.99      inference(equality_resolution_simp,[status(thm)],[c_48566]) ).
% 19.58/2.99  
% 19.58/2.99  
% 19.58/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.58/2.99  
% 19.58/2.99  ------                               Statistics
% 19.58/2.99  
% 19.58/2.99  ------ General
% 19.58/2.99  
% 19.58/2.99  abstr_ref_over_cycles:                  0
% 19.58/2.99  abstr_ref_under_cycles:                 0
% 19.58/2.99  gc_basic_clause_elim:                   0
% 19.58/2.99  forced_gc_time:                         0
% 19.58/2.99  parsing_time:                           0.024
% 19.58/2.99  unif_index_cands_time:                  0.
% 19.58/2.99  unif_index_add_time:                    0.
% 19.58/2.99  orderings_time:                         0.
% 19.58/2.99  out_proof_time:                         0.008
% 19.58/2.99  total_time:                             2.167
% 19.58/2.99  num_of_symbols:                         41
% 19.58/2.99  num_of_terms:                           107566
% 19.58/2.99  
% 19.58/2.99  ------ Preprocessing
% 19.58/2.99  
% 19.58/2.99  num_of_splits:                          0
% 19.58/2.99  num_of_split_atoms:                     0
% 19.58/2.99  num_of_reused_defs:                     0
% 19.58/2.99  num_eq_ax_congr_red:                    0
% 19.58/2.99  num_of_sem_filtered_clauses:            1
% 19.58/2.99  num_of_subtypes:                        0
% 19.58/2.99  monotx_restored_types:                  0
% 19.58/2.99  sat_num_of_epr_types:                   0
% 19.58/2.99  sat_num_of_non_cyclic_types:            0
% 19.58/2.99  sat_guarded_non_collapsed_types:        0
% 19.58/2.99  num_pure_diseq_elim:                    0
% 19.58/2.99  simp_replaced_by:                       0
% 19.58/2.99  res_preprocessed:                       74
% 19.58/2.99  prep_upred:                             0
% 19.58/2.99  prep_unflattend:                        26
% 19.58/2.99  smt_new_axioms:                         0
% 19.58/2.99  pred_elim_cands:                        1
% 19.58/2.99  pred_elim:                              1
% 19.58/2.99  pred_elim_cl:                           1
% 19.58/2.99  pred_elim_cycles:                       3
% 19.58/2.99  merged_defs:                            8
% 19.58/2.99  merged_defs_ncl:                        0
% 19.58/2.99  bin_hyper_res:                          8
% 19.58/2.99  prep_cycles:                            4
% 19.58/2.99  pred_elim_time:                         0.003
% 19.58/2.99  splitting_time:                         0.
% 19.58/2.99  sem_filter_time:                        0.
% 19.58/2.99  monotx_time:                            0.
% 19.58/2.99  subtype_inf_time:                       0.
% 19.58/2.99  
% 19.58/2.99  ------ Problem properties
% 19.58/2.99  
% 19.58/2.99  clauses:                                14
% 19.58/2.99  conjectures:                            1
% 19.58/2.99  epr:                                    0
% 19.58/2.99  horn:                                   14
% 19.58/2.99  ground:                                 2
% 19.58/2.99  unary:                                  11
% 19.58/2.99  binary:                                 3
% 19.58/2.99  lits:                                   17
% 19.58/2.99  lits_eq:                                11
% 19.58/2.99  fd_pure:                                0
% 19.58/2.99  fd_pseudo:                              0
% 19.58/2.99  fd_cond:                                0
% 19.58/2.99  fd_pseudo_cond:                         0
% 19.58/2.99  ac_symbols:                             0
% 19.58/2.99  
% 19.58/2.99  ------ Propositional Solver
% 19.58/2.99  
% 19.58/2.99  prop_solver_calls:                      37
% 19.58/2.99  prop_fast_solver_calls:                 489
% 19.58/2.99  smt_solver_calls:                       0
% 19.58/2.99  smt_fast_solver_calls:                  0
% 19.58/2.99  prop_num_of_clauses:                    12358
% 19.58/2.99  prop_preprocess_simplified:             11625
% 19.58/2.99  prop_fo_subsumed:                       0
% 19.58/2.99  prop_solver_time:                       0.
% 19.58/2.99  smt_solver_time:                        0.
% 19.58/2.99  smt_fast_solver_time:                   0.
% 19.58/2.99  prop_fast_solver_time:                  0.
% 19.58/2.99  prop_unsat_core_time:                   0.
% 19.58/2.99  
% 19.58/2.99  ------ QBF
% 19.58/2.99  
% 19.58/2.99  qbf_q_res:                              0
% 19.58/2.99  qbf_num_tautologies:                    0
% 19.58/2.99  qbf_prep_cycles:                        0
% 19.58/2.99  
% 19.58/2.99  ------ BMC1
% 19.58/2.99  
% 19.58/2.99  bmc1_current_bound:                     -1
% 19.58/2.99  bmc1_last_solved_bound:                 -1
% 19.58/2.99  bmc1_unsat_core_size:                   -1
% 19.58/2.99  bmc1_unsat_core_parents_size:           -1
% 19.58/2.99  bmc1_merge_next_fun:                    0
% 19.58/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.58/2.99  
% 19.58/2.99  ------ Instantiation
% 19.58/2.99  
% 19.58/2.99  inst_num_of_clauses:                    2712
% 19.58/2.99  inst_num_in_passive:                    1449
% 19.58/2.99  inst_num_in_active:                     889
% 19.58/2.99  inst_num_in_unprocessed:                377
% 19.58/2.99  inst_num_of_loops:                      950
% 19.58/2.99  inst_num_of_learning_restarts:          0
% 19.58/2.99  inst_num_moves_active_passive:          52
% 19.58/2.99  inst_lit_activity:                      0
% 19.58/2.99  inst_lit_activity_moves:                0
% 19.58/2.99  inst_num_tautologies:                   0
% 19.58/2.99  inst_num_prop_implied:                  0
% 19.58/2.99  inst_num_existing_simplified:           0
% 19.58/2.99  inst_num_eq_res_simplified:             0
% 19.58/2.99  inst_num_child_elim:                    0
% 19.58/2.99  inst_num_of_dismatching_blockings:      1353
% 19.58/2.99  inst_num_of_non_proper_insts:           2785
% 19.58/2.99  inst_num_of_duplicates:                 0
% 19.58/2.99  inst_inst_num_from_inst_to_res:         0
% 19.58/2.99  inst_dismatching_checking_time:         0.
% 19.58/2.99  
% 19.58/2.99  ------ Resolution
% 19.58/2.99  
% 19.58/2.99  res_num_of_clauses:                     0
% 19.58/2.99  res_num_in_passive:                     0
% 19.58/2.99  res_num_in_active:                      0
% 19.58/2.99  res_num_of_loops:                       78
% 19.58/2.99  res_forward_subset_subsumed:            446
% 19.58/2.99  res_backward_subset_subsumed:           8
% 19.58/2.99  res_forward_subsumed:                   0
% 19.58/2.99  res_backward_subsumed:                  0
% 19.58/2.99  res_forward_subsumption_resolution:     0
% 19.58/2.99  res_backward_subsumption_resolution:    0
% 19.58/2.99  res_clause_to_clause_subsumption:       48731
% 19.58/2.99  res_orphan_elimination:                 0
% 19.58/2.99  res_tautology_del:                      146
% 19.58/2.99  res_num_eq_res_simplified:              0
% 19.58/2.99  res_num_sel_changes:                    0
% 19.58/2.99  res_moves_from_active_to_pass:          0
% 19.58/2.99  
% 19.58/2.99  ------ Superposition
% 19.58/2.99  
% 19.58/2.99  sup_time_total:                         0.
% 19.58/2.99  sup_time_generating:                    0.
% 19.58/2.99  sup_time_sim_full:                      0.
% 19.58/2.99  sup_time_sim_immed:                     0.
% 19.58/2.99  
% 19.58/2.99  sup_num_of_clauses:                     3294
% 19.58/2.99  sup_num_in_active:                      139
% 19.58/2.99  sup_num_in_passive:                     3155
% 19.58/2.99  sup_num_of_loops:                       188
% 19.58/2.99  sup_fw_superposition:                   8428
% 19.58/2.99  sup_bw_superposition:                   6000
% 19.58/2.99  sup_immediate_simplified:               12118
% 19.58/2.99  sup_given_eliminated:                   15
% 19.58/2.99  comparisons_done:                       0
% 19.58/2.99  comparisons_avoided:                    0
% 19.58/2.99  
% 19.58/2.99  ------ Simplifications
% 19.58/2.99  
% 19.58/2.99  
% 19.58/2.99  sim_fw_subset_subsumed:                 2
% 19.58/2.99  sim_bw_subset_subsumed:                 0
% 19.58/2.99  sim_fw_subsumed:                        958
% 19.58/2.99  sim_bw_subsumed:                        200
% 19.58/2.99  sim_fw_subsumption_res:                 0
% 19.58/2.99  sim_bw_subsumption_res:                 0
% 19.58/2.99  sim_tautology_del:                      0
% 19.58/2.99  sim_eq_tautology_del:                   3667
% 19.58/2.99  sim_eq_res_simp:                        1
% 19.58/2.99  sim_fw_demodulated:                     11883
% 19.58/2.99  sim_bw_demodulated:                     294
% 19.58/2.99  sim_light_normalised:                   6863
% 19.58/2.99  sim_joinable_taut:                      0
% 19.58/2.99  sim_joinable_simp:                      0
% 19.58/2.99  sim_ac_normalised:                      0
% 19.58/2.99  sim_smt_subsumption:                    0
% 19.58/2.99  
%------------------------------------------------------------------------------
