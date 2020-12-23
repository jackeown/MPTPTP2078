%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:29 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 232 expanded)
%              Number of clauses        :   27 (  33 expanded)
%              Number of leaves         :   15 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  120 ( 384 expanded)
%              Number of equality atoms :   85 ( 277 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f52,f52])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
      & r2_hidden(sK5,sK2)
      & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
    & r2_hidden(sK5,sK2)
    & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f36])).

fof(f63,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f68])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f52,f69,f69])).

fof(f62,plain,(
    k3_xboole_0(sK3,sK4) = k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f77,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f62,f52,f70])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f49,f52,f52,f52,f52])).

fof(f61,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f64,plain,(
    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f64,f52,f70])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_385,plain,
    ( r2_hidden(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_386,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_763,plain,
    ( k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0),k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0),sK2)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_385,c_386])).

cnf(c_1213,plain,
    ( k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK2)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_385,c_763])).

cnf(c_17,negated_conjecture,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_767,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
    inference(demodulation,[status(thm)],[c_0,c_17])).

cnf(c_1214,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),sK2)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_1213,c_767])).

cnf(c_11,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1345,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_1214,c_11])).

cnf(c_1465,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_0,c_1345])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_384,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_388,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1606,plain,
    ( k2_xboole_0(sK2,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_384,c_388])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2079,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_1606,c_12])).

cnf(c_6843,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1465,c_2079])).

cnf(c_15,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_431,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_15,c_17])).

cnf(c_766,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(demodulation,[status(thm)],[c_0,c_431])).

cnf(c_6865,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(demodulation,[status(thm)],[c_6843,c_766])).

cnf(c_1426,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6865,c_1426])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.39/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/0.99  
% 3.39/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/0.99  
% 3.39/0.99  ------  iProver source info
% 3.39/0.99  
% 3.39/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.39/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/0.99  git: non_committed_changes: false
% 3.39/0.99  git: last_make_outside_of_git: false
% 3.39/0.99  
% 3.39/0.99  ------ 
% 3.39/0.99  
% 3.39/0.99  ------ Input Options
% 3.39/0.99  
% 3.39/0.99  --out_options                           all
% 3.39/0.99  --tptp_safe_out                         true
% 3.39/0.99  --problem_path                          ""
% 3.39/0.99  --include_path                          ""
% 3.39/0.99  --clausifier                            res/vclausify_rel
% 3.39/0.99  --clausifier_options                    --mode clausify
% 3.39/0.99  --stdin                                 false
% 3.39/0.99  --stats_out                             all
% 3.39/0.99  
% 3.39/0.99  ------ General Options
% 3.39/0.99  
% 3.39/0.99  --fof                                   false
% 3.39/0.99  --time_out_real                         305.
% 3.39/0.99  --time_out_virtual                      -1.
% 3.39/0.99  --symbol_type_check                     false
% 3.39/0.99  --clausify_out                          false
% 3.39/0.99  --sig_cnt_out                           false
% 3.39/0.99  --trig_cnt_out                          false
% 3.39/0.99  --trig_cnt_out_tolerance                1.
% 3.39/0.99  --trig_cnt_out_sk_spl                   false
% 3.39/0.99  --abstr_cl_out                          false
% 3.39/0.99  
% 3.39/0.99  ------ Global Options
% 3.39/0.99  
% 3.39/0.99  --schedule                              default
% 3.39/0.99  --add_important_lit                     false
% 3.39/0.99  --prop_solver_per_cl                    1000
% 3.39/0.99  --min_unsat_core                        false
% 3.39/0.99  --soft_assumptions                      false
% 3.39/0.99  --soft_lemma_size                       3
% 3.39/0.99  --prop_impl_unit_size                   0
% 3.39/0.99  --prop_impl_unit                        []
% 3.39/0.99  --share_sel_clauses                     true
% 3.39/0.99  --reset_solvers                         false
% 3.39/0.99  --bc_imp_inh                            [conj_cone]
% 3.39/0.99  --conj_cone_tolerance                   3.
% 3.39/0.99  --extra_neg_conj                        none
% 3.39/0.99  --large_theory_mode                     true
% 3.39/0.99  --prolific_symb_bound                   200
% 3.39/0.99  --lt_threshold                          2000
% 3.39/0.99  --clause_weak_htbl                      true
% 3.39/0.99  --gc_record_bc_elim                     false
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing Options
% 3.39/0.99  
% 3.39/0.99  --preprocessing_flag                    true
% 3.39/0.99  --time_out_prep_mult                    0.1
% 3.39/0.99  --splitting_mode                        input
% 3.39/0.99  --splitting_grd                         true
% 3.39/0.99  --splitting_cvd                         false
% 3.39/0.99  --splitting_cvd_svl                     false
% 3.39/0.99  --splitting_nvd                         32
% 3.39/0.99  --sub_typing                            true
% 3.39/0.99  --prep_gs_sim                           true
% 3.39/0.99  --prep_unflatten                        true
% 3.39/0.99  --prep_res_sim                          true
% 3.39/0.99  --prep_upred                            true
% 3.39/0.99  --prep_sem_filter                       exhaustive
% 3.39/0.99  --prep_sem_filter_out                   false
% 3.39/0.99  --pred_elim                             true
% 3.39/0.99  --res_sim_input                         true
% 3.39/0.99  --eq_ax_congr_red                       true
% 3.39/0.99  --pure_diseq_elim                       true
% 3.39/0.99  --brand_transform                       false
% 3.39/0.99  --non_eq_to_eq                          false
% 3.39/0.99  --prep_def_merge                        true
% 3.39/0.99  --prep_def_merge_prop_impl              false
% 3.39/0.99  --prep_def_merge_mbd                    true
% 3.39/0.99  --prep_def_merge_tr_red                 false
% 3.39/0.99  --prep_def_merge_tr_cl                  false
% 3.39/0.99  --smt_preprocessing                     true
% 3.39/0.99  --smt_ac_axioms                         fast
% 3.39/0.99  --preprocessed_out                      false
% 3.39/0.99  --preprocessed_stats                    false
% 3.39/0.99  
% 3.39/0.99  ------ Abstraction refinement Options
% 3.39/0.99  
% 3.39/0.99  --abstr_ref                             []
% 3.39/0.99  --abstr_ref_prep                        false
% 3.39/0.99  --abstr_ref_until_sat                   false
% 3.39/0.99  --abstr_ref_sig_restrict                funpre
% 3.39/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.99  --abstr_ref_under                       []
% 3.39/0.99  
% 3.39/0.99  ------ SAT Options
% 3.39/0.99  
% 3.39/0.99  --sat_mode                              false
% 3.39/0.99  --sat_fm_restart_options                ""
% 3.39/0.99  --sat_gr_def                            false
% 3.39/0.99  --sat_epr_types                         true
% 3.39/0.99  --sat_non_cyclic_types                  false
% 3.39/0.99  --sat_finite_models                     false
% 3.39/0.99  --sat_fm_lemmas                         false
% 3.39/0.99  --sat_fm_prep                           false
% 3.39/0.99  --sat_fm_uc_incr                        true
% 3.39/0.99  --sat_out_model                         small
% 3.39/0.99  --sat_out_clauses                       false
% 3.39/0.99  
% 3.39/0.99  ------ QBF Options
% 3.39/0.99  
% 3.39/0.99  --qbf_mode                              false
% 3.39/0.99  --qbf_elim_univ                         false
% 3.39/0.99  --qbf_dom_inst                          none
% 3.39/0.99  --qbf_dom_pre_inst                      false
% 3.39/0.99  --qbf_sk_in                             false
% 3.39/0.99  --qbf_pred_elim                         true
% 3.39/0.99  --qbf_split                             512
% 3.39/0.99  
% 3.39/0.99  ------ BMC1 Options
% 3.39/0.99  
% 3.39/0.99  --bmc1_incremental                      false
% 3.39/0.99  --bmc1_axioms                           reachable_all
% 3.39/0.99  --bmc1_min_bound                        0
% 3.39/0.99  --bmc1_max_bound                        -1
% 3.39/0.99  --bmc1_max_bound_default                -1
% 3.39/0.99  --bmc1_symbol_reachability              true
% 3.39/0.99  --bmc1_property_lemmas                  false
% 3.39/0.99  --bmc1_k_induction                      false
% 3.39/0.99  --bmc1_non_equiv_states                 false
% 3.39/0.99  --bmc1_deadlock                         false
% 3.39/0.99  --bmc1_ucm                              false
% 3.39/0.99  --bmc1_add_unsat_core                   none
% 3.39/0.99  --bmc1_unsat_core_children              false
% 3.39/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.99  --bmc1_out_stat                         full
% 3.39/0.99  --bmc1_ground_init                      false
% 3.39/0.99  --bmc1_pre_inst_next_state              false
% 3.39/0.99  --bmc1_pre_inst_state                   false
% 3.39/0.99  --bmc1_pre_inst_reach_state             false
% 3.39/0.99  --bmc1_out_unsat_core                   false
% 3.39/0.99  --bmc1_aig_witness_out                  false
% 3.39/0.99  --bmc1_verbose                          false
% 3.39/0.99  --bmc1_dump_clauses_tptp                false
% 3.39/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.99  --bmc1_dump_file                        -
% 3.39/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.99  --bmc1_ucm_extend_mode                  1
% 3.39/0.99  --bmc1_ucm_init_mode                    2
% 3.39/0.99  --bmc1_ucm_cone_mode                    none
% 3.39/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.99  --bmc1_ucm_relax_model                  4
% 3.39/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.99  --bmc1_ucm_layered_model                none
% 3.39/0.99  --bmc1_ucm_max_lemma_size               10
% 3.39/0.99  
% 3.39/0.99  ------ AIG Options
% 3.39/0.99  
% 3.39/0.99  --aig_mode                              false
% 3.39/0.99  
% 3.39/0.99  ------ Instantiation Options
% 3.39/0.99  
% 3.39/0.99  --instantiation_flag                    true
% 3.39/0.99  --inst_sos_flag                         false
% 3.39/0.99  --inst_sos_phase                        true
% 3.39/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.99  --inst_lit_sel_side                     num_symb
% 3.39/0.99  --inst_solver_per_active                1400
% 3.39/0.99  --inst_solver_calls_frac                1.
% 3.39/0.99  --inst_passive_queue_type               priority_queues
% 3.39/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.99  --inst_passive_queues_freq              [25;2]
% 3.39/0.99  --inst_dismatching                      true
% 3.39/0.99  --inst_eager_unprocessed_to_passive     true
% 3.39/0.99  --inst_prop_sim_given                   true
% 3.39/0.99  --inst_prop_sim_new                     false
% 3.39/0.99  --inst_subs_new                         false
% 3.39/0.99  --inst_eq_res_simp                      false
% 3.39/0.99  --inst_subs_given                       false
% 3.39/0.99  --inst_orphan_elimination               true
% 3.39/0.99  --inst_learning_loop_flag               true
% 3.39/0.99  --inst_learning_start                   3000
% 3.39/0.99  --inst_learning_factor                  2
% 3.39/0.99  --inst_start_prop_sim_after_learn       3
% 3.39/0.99  --inst_sel_renew                        solver
% 3.39/0.99  --inst_lit_activity_flag                true
% 3.39/0.99  --inst_restr_to_given                   false
% 3.39/0.99  --inst_activity_threshold               500
% 3.39/0.99  --inst_out_proof                        true
% 3.39/0.99  
% 3.39/0.99  ------ Resolution Options
% 3.39/0.99  
% 3.39/0.99  --resolution_flag                       true
% 3.39/0.99  --res_lit_sel                           adaptive
% 3.39/0.99  --res_lit_sel_side                      none
% 3.39/0.99  --res_ordering                          kbo
% 3.39/0.99  --res_to_prop_solver                    active
% 3.39/0.99  --res_prop_simpl_new                    false
% 3.39/0.99  --res_prop_simpl_given                  true
% 3.39/0.99  --res_passive_queue_type                priority_queues
% 3.39/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.99  --res_passive_queues_freq               [15;5]
% 3.39/0.99  --res_forward_subs                      full
% 3.39/0.99  --res_backward_subs                     full
% 3.39/0.99  --res_forward_subs_resolution           true
% 3.39/0.99  --res_backward_subs_resolution          true
% 3.39/0.99  --res_orphan_elimination                true
% 3.39/0.99  --res_time_limit                        2.
% 3.39/0.99  --res_out_proof                         true
% 3.39/0.99  
% 3.39/0.99  ------ Superposition Options
% 3.39/0.99  
% 3.39/0.99  --superposition_flag                    true
% 3.39/0.99  --sup_passive_queue_type                priority_queues
% 3.39/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.99  --demod_completeness_check              fast
% 3.39/0.99  --demod_use_ground                      true
% 3.39/0.99  --sup_to_prop_solver                    passive
% 3.39/0.99  --sup_prop_simpl_new                    true
% 3.39/0.99  --sup_prop_simpl_given                  true
% 3.39/0.99  --sup_fun_splitting                     false
% 3.39/0.99  --sup_smt_interval                      50000
% 3.39/0.99  
% 3.39/0.99  ------ Superposition Simplification Setup
% 3.39/0.99  
% 3.39/0.99  --sup_indices_passive                   []
% 3.39/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_full_bw                           [BwDemod]
% 3.39/0.99  --sup_immed_triv                        [TrivRules]
% 3.39/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_immed_bw_main                     []
% 3.39/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.99  
% 3.39/0.99  ------ Combination Options
% 3.39/0.99  
% 3.39/0.99  --comb_res_mult                         3
% 3.39/0.99  --comb_sup_mult                         2
% 3.39/0.99  --comb_inst_mult                        10
% 3.39/0.99  
% 3.39/0.99  ------ Debug Options
% 3.39/0.99  
% 3.39/0.99  --dbg_backtrace                         false
% 3.39/0.99  --dbg_dump_prop_clauses                 false
% 3.39/0.99  --dbg_dump_prop_clauses_file            -
% 3.39/0.99  --dbg_out_stat                          false
% 3.39/0.99  ------ Parsing...
% 3.39/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/0.99  ------ Proving...
% 3.39/0.99  ------ Problem Properties 
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  clauses                                 19
% 3.39/0.99  conjectures                             4
% 3.39/0.99  EPR                                     2
% 3.39/0.99  Horn                                    14
% 3.39/0.99  unary                                   9
% 3.39/0.99  binary                                  5
% 3.39/0.99  lits                                    35
% 3.39/0.99  lits eq                                 12
% 3.39/0.99  fd_pure                                 0
% 3.39/0.99  fd_pseudo                               0
% 3.39/0.99  fd_cond                                 1
% 3.39/0.99  fd_pseudo_cond                          3
% 3.39/0.99  AC symbols                              0
% 3.39/0.99  
% 3.39/0.99  ------ Schedule dynamic 5 is on 
% 3.39/0.99  
% 3.39/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  ------ 
% 3.39/0.99  Current options:
% 3.39/0.99  ------ 
% 3.39/0.99  
% 3.39/0.99  ------ Input Options
% 3.39/0.99  
% 3.39/0.99  --out_options                           all
% 3.39/0.99  --tptp_safe_out                         true
% 3.39/0.99  --problem_path                          ""
% 3.39/0.99  --include_path                          ""
% 3.39/0.99  --clausifier                            res/vclausify_rel
% 3.39/0.99  --clausifier_options                    --mode clausify
% 3.39/0.99  --stdin                                 false
% 3.39/0.99  --stats_out                             all
% 3.39/0.99  
% 3.39/0.99  ------ General Options
% 3.39/0.99  
% 3.39/0.99  --fof                                   false
% 3.39/0.99  --time_out_real                         305.
% 3.39/0.99  --time_out_virtual                      -1.
% 3.39/0.99  --symbol_type_check                     false
% 3.39/0.99  --clausify_out                          false
% 3.39/0.99  --sig_cnt_out                           false
% 3.39/0.99  --trig_cnt_out                          false
% 3.39/0.99  --trig_cnt_out_tolerance                1.
% 3.39/0.99  --trig_cnt_out_sk_spl                   false
% 3.39/0.99  --abstr_cl_out                          false
% 3.39/0.99  
% 3.39/0.99  ------ Global Options
% 3.39/0.99  
% 3.39/0.99  --schedule                              default
% 3.39/0.99  --add_important_lit                     false
% 3.39/0.99  --prop_solver_per_cl                    1000
% 3.39/0.99  --min_unsat_core                        false
% 3.39/0.99  --soft_assumptions                      false
% 3.39/0.99  --soft_lemma_size                       3
% 3.39/0.99  --prop_impl_unit_size                   0
% 3.39/0.99  --prop_impl_unit                        []
% 3.39/0.99  --share_sel_clauses                     true
% 3.39/0.99  --reset_solvers                         false
% 3.39/0.99  --bc_imp_inh                            [conj_cone]
% 3.39/0.99  --conj_cone_tolerance                   3.
% 3.39/0.99  --extra_neg_conj                        none
% 3.39/0.99  --large_theory_mode                     true
% 3.39/0.99  --prolific_symb_bound                   200
% 3.39/0.99  --lt_threshold                          2000
% 3.39/0.99  --clause_weak_htbl                      true
% 3.39/0.99  --gc_record_bc_elim                     false
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing Options
% 3.39/0.99  
% 3.39/0.99  --preprocessing_flag                    true
% 3.39/0.99  --time_out_prep_mult                    0.1
% 3.39/0.99  --splitting_mode                        input
% 3.39/0.99  --splitting_grd                         true
% 3.39/0.99  --splitting_cvd                         false
% 3.39/0.99  --splitting_cvd_svl                     false
% 3.39/0.99  --splitting_nvd                         32
% 3.39/0.99  --sub_typing                            true
% 3.39/0.99  --prep_gs_sim                           true
% 3.39/0.99  --prep_unflatten                        true
% 3.39/0.99  --prep_res_sim                          true
% 3.39/0.99  --prep_upred                            true
% 3.39/0.99  --prep_sem_filter                       exhaustive
% 3.39/0.99  --prep_sem_filter_out                   false
% 3.39/0.99  --pred_elim                             true
% 3.39/0.99  --res_sim_input                         true
% 3.39/0.99  --eq_ax_congr_red                       true
% 3.39/0.99  --pure_diseq_elim                       true
% 3.39/0.99  --brand_transform                       false
% 3.39/0.99  --non_eq_to_eq                          false
% 3.39/0.99  --prep_def_merge                        true
% 3.39/0.99  --prep_def_merge_prop_impl              false
% 3.39/0.99  --prep_def_merge_mbd                    true
% 3.39/0.99  --prep_def_merge_tr_red                 false
% 3.39/0.99  --prep_def_merge_tr_cl                  false
% 3.39/0.99  --smt_preprocessing                     true
% 3.39/0.99  --smt_ac_axioms                         fast
% 3.39/0.99  --preprocessed_out                      false
% 3.39/0.99  --preprocessed_stats                    false
% 3.39/0.99  
% 3.39/0.99  ------ Abstraction refinement Options
% 3.39/0.99  
% 3.39/0.99  --abstr_ref                             []
% 3.39/0.99  --abstr_ref_prep                        false
% 3.39/0.99  --abstr_ref_until_sat                   false
% 3.39/0.99  --abstr_ref_sig_restrict                funpre
% 3.39/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.99  --abstr_ref_under                       []
% 3.39/0.99  
% 3.39/0.99  ------ SAT Options
% 3.39/0.99  
% 3.39/0.99  --sat_mode                              false
% 3.39/0.99  --sat_fm_restart_options                ""
% 3.39/0.99  --sat_gr_def                            false
% 3.39/0.99  --sat_epr_types                         true
% 3.39/0.99  --sat_non_cyclic_types                  false
% 3.39/0.99  --sat_finite_models                     false
% 3.39/0.99  --sat_fm_lemmas                         false
% 3.39/0.99  --sat_fm_prep                           false
% 3.39/0.99  --sat_fm_uc_incr                        true
% 3.39/0.99  --sat_out_model                         small
% 3.39/0.99  --sat_out_clauses                       false
% 3.39/0.99  
% 3.39/0.99  ------ QBF Options
% 3.39/0.99  
% 3.39/0.99  --qbf_mode                              false
% 3.39/0.99  --qbf_elim_univ                         false
% 3.39/0.99  --qbf_dom_inst                          none
% 3.39/0.99  --qbf_dom_pre_inst                      false
% 3.39/0.99  --qbf_sk_in                             false
% 3.39/0.99  --qbf_pred_elim                         true
% 3.39/0.99  --qbf_split                             512
% 3.39/0.99  
% 3.39/0.99  ------ BMC1 Options
% 3.39/0.99  
% 3.39/0.99  --bmc1_incremental                      false
% 3.39/0.99  --bmc1_axioms                           reachable_all
% 3.39/0.99  --bmc1_min_bound                        0
% 3.39/0.99  --bmc1_max_bound                        -1
% 3.39/0.99  --bmc1_max_bound_default                -1
% 3.39/0.99  --bmc1_symbol_reachability              true
% 3.39/0.99  --bmc1_property_lemmas                  false
% 3.39/0.99  --bmc1_k_induction                      false
% 3.39/0.99  --bmc1_non_equiv_states                 false
% 3.39/0.99  --bmc1_deadlock                         false
% 3.39/0.99  --bmc1_ucm                              false
% 3.39/0.99  --bmc1_add_unsat_core                   none
% 3.39/0.99  --bmc1_unsat_core_children              false
% 3.39/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.99  --bmc1_out_stat                         full
% 3.39/0.99  --bmc1_ground_init                      false
% 3.39/0.99  --bmc1_pre_inst_next_state              false
% 3.39/0.99  --bmc1_pre_inst_state                   false
% 3.39/0.99  --bmc1_pre_inst_reach_state             false
% 3.39/0.99  --bmc1_out_unsat_core                   false
% 3.39/0.99  --bmc1_aig_witness_out                  false
% 3.39/0.99  --bmc1_verbose                          false
% 3.39/0.99  --bmc1_dump_clauses_tptp                false
% 3.39/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.99  --bmc1_dump_file                        -
% 3.39/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.99  --bmc1_ucm_extend_mode                  1
% 3.39/0.99  --bmc1_ucm_init_mode                    2
% 3.39/0.99  --bmc1_ucm_cone_mode                    none
% 3.39/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.99  --bmc1_ucm_relax_model                  4
% 3.39/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.99  --bmc1_ucm_layered_model                none
% 3.39/0.99  --bmc1_ucm_max_lemma_size               10
% 3.39/0.99  
% 3.39/0.99  ------ AIG Options
% 3.39/0.99  
% 3.39/0.99  --aig_mode                              false
% 3.39/0.99  
% 3.39/0.99  ------ Instantiation Options
% 3.39/0.99  
% 3.39/0.99  --instantiation_flag                    true
% 3.39/0.99  --inst_sos_flag                         false
% 3.39/0.99  --inst_sos_phase                        true
% 3.39/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.99  --inst_lit_sel_side                     none
% 3.39/0.99  --inst_solver_per_active                1400
% 3.39/0.99  --inst_solver_calls_frac                1.
% 3.39/0.99  --inst_passive_queue_type               priority_queues
% 3.39/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.99  --inst_passive_queues_freq              [25;2]
% 3.39/0.99  --inst_dismatching                      true
% 3.39/0.99  --inst_eager_unprocessed_to_passive     true
% 3.39/0.99  --inst_prop_sim_given                   true
% 3.39/0.99  --inst_prop_sim_new                     false
% 3.39/0.99  --inst_subs_new                         false
% 3.39/0.99  --inst_eq_res_simp                      false
% 3.39/0.99  --inst_subs_given                       false
% 3.39/0.99  --inst_orphan_elimination               true
% 3.39/0.99  --inst_learning_loop_flag               true
% 3.39/0.99  --inst_learning_start                   3000
% 3.39/0.99  --inst_learning_factor                  2
% 3.39/0.99  --inst_start_prop_sim_after_learn       3
% 3.39/0.99  --inst_sel_renew                        solver
% 3.39/0.99  --inst_lit_activity_flag                true
% 3.39/0.99  --inst_restr_to_given                   false
% 3.39/0.99  --inst_activity_threshold               500
% 3.39/0.99  --inst_out_proof                        true
% 3.39/0.99  
% 3.39/0.99  ------ Resolution Options
% 3.39/0.99  
% 3.39/0.99  --resolution_flag                       false
% 3.39/0.99  --res_lit_sel                           adaptive
% 3.39/0.99  --res_lit_sel_side                      none
% 3.39/0.99  --res_ordering                          kbo
% 3.39/0.99  --res_to_prop_solver                    active
% 3.39/0.99  --res_prop_simpl_new                    false
% 3.39/0.99  --res_prop_simpl_given                  true
% 3.39/0.99  --res_passive_queue_type                priority_queues
% 3.39/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.99  --res_passive_queues_freq               [15;5]
% 3.39/0.99  --res_forward_subs                      full
% 3.39/0.99  --res_backward_subs                     full
% 3.39/0.99  --res_forward_subs_resolution           true
% 3.39/0.99  --res_backward_subs_resolution          true
% 3.39/0.99  --res_orphan_elimination                true
% 3.39/0.99  --res_time_limit                        2.
% 3.39/0.99  --res_out_proof                         true
% 3.39/0.99  
% 3.39/0.99  ------ Superposition Options
% 3.39/0.99  
% 3.39/0.99  --superposition_flag                    true
% 3.39/0.99  --sup_passive_queue_type                priority_queues
% 3.39/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.99  --demod_completeness_check              fast
% 3.39/0.99  --demod_use_ground                      true
% 3.39/0.99  --sup_to_prop_solver                    passive
% 3.39/0.99  --sup_prop_simpl_new                    true
% 3.39/0.99  --sup_prop_simpl_given                  true
% 3.39/0.99  --sup_fun_splitting                     false
% 3.39/0.99  --sup_smt_interval                      50000
% 3.39/0.99  
% 3.39/0.99  ------ Superposition Simplification Setup
% 3.39/0.99  
% 3.39/0.99  --sup_indices_passive                   []
% 3.39/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_full_bw                           [BwDemod]
% 3.39/0.99  --sup_immed_triv                        [TrivRules]
% 3.39/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_immed_bw_main                     []
% 3.39/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.99  
% 3.39/0.99  ------ Combination Options
% 3.39/0.99  
% 3.39/0.99  --comb_res_mult                         3
% 3.39/0.99  --comb_sup_mult                         2
% 3.39/0.99  --comb_inst_mult                        10
% 3.39/0.99  
% 3.39/0.99  ------ Debug Options
% 3.39/0.99  
% 3.39/0.99  --dbg_backtrace                         false
% 3.39/0.99  --dbg_dump_prop_clauses                 false
% 3.39/0.99  --dbg_dump_prop_clauses_file            -
% 3.39/0.99  --dbg_out_stat                          false
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  ------ Proving...
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  % SZS status Theorem for theBenchmark.p
% 3.39/0.99  
% 3.39/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/0.99  
% 3.39/0.99  fof(f1,axiom,(
% 3.39/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f38,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f1])).
% 3.39/0.99  
% 3.39/0.99  fof(f10,axiom,(
% 3.39/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f52,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.39/0.99    inference(cnf_transformation,[],[f10])).
% 3.39/0.99  
% 3.39/0.99  fof(f71,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.39/0.99    inference(definition_unfolding,[],[f38,f52,f52])).
% 3.39/0.99  
% 3.39/0.99  fof(f19,conjecture,(
% 3.39/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f20,negated_conjecture,(
% 3.39/0.99    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 3.39/0.99    inference(negated_conjecture,[],[f19])).
% 3.39/0.99  
% 3.39/0.99  fof(f27,plain,(
% 3.39/0.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 3.39/0.99    inference(ennf_transformation,[],[f20])).
% 3.39/0.99  
% 3.39/0.99  fof(f28,plain,(
% 3.39/0.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 3.39/0.99    inference(flattening,[],[f27])).
% 3.39/0.99  
% 3.39/0.99  fof(f36,plain,(
% 3.39/0.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3))),
% 3.39/0.99    introduced(choice_axiom,[])).
% 3.39/0.99  
% 3.39/0.99  fof(f37,plain,(
% 3.39/0.99    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3)),
% 3.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f36])).
% 3.39/0.99  
% 3.39/0.99  fof(f63,plain,(
% 3.39/0.99    r2_hidden(sK5,sK2)),
% 3.39/0.99    inference(cnf_transformation,[],[f37])).
% 3.39/0.99  
% 3.39/0.99  fof(f18,axiom,(
% 3.39/0.99    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2))),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f25,plain,(
% 3.39/0.99    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 3.39/0.99    inference(ennf_transformation,[],[f18])).
% 3.39/0.99  
% 3.39/0.99  fof(f26,plain,(
% 3.39/0.99    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 3.39/0.99    inference(flattening,[],[f25])).
% 3.39/0.99  
% 3.39/0.99  fof(f60,plain,(
% 3.39/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f26])).
% 3.39/0.99  
% 3.39/0.99  fof(f12,axiom,(
% 3.39/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f54,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f12])).
% 3.39/0.99  
% 3.39/0.99  fof(f13,axiom,(
% 3.39/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f55,plain,(
% 3.39/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f13])).
% 3.39/0.99  
% 3.39/0.99  fof(f14,axiom,(
% 3.39/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f56,plain,(
% 3.39/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f14])).
% 3.39/0.99  
% 3.39/0.99  fof(f15,axiom,(
% 3.39/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f57,plain,(
% 3.39/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f15])).
% 3.39/0.99  
% 3.39/0.99  fof(f16,axiom,(
% 3.39/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f58,plain,(
% 3.39/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f16])).
% 3.39/0.99  
% 3.39/0.99  fof(f17,axiom,(
% 3.39/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f59,plain,(
% 3.39/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f17])).
% 3.39/0.99  
% 3.39/0.99  fof(f65,plain,(
% 3.39/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.39/0.99    inference(definition_unfolding,[],[f58,f59])).
% 3.39/0.99  
% 3.39/0.99  fof(f66,plain,(
% 3.39/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.39/0.99    inference(definition_unfolding,[],[f57,f65])).
% 3.39/0.99  
% 3.39/0.99  fof(f67,plain,(
% 3.39/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.39/0.99    inference(definition_unfolding,[],[f56,f66])).
% 3.39/0.99  
% 3.39/0.99  fof(f68,plain,(
% 3.39/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.39/0.99    inference(definition_unfolding,[],[f55,f67])).
% 3.39/0.99  
% 3.39/0.99  fof(f69,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.39/0.99    inference(definition_unfolding,[],[f54,f68])).
% 3.39/0.99  
% 3.39/0.99  fof(f75,plain,(
% 3.39/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 3.39/0.99    inference(definition_unfolding,[],[f60,f52,f69,f69])).
% 3.39/0.99  
% 3.39/0.99  fof(f62,plain,(
% 3.39/0.99    k3_xboole_0(sK3,sK4) = k1_tarski(sK5)),
% 3.39/0.99    inference(cnf_transformation,[],[f37])).
% 3.39/0.99  
% 3.39/0.99  fof(f11,axiom,(
% 3.39/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f53,plain,(
% 3.39/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f11])).
% 3.39/0.99  
% 3.39/0.99  fof(f70,plain,(
% 3.39/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.39/0.99    inference(definition_unfolding,[],[f53,f69])).
% 3.39/0.99  
% 3.39/0.99  fof(f77,plain,(
% 3.39/0.99    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),
% 3.39/0.99    inference(definition_unfolding,[],[f62,f52,f70])).
% 3.39/0.99  
% 3.39/0.99  fof(f7,axiom,(
% 3.39/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f49,plain,(
% 3.39/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f7])).
% 3.39/0.99  
% 3.39/0.99  fof(f73,plain,(
% 3.39/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 3.39/0.99    inference(definition_unfolding,[],[f49,f52,f52,f52,f52])).
% 3.39/0.99  
% 3.39/0.99  fof(f61,plain,(
% 3.39/0.99    r1_tarski(sK2,sK3)),
% 3.39/0.99    inference(cnf_transformation,[],[f37])).
% 3.39/0.99  
% 3.39/0.99  fof(f6,axiom,(
% 3.39/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f24,plain,(
% 3.39/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.39/0.99    inference(ennf_transformation,[],[f6])).
% 3.39/0.99  
% 3.39/0.99  fof(f48,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f24])).
% 3.39/0.99  
% 3.39/0.99  fof(f8,axiom,(
% 3.39/0.99    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f50,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.39/0.99    inference(cnf_transformation,[],[f8])).
% 3.39/0.99  
% 3.39/0.99  fof(f74,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 3.39/0.99    inference(definition_unfolding,[],[f50,f52])).
% 3.39/0.99  
% 3.39/0.99  fof(f64,plain,(
% 3.39/0.99    k3_xboole_0(sK2,sK4) != k1_tarski(sK5)),
% 3.39/0.99    inference(cnf_transformation,[],[f37])).
% 3.39/0.99  
% 3.39/0.99  fof(f76,plain,(
% 3.39/0.99    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),
% 3.39/0.99    inference(definition_unfolding,[],[f64,f52,f70])).
% 3.39/0.99  
% 3.39/0.99  cnf(c_0,plain,
% 3.39/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.39/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_16,negated_conjecture,
% 3.39/0.99      ( r2_hidden(sK5,sK2) ),
% 3.39/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_385,plain,
% 3.39/0.99      ( r2_hidden(sK5,sK2) = iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_14,plain,
% 3.39/0.99      ( ~ r2_hidden(X0,X1)
% 3.39/0.99      | ~ r2_hidden(X2,X1)
% 3.39/0.99      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
% 3.39/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_386,plain,
% 3.39/0.99      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
% 3.39/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.39/0.99      | r2_hidden(X1,X2) != iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_763,plain,
% 3.39/0.99      ( k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0),k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0),sK2)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0)
% 3.39/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_385,c_386]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1213,plain,
% 3.39/0.99      ( k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK2)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_385,c_763]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_17,negated_conjecture,
% 3.39/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 3.39/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_767,plain,
% 3.39/0.99      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
% 3.39/0.99      inference(demodulation,[status(thm)],[c_0,c_17]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1214,plain,
% 3.39/0.99      ( k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),sK2)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
% 3.39/0.99      inference(light_normalisation,[status(thm)],[c_1213,c_767]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_11,plain,
% 3.39/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 3.39/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1345,plain,
% 3.39/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_1214,c_11]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1465,plain,
% 3.39/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_0,c_1345]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_18,negated_conjecture,
% 3.39/0.99      ( r1_tarski(sK2,sK3) ),
% 3.39/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_384,plain,
% 3.39/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_10,plain,
% 3.39/0.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.39/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_388,plain,
% 3.39/0.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1606,plain,
% 3.39/0.99      ( k2_xboole_0(sK2,sK3) = sK3 ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_384,c_388]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_12,plain,
% 3.39/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 3.39/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_2079,plain,
% 3.39/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_1606,c_12]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_6843,plain,
% 3.39/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
% 3.39/0.99      inference(light_normalisation,[status(thm)],[c_1465,c_2079]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_15,negated_conjecture,
% 3.39/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 3.39/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_431,plain,
% 3.39/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 3.39/0.99      inference(light_normalisation,[status(thm)],[c_15,c_17]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_766,plain,
% 3.39/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 3.39/0.99      inference(demodulation,[status(thm)],[c_0,c_431]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_6865,plain,
% 3.39/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 3.39/0.99      inference(demodulation,[status(thm)],[c_6843,c_766]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1426,plain,
% 3.39/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 3.39/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(contradiction,plain,
% 3.39/0.99      ( $false ),
% 3.39/0.99      inference(minisat,[status(thm)],[c_6865,c_1426]) ).
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/0.99  
% 3.39/0.99  ------                               Statistics
% 3.39/0.99  
% 3.39/0.99  ------ General
% 3.39/0.99  
% 3.39/0.99  abstr_ref_over_cycles:                  0
% 3.39/0.99  abstr_ref_under_cycles:                 0
% 3.39/0.99  gc_basic_clause_elim:                   0
% 3.39/0.99  forced_gc_time:                         0
% 3.39/0.99  parsing_time:                           0.01
% 3.39/0.99  unif_index_cands_time:                  0.
% 3.39/0.99  unif_index_add_time:                    0.
% 3.39/0.99  orderings_time:                         0.
% 3.39/0.99  out_proof_time:                         0.007
% 3.39/0.99  total_time:                             0.327
% 3.39/0.99  num_of_symbols:                         43
% 3.39/0.99  num_of_terms:                           10361
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing
% 3.39/0.99  
% 3.39/0.99  num_of_splits:                          0
% 3.39/0.99  num_of_split_atoms:                     0
% 3.39/0.99  num_of_reused_defs:                     0
% 3.39/0.99  num_eq_ax_congr_red:                    12
% 3.39/0.99  num_of_sem_filtered_clauses:            1
% 3.39/0.99  num_of_subtypes:                        0
% 3.39/0.99  monotx_restored_types:                  0
% 3.39/0.99  sat_num_of_epr_types:                   0
% 3.39/0.99  sat_num_of_non_cyclic_types:            0
% 3.39/0.99  sat_guarded_non_collapsed_types:        0
% 3.39/0.99  num_pure_diseq_elim:                    0
% 3.39/0.99  simp_replaced_by:                       0
% 3.39/0.99  res_preprocessed:                       70
% 3.39/0.99  prep_upred:                             0
% 3.39/0.99  prep_unflattend:                        0
% 3.39/0.99  smt_new_axioms:                         0
% 3.39/0.99  pred_elim_cands:                        2
% 3.39/0.99  pred_elim:                              0
% 3.39/0.99  pred_elim_cl:                           0
% 3.39/0.99  pred_elim_cycles:                       1
% 3.39/0.99  merged_defs:                            0
% 3.39/0.99  merged_defs_ncl:                        0
% 3.39/0.99  bin_hyper_res:                          0
% 3.39/0.99  prep_cycles:                            3
% 3.39/0.99  pred_elim_time:                         0.
% 3.39/0.99  splitting_time:                         0.
% 3.39/0.99  sem_filter_time:                        0.
% 3.39/0.99  monotx_time:                            0.001
% 3.39/0.99  subtype_inf_time:                       0.
% 3.39/0.99  
% 3.39/0.99  ------ Problem properties
% 3.39/0.99  
% 3.39/0.99  clauses:                                19
% 3.39/0.99  conjectures:                            4
% 3.39/0.99  epr:                                    2
% 3.39/0.99  horn:                                   14
% 3.39/0.99  ground:                                 4
% 3.39/0.99  unary:                                  9
% 3.39/0.99  binary:                                 5
% 3.39/0.99  lits:                                   35
% 3.39/0.99  lits_eq:                                12
% 3.39/0.99  fd_pure:                                0
% 3.39/0.99  fd_pseudo:                              0
% 3.39/0.99  fd_cond:                                1
% 3.39/0.99  fd_pseudo_cond:                         3
% 3.39/0.99  ac_symbols:                             0
% 3.39/0.99  
% 3.39/0.99  ------ Propositional Solver
% 3.39/0.99  
% 3.39/0.99  prop_solver_calls:                      24
% 3.39/0.99  prop_fast_solver_calls:                 390
% 3.39/0.99  smt_solver_calls:                       0
% 3.39/0.99  smt_fast_solver_calls:                  0
% 3.39/0.99  prop_num_of_clauses:                    3104
% 3.39/0.99  prop_preprocess_simplified:             5409
% 3.39/0.99  prop_fo_subsumed:                       0
% 3.39/0.99  prop_solver_time:                       0.
% 3.39/0.99  smt_solver_time:                        0.
% 3.39/0.99  smt_fast_solver_time:                   0.
% 3.39/0.99  prop_fast_solver_time:                  0.
% 3.39/0.99  prop_unsat_core_time:                   0.
% 3.39/0.99  
% 3.39/0.99  ------ QBF
% 3.39/0.99  
% 3.39/0.99  qbf_q_res:                              0
% 3.39/0.99  qbf_num_tautologies:                    0
% 3.39/0.99  qbf_prep_cycles:                        0
% 3.39/0.99  
% 3.39/0.99  ------ BMC1
% 3.39/0.99  
% 3.39/0.99  bmc1_current_bound:                     -1
% 3.39/0.99  bmc1_last_solved_bound:                 -1
% 3.39/0.99  bmc1_unsat_core_size:                   -1
% 3.39/0.99  bmc1_unsat_core_parents_size:           -1
% 3.39/0.99  bmc1_merge_next_fun:                    0
% 3.39/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.39/0.99  
% 3.39/0.99  ------ Instantiation
% 3.39/0.99  
% 3.39/0.99  inst_num_of_clauses:                    783
% 3.39/0.99  inst_num_in_passive:                    198
% 3.39/0.99  inst_num_in_active:                     310
% 3.39/0.99  inst_num_in_unprocessed:                275
% 3.39/0.99  inst_num_of_loops:                      350
% 3.39/0.99  inst_num_of_learning_restarts:          0
% 3.39/0.99  inst_num_moves_active_passive:          37
% 3.39/0.99  inst_lit_activity:                      0
% 3.39/0.99  inst_lit_activity_moves:                0
% 3.39/0.99  inst_num_tautologies:                   0
% 3.39/0.99  inst_num_prop_implied:                  0
% 3.39/0.99  inst_num_existing_simplified:           0
% 3.39/0.99  inst_num_eq_res_simplified:             0
% 3.39/0.99  inst_num_child_elim:                    0
% 3.39/0.99  inst_num_of_dismatching_blockings:      556
% 3.39/0.99  inst_num_of_non_proper_insts:           770
% 3.39/0.99  inst_num_of_duplicates:                 0
% 3.39/0.99  inst_inst_num_from_inst_to_res:         0
% 3.39/0.99  inst_dismatching_checking_time:         0.
% 3.39/0.99  
% 3.39/0.99  ------ Resolution
% 3.39/0.99  
% 3.39/0.99  res_num_of_clauses:                     0
% 3.39/0.99  res_num_in_passive:                     0
% 3.39/0.99  res_num_in_active:                      0
% 3.39/0.99  res_num_of_loops:                       73
% 3.39/0.99  res_forward_subset_subsumed:            44
% 3.39/0.99  res_backward_subset_subsumed:           0
% 3.39/0.99  res_forward_subsumed:                   0
% 3.39/0.99  res_backward_subsumed:                  0
% 3.39/0.99  res_forward_subsumption_resolution:     0
% 3.39/0.99  res_backward_subsumption_resolution:    0
% 3.39/0.99  res_clause_to_clause_subsumption:       1912
% 3.39/0.99  res_orphan_elimination:                 0
% 3.39/0.99  res_tautology_del:                      50
% 3.39/0.99  res_num_eq_res_simplified:              0
% 3.39/0.99  res_num_sel_changes:                    0
% 3.39/0.99  res_moves_from_active_to_pass:          0
% 3.39/0.99  
% 3.39/0.99  ------ Superposition
% 3.39/0.99  
% 3.39/0.99  sup_time_total:                         0.
% 3.39/0.99  sup_time_generating:                    0.
% 3.39/0.99  sup_time_sim_full:                      0.
% 3.39/0.99  sup_time_sim_immed:                     0.
% 3.39/0.99  
% 3.39/0.99  sup_num_of_clauses:                     265
% 3.39/0.99  sup_num_in_active:                      45
% 3.39/0.99  sup_num_in_passive:                     220
% 3.39/0.99  sup_num_of_loops:                       69
% 3.39/0.99  sup_fw_superposition:                   334
% 3.39/0.99  sup_bw_superposition:                   162
% 3.39/0.99  sup_immediate_simplified:               76
% 3.39/0.99  sup_given_eliminated:                   0
% 3.39/0.99  comparisons_done:                       0
% 3.39/0.99  comparisons_avoided:                    3
% 3.39/0.99  
% 3.39/0.99  ------ Simplifications
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  sim_fw_subset_subsumed:                 0
% 3.39/0.99  sim_bw_subset_subsumed:                 0
% 3.39/0.99  sim_fw_subsumed:                        53
% 3.39/0.99  sim_bw_subsumed:                        5
% 3.39/0.99  sim_fw_subsumption_res:                 1
% 3.39/0.99  sim_bw_subsumption_res:                 0
% 3.39/0.99  sim_tautology_del:                      10
% 3.39/0.99  sim_eq_tautology_del:                   2
% 3.39/0.99  sim_eq_res_simp:                        0
% 3.39/0.99  sim_fw_demodulated:                     15
% 3.39/0.99  sim_bw_demodulated:                     24
% 3.39/0.99  sim_light_normalised:                   8
% 3.39/0.99  sim_joinable_taut:                      0
% 3.39/0.99  sim_joinable_simp:                      0
% 3.39/0.99  sim_ac_normalised:                      0
% 3.39/0.99  sim_smt_subsumption:                    0
% 3.39/0.99  
%------------------------------------------------------------------------------
