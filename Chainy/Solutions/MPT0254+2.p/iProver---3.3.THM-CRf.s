%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0254+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:30 EST 2020

% Result     : Theorem 11.48s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 263 expanded)
%              Number of clauses        :   25 (  75 expanded)
%              Number of leaves         :   13 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :   68 ( 272 expanded)
%              Number of equality atoms :   67 ( 271 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f863,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f657,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1278,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f863,f657])).

fof(f350,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f351,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f350])).

fof(f507,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f351])).

fof(f648,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
   => k2_xboole_0(k1_tarski(sK35),sK36) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f649,plain,(
    k2_xboole_0(k1_tarski(sK35),sK36) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f507,f648])).

fof(f1133,plain,(
    k2_xboole_0(k1_tarski(sK35),sK36) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f649])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f865,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f805,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1137,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f865,f805])).

fof(f1454,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK35),sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36))) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f1133,f1137,f657])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f862,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f654,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f732,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1148,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f732,f805])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f819,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1251,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f819,f657])).

fof(f320,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f636,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f320])).

fof(f1081,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f636])).

fof(f1525,plain,(
    ! [X1] : k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1) ),
    inference(equality_resolution,[],[f1081])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f782,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1224,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f782,f805,f657,f657])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f795,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1232,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f795,f657])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1278])).

cnf(c_471,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1454])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f862])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f654])).

cnf(c_8249,negated_conjecture,
    ( k5_xboole_0(sK36,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36)))) = o_0_0_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_471,c_211,c_7])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1148])).

cnf(c_14522,plain,
    ( k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),sK36)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8249,c_1])).

cnf(c_17342,plain,
    ( k5_xboole_0(sK36,k5_xboole_0(k4_xboole_0(k1_tarski(sK35),sK36),X0)) = k5_xboole_0(o_0_0_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_14522,c_211])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1251])).

cnf(c_16885,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_17353,plain,
    ( k5_xboole_0(sK36,k5_xboole_0(k4_xboole_0(k1_tarski(sK35),sK36),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_17342,c_16885])).

cnf(c_17416,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) = k5_xboole_0(sK36,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_212,c_17353])).

cnf(c_17422,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) = sK36 ),
    inference(demodulation,[status(thm)],[c_17416,c_168])).

cnf(c_17743,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36)) = k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(superposition,[status(thm)],[c_17422,c_1])).

cnf(c_17748,plain,
    ( k5_xboole_0(k1_tarski(sK35),sK36) = sK36 ),
    inference(light_normalisation,[status(thm)],[c_17743,c_17422])).

cnf(c_17424,plain,
    ( k5_xboole_0(sK36,k5_xboole_0(sK36,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_17422,c_17353])).

cnf(c_17434,plain,
    ( k5_xboole_0(sK36,k5_xboole_0(X0,sK36)) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_17424])).

cnf(c_18628,plain,
    ( k5_xboole_0(sK36,sK36) = k1_tarski(sK35) ),
    inference(superposition,[status(thm)],[c_17748,c_17434])).

cnf(c_18630,plain,
    ( k1_tarski(sK35) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18628,c_212])).

cnf(c_420,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1525])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1224])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1232])).

cnf(c_14294,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_14302,plain,
    ( k1_tarski(X0) != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_420,c_14294])).

cnf(c_21317,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18630,c_14302])).

%------------------------------------------------------------------------------
