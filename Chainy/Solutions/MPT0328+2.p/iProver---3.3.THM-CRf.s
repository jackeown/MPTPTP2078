%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0328+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:35 EST 2020

% Result     : Theorem 15.35s
% Output     : CNFRefutation 15.35s
% Verified   : 
% Statistics : Number of formulae       :   42 (  85 expanded)
%              Number of clauses        :   16 (  24 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 ( 106 expanded)
%              Number of equality atoms :   42 (  86 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f405,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f833,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f405])).

fof(f1439,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f833])).

fof(f353,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f354,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f353])).

fof(f604,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f354])).

fof(f817,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & ~ r2_hidden(X0,X1) )
   => ( k4_xboole_0(k2_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54)) != sK55
      & ~ r2_hidden(sK54,sK55) ) ),
    introduced(choice_axiom,[])).

fof(f818,plain,
    ( k4_xboole_0(k2_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54)) != sK55
    & ~ r2_hidden(sK54,sK55) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK54,sK55])],[f604,f817])).

fof(f1361,plain,(
    ~ r2_hidden(sK54,sK55) ),
    inference(cnf_transformation,[],[f818])).

fof(f1362,plain,(
    k4_xboole_0(k2_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54)) != sK55 ),
    inference(cnf_transformation,[],[f818])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1069,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1009,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1488,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1069,f1009])).

fof(f1798,plain,(
    k4_xboole_0(k5_xboole_0(k5_xboole_0(sK55,k1_tarski(sK54)),k4_xboole_0(sK55,k4_xboole_0(sK55,k1_tarski(sK54)))),k1_tarski(sK54)) != sK55 ),
    inference(definition_unfolding,[],[f1362,f1488])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1066,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f858,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1073,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1632,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1073,f1488])).

fof(f102,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1001,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f102])).

fof(f1585,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f1001,f1488])).

cnf(c_572,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f1439])).

cnf(c_14085,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_496,negated_conjecture,
    ( ~ r2_hidden(sK54,sK55) ),
    inference(cnf_transformation,[],[f1361])).

cnf(c_14112,plain,
    ( r2_hidden(sK54,sK55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_37717,plain,
    ( k4_xboole_0(sK55,k1_tarski(sK54)) = sK55 ),
    inference(superposition,[status(thm)],[c_14085,c_14112])).

cnf(c_495,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(sK55,k1_tarski(sK54)),k4_xboole_0(sK55,k4_xboole_0(sK55,k1_tarski(sK54)))),k1_tarski(sK54)) != sK55 ),
    inference(cnf_transformation,[],[f1798])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1066])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f858])).

cnf(c_6923,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(sK55,k5_xboole_0(k1_tarski(sK54),k4_xboole_0(sK55,k4_xboole_0(sK55,k1_tarski(sK54))))),k1_tarski(sK54)) != sK55 ),
    inference(theory_normalisation,[status(thm)],[c_495,c_211,c_7])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1632])).

cnf(c_7041,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_147,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1585])).

cnf(c_7068,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X1) = k4_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_147,c_211,c_7])).

cnf(c_14926,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7068,c_7041])).

cnf(c_15057,plain,
    ( k4_xboole_0(sK55,k1_tarski(sK54)) != sK55 ),
    inference(demodulation,[status(thm)],[c_6923,c_7041,c_14926])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37717,c_15057])).

%------------------------------------------------------------------------------
