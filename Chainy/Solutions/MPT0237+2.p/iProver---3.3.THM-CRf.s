%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0237+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:29 EST 2020

% Result     : Theorem 10.98s
% Output     : CNFRefutation 10.98s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 107 expanded)
%              Number of clauses        :   12 (  24 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   38 ( 108 expanded)
%              Number of equality atoms :   37 ( 107 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f326,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f325])).

fof(f467,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f326])).

fof(f586,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK28,sK29) != k3_tarski(k2_tarski(k1_tarski(sK28),k1_tarski(sK29))) ),
    introduced(choice_axiom,[])).

fof(f587,plain,(
    k2_tarski(sK28,sK29) != k3_tarski(k2_tarski(k1_tarski(sK28),k1_tarski(sK29))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29])],[f467,f586])).

fof(f1016,plain,(
    k2_tarski(sK28,sK29) != k3_tarski(k2_tarski(k1_tarski(sK28),k1_tarski(sK29))) ),
    inference(cnf_transformation,[],[f587])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f899,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f803,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f743,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1020,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f803,f743])).

fof(f1021,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f899,f1020])).

fof(f1307,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)))) != k3_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(k1_tarski(sK28)),k1_tarski(k1_tarski(sK29))),k4_xboole_0(k1_tarski(k1_tarski(sK28)),k4_xboole_0(k1_tarski(k1_tarski(sK28)),k1_tarski(k1_tarski(sK29)))))) ),
    inference(definition_unfolding,[],[f1016,f1021,f1021])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f800,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f592,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f807,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1164,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f807,f1020])).

fof(f302,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f992,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f302])).

fof(f1289,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))) ),
    inference(definition_unfolding,[],[f992,f1020,f1021])).

cnf(c_416,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)))) != k3_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(k1_tarski(sK28)),k1_tarski(k1_tarski(sK29))),k4_xboole_0(k1_tarski(k1_tarski(sK28)),k4_xboole_0(k1_tarski(k1_tarski(sK28)),k1_tarski(k1_tarski(sK29)))))) ),
    inference(cnf_transformation,[],[f1307])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f800])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f592])).

cnf(c_7605,negated_conjecture,
    ( k3_tarski(k5_xboole_0(k1_tarski(k1_tarski(sK28)),k5_xboole_0(k1_tarski(k1_tarski(sK29)),k4_xboole_0(k1_tarski(k1_tarski(sK28)),k4_xboole_0(k1_tarski(k1_tarski(sK28)),k1_tarski(k1_tarski(sK29))))))) != k5_xboole_0(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29))))) ),
    inference(theory_normalisation,[status(thm)],[c_416,c_211,c_7])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1164])).

cnf(c_7723,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_392,plain,
    ( k3_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f1289])).

cnf(c_7618,plain,
    ( k3_tarski(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(theory_normalisation,[status(thm)],[c_392,c_211,c_7])).

cnf(c_13850,plain,
    ( k3_tarski(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7618,c_7723])).

cnf(c_13851,plain,
    ( k3_tarski(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_13850,c_7723])).

cnf(c_14148,plain,
    ( k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))) != k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))) ),
    inference(demodulation,[status(thm)],[c_7605,c_7723,c_13851])).

cnf(c_14149,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14148])).

%------------------------------------------------------------------------------
