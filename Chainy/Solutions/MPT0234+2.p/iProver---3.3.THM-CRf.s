%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0234+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :   38 (  54 expanded)
%              Number of clauses        :   12 (  14 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 (  74 expanded)
%              Number of equality atoms :   50 (  73 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f310,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f578,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f310])).

fof(f994,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f578])).

fof(f319,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f320,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f319])).

fof(f460,plain,(
    ? [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1)
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f320])).

fof(f579,plain,
    ( ? [X0,X1] :
        ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1)
        & X0 != X1 )
   => ( k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) != k2_tarski(sK28,sK29)
      & sK28 != sK29 ) ),
    introduced(choice_axiom,[])).

fof(f580,plain,
    ( k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) != k2_tarski(sK28,sK29)
    & sK28 != sK29 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29])],[f460,f579])).

fof(f1004,plain,(
    k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) != k2_tarski(sK28,sK29) ),
    inference(cnf_transformation,[],[f580])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f892,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f796,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f736,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1009,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f796,f736])).

fof(f1010,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f892,f1009])).

fof(f1292,plain,(
    k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) != k5_xboole_0(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)))) ),
    inference(definition_unfolding,[],[f1004,f1010])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f793,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f585,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f800,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1153,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f800,f1009])).

fof(f1003,plain,(
    sK28 != sK29 ),
    inference(cnf_transformation,[],[f580])).

cnf(c_400,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f994])).

cnf(c_410,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) != k5_xboole_0(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)))) ),
    inference(cnf_transformation,[],[f1292])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f793])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f585])).

cnf(c_4567,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29))))) != k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(theory_normalisation,[status(thm)],[c_410,c_211,c_7])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1153])).

cnf(c_4682,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_10362,plain,
    ( k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))) != k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(demodulation,[status(thm)],[c_4567,c_4682])).

cnf(c_13395,plain,
    ( sK29 = sK28 ),
    inference(superposition,[status(thm)],[c_400,c_10362])).

cnf(c_411,negated_conjecture,
    ( sK28 != sK29 ),
    inference(cnf_transformation,[],[f1003])).

cnf(c_13723,plain,
    ( sK28 != sK28 ),
    inference(demodulation,[status(thm)],[c_13395,c_411])).

cnf(c_13724,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_13723])).

%------------------------------------------------------------------------------
