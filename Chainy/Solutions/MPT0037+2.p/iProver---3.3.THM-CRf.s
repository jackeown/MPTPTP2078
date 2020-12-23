%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0037+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:14 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   50 (  61 expanded)
%              Number of clauses        :   23 (  25 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 (  80 expanded)
%              Number of equality atoms :   49 (  61 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f64])).

fof(f118,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f175,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( k2_xboole_0(sK15,k3_xboole_0(sK17,sK16)) != k3_xboole_0(k2_xboole_0(sK15,sK17),sK16)
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f176,plain,
    ( k2_xboole_0(sK15,k3_xboole_0(sK17,sK16)) != k3_xboole_0(k2_xboole_0(sK15,sK17),sK16)
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f118,f175])).

fof(f274,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f176])).

fof(f60,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f117,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f270,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f180,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f213,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f77])).

fof(f55,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f265,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f179,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f263,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

fof(f56,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f266,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f275,plain,(
    k2_xboole_0(sK15,k3_xboole_0(sK17,sK16)) != k3_xboole_0(k2_xboole_0(sK15,sK17),sK16) ),
    inference(cnf_transformation,[],[f176])).

fof(f46,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f254,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f277,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_96,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f274])).

cnf(c_3293,plain,
    ( r1_tarski(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_96])).

cnf(c_91,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f270])).

cnf(c_3296,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_91])).

cnf(c_10215,plain,
    ( k3_xboole_0(sK15,sK16) = sK15 ),
    inference(superposition,[status(thm)],[c_3293,c_3296])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f180])).

cnf(c_34,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f213])).

cnf(c_86,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f265])).

cnf(c_5824,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_34,c_86])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f179])).

cnf(c_84,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f263])).

cnf(c_4062,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_84])).

cnf(c_5915,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5824,c_4062])).

cnf(c_6304,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
    inference(superposition,[status(thm)],[c_3,c_5915])).

cnf(c_11357,plain,
    ( k2_xboole_0(sK15,sK16) = sK16 ),
    inference(superposition,[status(thm)],[c_10215,c_6304])).

cnf(c_87,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f266])).

cnf(c_12315,plain,
    ( k3_xboole_0(sK16,k2_xboole_0(sK15,X0)) = k2_xboole_0(sK15,k3_xboole_0(sK16,X0)) ),
    inference(superposition,[status(thm)],[c_11357,c_87])).

cnf(c_95,negated_conjecture,
    ( k2_xboole_0(sK15,k3_xboole_0(sK17,sK16)) != k3_xboole_0(k2_xboole_0(sK15,sK17),sK16) ),
    inference(cnf_transformation,[],[f275])).

cnf(c_75,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f254])).

cnf(c_98,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f277])).

cnf(c_1747,negated_conjecture,
    ( k3_xboole_0(sK16,k2_xboole_0(sK15,sK17)) != k2_xboole_0(sK15,k3_xboole_0(sK17,sK16)) ),
    inference(theory_normalisation,[status(thm)],[c_95,c_75,c_3,c_98,c_2])).

cnf(c_22665,plain,
    ( k2_xboole_0(sK15,k3_xboole_0(sK16,sK17)) != k2_xboole_0(sK15,k3_xboole_0(sK17,sK16)) ),
    inference(demodulation,[status(thm)],[c_12315,c_1747])).

cnf(c_22669,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_22665])).

%------------------------------------------------------------------------------
