%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0108+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:22 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   33 (  75 expanded)
%              Number of clauses        :   11 (  19 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  76 expanded)
%              Number of equality atoms :   33 (  75 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f46])).

fof(f177,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f47])).

fof(f304,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK13,sK14) != k4_xboole_0(k2_xboole_0(sK13,sK14),k3_xboole_0(sK13,sK14)) ),
    introduced(choice_axiom,[])).

fof(f305,plain,(
    k5_xboole_0(sK13,sK14) != k4_xboole_0(k2_xboole_0(sK13,sK14),k3_xboole_0(sK13,sK14)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f177,f304])).

fof(f390,plain,(
    k5_xboole_0(sK13,sK14) != k4_xboole_0(k2_xboole_0(sK13,sK14),k3_xboole_0(sK13,sK14)) ),
    inference(cnf_transformation,[],[f305])).

fof(f148,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f500,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f148])).

fof(f507,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f500,f440])).

fof(f92,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f440,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f92])).

fof(f544,plain,(
    k5_xboole_0(sK13,sK14) != k4_xboole_0(k5_xboole_0(k5_xboole_0(sK13,sK14),k4_xboole_0(sK13,k4_xboole_0(sK13,sK14))),k4_xboole_0(sK13,k4_xboole_0(sK13,sK14))) ),
    inference(definition_unfolding,[],[f390,f507,f440])).

fof(f145,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f497,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f145])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f316,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f152,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f504,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f152])).

fof(f627,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f504,f507])).

fof(f44,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f388,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f543,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f388,f507,f440])).

cnf(c_77,negated_conjecture,
    ( k5_xboole_0(sK13,sK14) != k4_xboole_0(k5_xboole_0(k5_xboole_0(sK13,sK14),k4_xboole_0(sK13,k4_xboole_0(sK13,sK14))),k4_xboole_0(sK13,k4_xboole_0(sK13,sK14))) ),
    inference(cnf_transformation,[],[f544])).

cnf(c_183,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f497])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f316])).

cnf(c_2981,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(sK13,k5_xboole_0(sK14,k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)))),k4_xboole_0(sK13,k4_xboole_0(sK13,sK14))) != k5_xboole_0(sK13,sK14) ),
    inference(theory_normalisation,[status(thm)],[c_77,c_183,c_6])).

cnf(c_189,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f627])).

cnf(c_2935,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_189,c_183,c_6])).

cnf(c_76,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f543])).

cnf(c_2982,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_76,c_183,c_6])).

cnf(c_6091,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2982,c_2935])).

cnf(c_6139,plain,
    ( k5_xboole_0(sK13,sK14) != k5_xboole_0(sK13,sK14) ),
    inference(demodulation,[status(thm)],[c_2981,c_2935,c_6091])).

cnf(c_6140,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6139])).

%------------------------------------------------------------------------------
