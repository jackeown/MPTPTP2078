%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0013+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:11 EST 2020

% Result     : Theorem 1.28s
% Output     : CNFRefutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f163,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

fof(f44,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f201,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f44])).

fof(f47,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f47])).

fof(f78,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f48])).

fof(f126,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k2_xboole_0(X0,X1))
   => k2_xboole_0(sK13,sK14) != k2_xboole_0(sK13,k2_xboole_0(sK13,sK14)) ),
    introduced(choice_axiom,[])).

fof(f127,plain,(
    k2_xboole_0(sK13,sK14) != k2_xboole_0(sK13,k2_xboole_0(sK13,sK14)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f78,f126])).

fof(f204,plain,(
    k2_xboole_0(sK13,sK14) != k2_xboole_0(sK13,k2_xboole_0(sK13,sK14)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_33,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f163])).

cnf(c_71,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f201])).

cnf(c_3055,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_33,c_71])).

cnf(c_74,negated_conjecture,
    ( k2_xboole_0(sK13,sK14) != k2_xboole_0(sK13,k2_xboole_0(sK13,sK14)) ),
    inference(cnf_transformation,[],[f204])).

cnf(c_3554,plain,
    ( k2_xboole_0(sK13,sK14) != k2_xboole_0(sK13,sK14) ),
    inference(demodulation,[status(thm)],[c_3055,c_74])).

cnf(c_3556,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3554])).

%------------------------------------------------------------------------------
