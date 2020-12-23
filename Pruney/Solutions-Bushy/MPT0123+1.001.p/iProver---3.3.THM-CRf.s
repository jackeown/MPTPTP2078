%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0123+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:32 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   21 (  24 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   22 (  25 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f13,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_2,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_19,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_3,negated_conjecture,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_10,negated_conjecture,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(theory_normalisation,[status(thm)],[c_3,c_2,c_0])).

cnf(c_21,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_19,c_10])).

cnf(c_22,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_21])).


%------------------------------------------------------------------------------
