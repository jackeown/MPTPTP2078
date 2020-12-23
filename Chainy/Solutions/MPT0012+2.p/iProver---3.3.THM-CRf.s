%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0012+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f45])).

fof(f76,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f46])).

fof(f125,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
   => k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) != k2_xboole_0(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK15)) ),
    introduced(choice_axiom,[])).

fof(f126,plain,(
    k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) != k2_xboole_0(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK15)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f76,f125])).

fof(f201,plain,(
    k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) != k2_xboole_0(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK15)) ),
    inference(cnf_transformation,[],[f126])).

fof(f44,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f200,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f129,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f162,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_72,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) != k2_xboole_0(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK15)) ),
    inference(cnf_transformation,[],[f201])).

cnf(c_71,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f200])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1310,negated_conjecture,
    ( k2_xboole_0(sK13,k2_xboole_0(sK14,k2_xboole_0(sK15,sK15))) != k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)) ),
    inference(theory_normalisation,[status(thm)],[c_72,c_71,c_2])).

cnf(c_33,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f162])).

cnf(c_2618,plain,
    ( k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)) != k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)) ),
    inference(demodulation,[status(thm)],[c_1310,c_33])).

cnf(c_2619,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2618])).

%------------------------------------------------------------------------------
