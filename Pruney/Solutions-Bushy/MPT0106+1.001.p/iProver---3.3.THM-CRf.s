%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0106+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:29 EST 2020

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   20 (  23 expanded)
%              Number of clauses        :    7 (   8 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   21 (  24 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(ennf_transformation,[],[f5])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))
   => k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f12,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f12,f9])).

cnf(c_0,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_1,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_19,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_37,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X4,X2))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X3,X4)),X2) ),
    inference(superposition,[status(thm)],[c_0,c_19])).

cnf(c_2,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_247,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(demodulation,[status(thm)],[c_37,c_2])).

cnf(c_295,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_247])).


%------------------------------------------------------------------------------
