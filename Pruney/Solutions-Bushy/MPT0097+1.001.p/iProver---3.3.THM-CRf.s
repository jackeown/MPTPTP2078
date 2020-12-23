%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0097+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:28 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :   10
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f6,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f10,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_1,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_2,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_28,plain,
    ( k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_29,plain,
    ( k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_28])).

cnf(c_39,plain,
    ( k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(X0_34,sK1) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_45,plain,
    ( k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_40,plain,
    ( k4_xboole_0(X0_34,k3_xboole_0(X0_34,X0_35)) = k4_xboole_0(X0_34,X0_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_44,plain,
    ( k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45,c_44])).


%------------------------------------------------------------------------------
