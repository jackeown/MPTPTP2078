%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0120+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:31 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   12 (  15 expanded)
%              Number of clauses        :    4 (   5 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   13 (  16 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    inference(negated_conjecture,[],[f2])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    inference(ennf_transformation,[],[f3])).

fof(f5,plain,
    ( ? [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
   => k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).

fof(f8,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_1,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_11,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(demodulation,[status(thm)],[c_0,c_1])).

cnf(c_12,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_0,c_11])).


%------------------------------------------------------------------------------
