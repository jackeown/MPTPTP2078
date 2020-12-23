%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0334+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:02 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :   34 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
        & X0 != X1 )
   => ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f13,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

cnf(c_0,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_33,plain,
    ( X0 = X1
    | k4_xboole_0(k2_xboole_0(X2,X3),X4) = k2_xboole_0(k4_xboole_0(X2,X4),X3)
    | k1_tarski(X1) != X4
    | k1_tarski(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_34,plain,
    ( X0 = X1
    | k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ),
    inference(unflattening,[status(thm)],[c_33])).

cnf(c_72,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_tarski(sK0)),k1_tarski(sK1)) = k2_xboole_0(k4_xboole_0(X0,k1_tarski(sK1)),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_89,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) = k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_2,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_3,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_89,c_2,c_3])).


%------------------------------------------------------------------------------
