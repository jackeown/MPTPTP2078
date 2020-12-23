%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0332+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:01 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   24 (  34 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  85 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f13,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_0,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(X1,k2_tarski(X0,X2)) = X1 ),
    inference(cnf_transformation,[],[f9])).

cnf(c_43,plain,
    ( r2_hidden(X0_35,X0_36)
    | r2_hidden(X1_35,X0_36)
    | k4_xboole_0(X0_36,k2_tarski(X0_35,X1_35)) = X0_36 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_179,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(sK2,k2_tarski(sK0,sK1)) = sK2 ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_2,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_41,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) != sK2 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_42,plain,
    ( k4_xboole_0(k2_xboole_0(X0_36,X0_37),X0_37) = k4_xboole_0(X0_36,X0_37) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_122,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2 ),
    inference(demodulation,[status(thm)],[c_41,c_42])).

cnf(c_3,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_179,c_122,c_3,c_4])).


%------------------------------------------------------------------------------
