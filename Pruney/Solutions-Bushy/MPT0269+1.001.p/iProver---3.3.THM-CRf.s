%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0269+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:53 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   31 (  41 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 119 expanded)
%              Number of equality atoms :   69 ( 105 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f6])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( k1_tarski(sK1) != sK0
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( k1_tarski(sK1) != sK0
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f9])).

fof(f18,plain,(
    k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_122,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_163,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_123,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_158,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) != X0
    | k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_162,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) != k4_xboole_0(sK0,k1_tarski(sK1))
    | k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_45,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_101,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != k1_xboole_0
    | k1_tarski(X3) != X2
    | k1_tarski(X3) = X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_45])).

cnf(c_102,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) != k1_xboole_0
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_101])).

cnf(c_145,plain,
    ( k4_xboole_0(sK0,k1_tarski(X0)) != k1_xboole_0
    | k1_tarski(X0) = sK0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_153,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) != k1_xboole_0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_5,negated_conjecture,
    ( k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_163,c_162,c_153,c_5,c_6,c_7])).


%------------------------------------------------------------------------------
