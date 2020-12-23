%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0222+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:45 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   34 (  52 expanded)
%              Number of clauses        :   14 (  15 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 197 expanded)
%              Number of equality atoms :   49 ( 107 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f7])).

fof(f9,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f13,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        & X0 != X1 )
   => ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
      & sK1 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    & sK1 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f6,f11])).

fof(f19,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f14])).

fof(f21,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f20])).

fof(f18,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_399,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK2))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_266,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_268,plain,
    ( k1_tarski(sK1) = k1_tarski(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_4,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_5,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_73,plain,
    ( r2_hidden(X0,X1)
    | k1_tarski(X0) != k1_tarski(sK1)
    | k1_tarski(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_74,plain,
    ( r2_hidden(X0,k1_tarski(sK2))
    | k1_tarski(X0) != k1_tarski(sK1) ),
    inference(unflattening,[status(thm)],[c_73])).

cnf(c_76,plain,
    ( r2_hidden(sK1,k1_tarski(sK2))
    | k1_tarski(sK1) != k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_15,plain,
    ( r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_399,c_268,c_76,c_15,c_12,c_6])).


%------------------------------------------------------------------------------
