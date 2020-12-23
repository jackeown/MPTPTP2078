%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0217+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:45 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   36 (  72 expanded)
%              Number of clauses        :   17 (  20 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  141 ( 413 expanded)
%              Number of equality atoms :  110 ( 312 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f5])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f6])).

fof(f8,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).

fof(f13,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f13])).

fof(f24,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f23])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) )
   => ( sK1 != sK4
      & sK1 != sK3
      & k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f4,f10])).

fof(f18,plain,(
    k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f12])).

fof(f20,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_289,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,negated_conjecture,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_288,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_788,plain,
    ( sK3 = X0
    | sK4 = X0
    | r2_hidden(X0,k2_tarski(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_288])).

cnf(c_811,plain,
    ( sK3 = sK1
    | sK4 = sK1 ),
    inference(superposition,[status(thm)],[c_289,c_788])).

cnf(c_184,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_345,plain,
    ( sK3 != X0
    | sK1 != X0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_346,plain,
    ( sK3 != sK1
    | sK1 = sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_343,plain,
    ( sK4 != X0
    | sK1 != X0
    | sK1 = sK4 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_344,plain,
    ( sK4 != sK1
    | sK1 = sK4
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_13,plain,
    ( r2_hidden(sK1,k2_tarski(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,negated_conjecture,
    ( sK1 != sK4 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_811,c_346,c_344,c_13,c_10,c_6,c_7])).


%------------------------------------------------------------------------------
