%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0226+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:28 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :   30 (  37 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 101 expanded)
%              Number of equality atoms :   59 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f310,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f309])).

fof(f442,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f310])).

fof(f557,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK28 != sK29
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) ) ),
    introduced(choice_axiom,[])).

fof(f558,plain,
    ( sK28 != sK29
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29])],[f442,f557])).

fof(f964,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(cnf_transformation,[],[f558])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f566,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1237,plain,(
    o_0_0_xboole_0 = k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(definition_unfolding,[],[f964,f566])).

fof(f297,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f553,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f297])).

fof(f948,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f553])).

fof(f1227,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(definition_unfolding,[],[f948,f566])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f517,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f518,plain,(
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
    inference(rectify,[],[f517])).

fof(f519,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK20(X0,X1) != X0
          | ~ r2_hidden(sK20(X0,X1),X1) )
        & ( sK20(X0,X1) = X0
          | r2_hidden(sK20(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f520,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK20(X0,X1) != X0
            | ~ r2_hidden(sK20(X0,X1),X1) )
          & ( sK20(X0,X1) = X0
            | r2_hidden(sK20(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f518,f519])).

fof(f790,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f520])).

fof(f1264,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f790])).

fof(f965,plain,(
    sK28 != sK29 ),
    inference(cnf_transformation,[],[f558])).

cnf(c_394,negated_conjecture,
    ( o_0_0_xboole_0 = k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(cnf_transformation,[],[f1237])).

cnf(c_378,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1227])).

cnf(c_12528,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) != o_0_0_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_13971,plain,
    ( r2_hidden(sK28,k1_tarski(sK29)) = iProver_top ),
    inference(superposition,[status(thm)],[c_394,c_12528])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f1264])).

cnf(c_13303,plain,
    ( ~ r2_hidden(sK28,k1_tarski(sK29))
    | sK28 = sK29 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_13304,plain,
    ( sK28 = sK29
    | r2_hidden(sK28,k1_tarski(sK29)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13303])).

cnf(c_393,negated_conjecture,
    ( sK28 != sK29 ),
    inference(cnf_transformation,[],[f965])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13971,c_13304,c_393])).

%------------------------------------------------------------------------------
