%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:35 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 423 expanded)
%              Number of clauses        :   30 (  71 expanded)
%              Number of leaves         :   13 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          :  321 (2080 expanded)
%              Number of equality atoms :  164 (1019 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK3,sK2)
        | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 )
      & ( ~ r2_hidden(sK3,sK2)
        | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 )
    & ( ~ r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f37])).

fof(f68,plain,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f69])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f84,plain,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2 ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f67,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(definition_unfolding,[],[f67,f71])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f95,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f93,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f94,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f93])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

cnf(c_486,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1165,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3,sK2)
    | sK2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_1532,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK3,sK2)
    | sK2 != sK2
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_10598,plain,
    ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | r2_hidden(sK3,sK2)
    | sK2 != sK2
    | sK3 != sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2932,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | r2_hidden(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_4,c_23])).

cnf(c_6458,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(resolution,[status(thm)],[c_2,c_2932])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_31,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_34,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1181,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1278,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,sK2)
    | X1 != sK2
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_2353,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
    | ~ r2_hidden(sK3,sK2)
    | X0 != sK3
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_2355,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
    | ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2353])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4867,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(X0,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4869,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK3,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_4867])).

cnf(c_7563,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6458,c_24,c_23,c_31,c_34,c_1181,c_2355,c_2932,c_4869])).

cnf(c_7567,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7563,c_24,c_23,c_31,c_34,c_1181,c_2355,c_2932,c_4869])).

cnf(c_7581,plain,
    ( sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = sK3 ),
    inference(resolution,[status(thm)],[c_7567,c_21])).

cnf(c_483,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_482,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2295,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_483,c_482])).

cnf(c_7584,plain,
    ( sK3 = sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
    inference(resolution,[status(thm)],[c_7581,c_2295])).

cnf(c_1533,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10598,c_7584,c_4869,c_2932,c_2355,c_1533,c_34,c_31,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.97/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.99  
% 2.97/0.99  ------  iProver source info
% 2.97/0.99  
% 2.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.99  git: non_committed_changes: false
% 2.97/0.99  git: last_make_outside_of_git: false
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  ------ Parsing...
% 2.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.99  ------ Proving...
% 2.97/0.99  ------ Problem Properties 
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  clauses                                 24
% 2.97/0.99  conjectures                             2
% 2.97/0.99  EPR                                     0
% 2.97/0.99  Horn                                    17
% 2.97/0.99  unary                                   9
% 2.97/0.99  binary                                  6
% 2.97/0.99  lits                                    52
% 2.97/0.99  lits eq                                 25
% 2.97/0.99  fd_pure                                 0
% 2.97/0.99  fd_pseudo                               0
% 2.97/0.99  fd_cond                                 0
% 2.97/0.99  fd_pseudo_cond                          7
% 2.97/0.99  AC symbols                              0
% 2.97/0.99  
% 2.97/0.99  ------ Input Options Time Limit: Unbounded
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  Current options:
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ Proving...
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS status Theorem for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  fof(f2,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f26,plain,(
% 2.97/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.97/0.99    inference(nnf_transformation,[],[f2])).
% 2.97/0.99  
% 2.97/0.99  fof(f27,plain,(
% 2.97/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.97/0.99    inference(flattening,[],[f26])).
% 2.97/0.99  
% 2.97/0.99  fof(f28,plain,(
% 2.97/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.97/0.99    inference(rectify,[],[f27])).
% 2.97/0.99  
% 2.97/0.99  fof(f29,plain,(
% 2.97/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f30,plain,(
% 2.97/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.97/0.99  
% 2.97/0.99  fof(f45,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f30])).
% 2.97/0.99  
% 2.97/0.99  fof(f43,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f30])).
% 2.97/0.99  
% 2.97/0.99  fof(f17,conjecture,(
% 2.97/0.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f18,negated_conjecture,(
% 2.97/0.99    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.97/0.99    inference(negated_conjecture,[],[f17])).
% 2.97/0.99  
% 2.97/0.99  fof(f25,plain,(
% 2.97/0.99    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f18])).
% 2.97/0.99  
% 2.97/0.99  fof(f36,plain,(
% 2.97/0.99    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 2.97/0.99    inference(nnf_transformation,[],[f25])).
% 2.97/0.99  
% 2.97/0.99  fof(f37,plain,(
% 2.97/0.99    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f38,plain,(
% 2.97/0.99    (r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2)),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f37])).
% 2.97/0.99  
% 2.97/0.99  fof(f68,plain,(
% 2.97/0.99    r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2),
% 2.97/0.99    inference(cnf_transformation,[],[f38])).
% 2.97/0.99  
% 2.97/0.99  fof(f12,axiom,(
% 2.97/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f62,plain,(
% 2.97/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f12])).
% 2.97/0.99  
% 2.97/0.99  fof(f13,axiom,(
% 2.97/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f63,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f13])).
% 2.97/0.99  
% 2.97/0.99  fof(f14,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f64,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f14])).
% 2.97/0.99  
% 2.97/0.99  fof(f15,axiom,(
% 2.97/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f65,plain,(
% 2.97/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f15])).
% 2.97/0.99  
% 2.97/0.99  fof(f69,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.97/0.99    inference(definition_unfolding,[],[f64,f65])).
% 2.97/0.99  
% 2.97/0.99  fof(f70,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.97/0.99    inference(definition_unfolding,[],[f63,f69])).
% 2.97/0.99  
% 2.97/0.99  fof(f71,plain,(
% 2.97/0.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.97/0.99    inference(definition_unfolding,[],[f62,f70])).
% 2.97/0.99  
% 2.97/0.99  fof(f84,plain,(
% 2.97/0.99    r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2),
% 2.97/0.99    inference(definition_unfolding,[],[f68,f71])).
% 2.97/0.99  
% 2.97/0.99  fof(f67,plain,(
% 2.97/0.99    ~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2),
% 2.97/0.99    inference(cnf_transformation,[],[f38])).
% 2.97/0.99  
% 2.97/0.99  fof(f85,plain,(
% 2.97/0.99    ~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2),
% 2.97/0.99    inference(definition_unfolding,[],[f67,f71])).
% 2.97/0.99  
% 2.97/0.99  fof(f11,axiom,(
% 2.97/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f23,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.97/0.99    inference(ennf_transformation,[],[f11])).
% 2.97/0.99  
% 2.97/0.99  fof(f31,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.97/0.99    inference(nnf_transformation,[],[f23])).
% 2.97/0.99  
% 2.97/0.99  fof(f32,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.97/0.99    inference(flattening,[],[f31])).
% 2.97/0.99  
% 2.97/0.99  fof(f33,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.97/0.99    inference(rectify,[],[f32])).
% 2.97/0.99  
% 2.97/0.99  fof(f34,plain,(
% 2.97/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f35,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 2.97/0.99  
% 2.97/0.99  fof(f54,plain,(
% 2.97/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.97/0.99    inference(cnf_transformation,[],[f35])).
% 2.97/0.99  
% 2.97/0.99  fof(f82,plain,(
% 2.97/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.97/0.99    inference(definition_unfolding,[],[f54,f69])).
% 2.97/0.99  
% 2.97/0.99  fof(f95,plain,(
% 2.97/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 2.97/0.99    inference(equality_resolution,[],[f82])).
% 2.97/0.99  
% 2.97/0.99  fof(f55,plain,(
% 2.97/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.97/0.99    inference(cnf_transformation,[],[f35])).
% 2.97/0.99  
% 2.97/0.99  fof(f81,plain,(
% 2.97/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.97/0.99    inference(definition_unfolding,[],[f55,f69])).
% 2.97/0.99  
% 2.97/0.99  fof(f93,plain,(
% 2.97/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 2.97/0.99    inference(equality_resolution,[],[f81])).
% 2.97/0.99  
% 2.97/0.99  fof(f94,plain,(
% 2.97/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 2.97/0.99    inference(equality_resolution,[],[f93])).
% 2.97/0.99  
% 2.97/0.99  fof(f41,plain,(
% 2.97/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.97/0.99    inference(cnf_transformation,[],[f30])).
% 2.97/0.99  
% 2.97/0.99  fof(f87,plain,(
% 2.97/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.97/0.99    inference(equality_resolution,[],[f41])).
% 2.97/0.99  
% 2.97/0.99  cnf(c_486,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.97/0.99      theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1165,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(sK3,sK2) | sK2 != X1 | sK3 != X0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_486]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1532,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,sK2)
% 2.97/0.99      | r2_hidden(sK3,sK2)
% 2.97/0.99      | sK2 != sK2
% 2.97/0.99      | sK3 != X0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1165]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_10598,plain,
% 2.97/0.99      ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 2.97/0.99      | r2_hidden(sK3,sK2)
% 2.97/0.99      | sK2 != sK2
% 2.97/0.99      | sK3 != sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1532]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2,plain,
% 2.97/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.97/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.97/0.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 2.97/0.99      | k4_xboole_0(X0,X1) = X2 ),
% 2.97/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4,plain,
% 2.97/0.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.97/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.97/0.99      | k4_xboole_0(X0,X1) = X2 ),
% 2.97/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_23,negated_conjecture,
% 2.97/0.99      ( r2_hidden(sK3,sK2)
% 2.97/0.99      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2 ),
% 2.97/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2932,plain,
% 2.97/0.99      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 2.97/0.99      | r2_hidden(sK3,sK2) ),
% 2.97/0.99      inference(resolution,[status(thm)],[c_4,c_23]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6458,plain,
% 2.97/0.99      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.97/0.99      | ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 2.97/0.99      | r2_hidden(sK3,sK2)
% 2.97/0.99      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
% 2.97/0.99      inference(resolution,[status(thm)],[c_2,c_2932]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_24,negated_conjecture,
% 2.97/0.99      ( ~ r2_hidden(sK3,sK2)
% 2.97/0.99      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
% 2.97/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_21,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 2.97/0.99      | X0 = X1
% 2.97/0.99      | X0 = X2
% 2.97/0.99      | X0 = X3 ),
% 2.97/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_31,plain,
% 2.97/0.99      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_20,plain,
% 2.97/0.99      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_34,plain,
% 2.97/0.99      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1181,plain,
% 2.97/0.99      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.97/0.99      | ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 2.97/0.99      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1278,plain,
% 2.97/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(sK3,sK2) | X1 != sK2 | X0 != sK3 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_486]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2353,plain,
% 2.97/0.99      ( r2_hidden(X0,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
% 2.97/0.99      | ~ r2_hidden(sK3,sK2)
% 2.97/0.99      | X0 != sK3
% 2.97/0.99      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1278]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2355,plain,
% 2.97/0.99      ( r2_hidden(sK3,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
% 2.97/0.99      | ~ r2_hidden(sK3,sK2)
% 2.97/0.99      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2
% 2.97/0.99      | sK3 != sK3 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_2353]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4867,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.97/0.99      | ~ r2_hidden(X0,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4869,plain,
% 2.97/0.99      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.97/0.99      | ~ r2_hidden(sK3,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_4867]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7563,plain,
% 2.97/0.99      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.97/0.99      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_6458,c_24,c_23,c_31,c_34,c_1181,c_2355,c_2932,c_4869]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7567,plain,
% 2.97/0.99      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_7563,c_24,c_23,c_31,c_34,c_1181,c_2355,c_2932,c_4869]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7581,plain,
% 2.97/0.99      ( sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = sK3 ),
% 2.97/0.99      inference(resolution,[status(thm)],[c_7567,c_21]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_483,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_482,plain,( X0 = X0 ),theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2295,plain,
% 2.97/0.99      ( X0 != X1 | X1 = X0 ),
% 2.97/0.99      inference(resolution,[status(thm)],[c_483,c_482]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7584,plain,
% 2.97/0.99      ( sK3 = sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
% 2.97/0.99      inference(resolution,[status(thm)],[c_7581,c_2295]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1533,plain,
% 2.97/0.99      ( sK2 = sK2 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_482]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(contradiction,plain,
% 2.97/0.99      ( $false ),
% 2.97/0.99      inference(minisat,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_10598,c_7584,c_4869,c_2932,c_2355,c_1533,c_34,c_31,
% 2.97/0.99                 c_24]) ).
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  ------                               Statistics
% 2.97/0.99  
% 2.97/0.99  ------ Selected
% 2.97/0.99  
% 2.97/0.99  total_time:                             0.276
% 2.97/0.99  
%------------------------------------------------------------------------------
