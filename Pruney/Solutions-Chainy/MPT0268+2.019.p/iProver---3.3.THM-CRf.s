%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:35 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 804 expanded)
%              Number of clauses        :   33 ( 134 expanded)
%              Number of leaves         :   13 ( 204 expanded)
%              Depth                    :   18
%              Number of atoms          :  327 (3991 expanded)
%              Number of equality atoms :  163 (1907 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f36,plain,
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

fof(f37,plain,
    ( ( r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 )
    & ( ~ r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f36])).

fof(f66,plain,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f83,plain,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2 ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f65,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f22])).

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
    inference(flattening,[],[f30])).

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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f67])).

fof(f94,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f67])).

fof(f92,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f93,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f92])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2499,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | r2_hidden(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_4,c_22])).

cnf(c_4823,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(resolution,[status(thm)],[c_2,c_2499])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_30,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_33,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1173,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1151,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k4_xboole_0(X3,X4))
    | X2 != X0
    | k4_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_1279,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2))
    | ~ r2_hidden(sK3,sK2)
    | X0 != sK3
    | k4_xboole_0(X1,X2) != sK2 ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_2047,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
    | ~ r2_hidden(sK3,sK2)
    | X0 != sK3
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_2049,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
    | ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3812,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(X0,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3814,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK3,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_3812])).

cnf(c_5676,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4823,c_23,c_22,c_30,c_33,c_1173,c_2049,c_2499,c_3814])).

cnf(c_5680,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5676,c_23,c_22,c_30,c_33,c_1173,c_2049,c_2499,c_3814])).

cnf(c_5694,plain,
    ( sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = sK3 ),
    inference(resolution,[status(thm)],[c_5680,c_20])).

cnf(c_479,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_478,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1960,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_479,c_478])).

cnf(c_5697,plain,
    ( sK3 = sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
    inference(resolution,[status(thm)],[c_5694,c_1960])).

cnf(c_2265,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_482,c_478])).

cnf(c_6303,plain,
    ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),X0)
    | r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_5697,c_2265])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5692,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
    inference(resolution,[status(thm)],[c_5680,c_3])).

cnf(c_6285,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5692,c_23,c_30,c_33,c_2049,c_2499,c_3814])).

cnf(c_8459,plain,
    ( r2_hidden(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_6303,c_6285])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8459,c_3814,c_2049,c_33,c_30,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:26:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.79/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/0.98  
% 2.79/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/0.98  
% 2.79/0.98  ------  iProver source info
% 2.79/0.98  
% 2.79/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.79/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/0.98  git: non_committed_changes: false
% 2.79/0.98  git: last_make_outside_of_git: false
% 2.79/0.98  
% 2.79/0.98  ------ 
% 2.79/0.98  ------ Parsing...
% 2.79/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/0.98  ------ Proving...
% 2.79/0.98  ------ Problem Properties 
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  clauses                                 23
% 2.79/0.98  conjectures                             2
% 2.79/0.98  EPR                                     0
% 2.79/0.98  Horn                                    16
% 2.79/0.98  unary                                   8
% 2.79/0.98  binary                                  6
% 2.79/0.98  lits                                    51
% 2.79/0.98  lits eq                                 24
% 2.79/0.98  fd_pure                                 0
% 2.79/0.98  fd_pseudo                               0
% 2.79/0.98  fd_cond                                 0
% 2.79/0.98  fd_pseudo_cond                          7
% 2.79/0.98  AC symbols                              0
% 2.79/0.98  
% 2.79/0.98  ------ Input Options Time Limit: Unbounded
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  ------ 
% 2.79/0.98  Current options:
% 2.79/0.98  ------ 
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  ------ Proving...
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  % SZS status Theorem for theBenchmark.p
% 2.79/0.98  
% 2.79/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/0.98  
% 2.79/0.98  fof(f2,axiom,(
% 2.79/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.98  
% 2.79/0.98  fof(f25,plain,(
% 2.79/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.79/0.98    inference(nnf_transformation,[],[f2])).
% 2.79/0.98  
% 2.79/0.98  fof(f26,plain,(
% 2.79/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.79/0.98    inference(flattening,[],[f25])).
% 2.79/0.98  
% 2.79/0.98  fof(f27,plain,(
% 2.79/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.79/0.98    inference(rectify,[],[f26])).
% 2.79/0.98  
% 2.79/0.98  fof(f28,plain,(
% 2.79/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.79/0.98    introduced(choice_axiom,[])).
% 2.79/0.98  
% 2.79/0.98  fof(f29,plain,(
% 2.79/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.79/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.79/0.98  
% 2.79/0.98  fof(f44,plain,(
% 2.79/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.79/0.98    inference(cnf_transformation,[],[f29])).
% 2.79/0.98  
% 2.79/0.98  fof(f42,plain,(
% 2.79/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.79/0.98    inference(cnf_transformation,[],[f29])).
% 2.79/0.98  
% 2.79/0.98  fof(f16,conjecture,(
% 2.79/0.98    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.98  
% 2.79/0.98  fof(f17,negated_conjecture,(
% 2.79/0.98    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.79/0.98    inference(negated_conjecture,[],[f16])).
% 2.79/0.98  
% 2.79/0.98  fof(f24,plain,(
% 2.79/0.98    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 2.79/0.98    inference(ennf_transformation,[],[f17])).
% 2.79/0.98  
% 2.79/0.98  fof(f35,plain,(
% 2.79/0.98    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 2.79/0.98    inference(nnf_transformation,[],[f24])).
% 2.79/0.98  
% 2.79/0.98  fof(f36,plain,(
% 2.79/0.98    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2))),
% 2.79/0.98    introduced(choice_axiom,[])).
% 2.79/0.98  
% 2.79/0.98  fof(f37,plain,(
% 2.79/0.98    (r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2)),
% 2.79/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f36])).
% 2.79/0.98  
% 2.79/0.98  fof(f66,plain,(
% 2.79/0.98    r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2),
% 2.79/0.98    inference(cnf_transformation,[],[f37])).
% 2.79/0.98  
% 2.79/0.98  fof(f11,axiom,(
% 2.79/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.98  
% 2.79/0.98  fof(f60,plain,(
% 2.79/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.79/0.98    inference(cnf_transformation,[],[f11])).
% 2.79/0.98  
% 2.79/0.98  fof(f12,axiom,(
% 2.79/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.98  
% 2.79/0.98  fof(f61,plain,(
% 2.79/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.79/0.98    inference(cnf_transformation,[],[f12])).
% 2.79/0.98  
% 2.79/0.98  fof(f13,axiom,(
% 2.79/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.98  
% 2.79/0.98  fof(f62,plain,(
% 2.79/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.79/0.98    inference(cnf_transformation,[],[f13])).
% 2.79/0.98  
% 2.79/0.98  fof(f14,axiom,(
% 2.79/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.98  
% 2.79/0.98  fof(f63,plain,(
% 2.79/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.79/0.98    inference(cnf_transformation,[],[f14])).
% 2.79/0.98  
% 2.79/0.98  fof(f67,plain,(
% 2.79/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.79/0.98    inference(definition_unfolding,[],[f62,f63])).
% 2.79/0.98  
% 2.79/0.98  fof(f68,plain,(
% 2.79/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.79/0.98    inference(definition_unfolding,[],[f61,f67])).
% 2.79/0.98  
% 2.79/0.98  fof(f69,plain,(
% 2.79/0.98    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.79/0.98    inference(definition_unfolding,[],[f60,f68])).
% 2.79/0.98  
% 2.79/0.98  fof(f83,plain,(
% 2.79/0.98    r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2),
% 2.79/0.98    inference(definition_unfolding,[],[f66,f69])).
% 2.79/0.98  
% 2.79/0.98  fof(f65,plain,(
% 2.79/0.98    ~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2),
% 2.79/0.98    inference(cnf_transformation,[],[f37])).
% 2.79/0.98  
% 2.79/0.98  fof(f84,plain,(
% 2.79/0.98    ~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2),
% 2.79/0.98    inference(definition_unfolding,[],[f65,f69])).
% 2.79/0.98  
% 2.79/0.98  fof(f10,axiom,(
% 2.79/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.98  
% 2.79/0.98  fof(f22,plain,(
% 2.79/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.79/0.98    inference(ennf_transformation,[],[f10])).
% 2.79/0.98  
% 2.79/0.98  fof(f30,plain,(
% 2.79/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.79/0.98    inference(nnf_transformation,[],[f22])).
% 2.79/0.98  
% 2.79/0.98  fof(f31,plain,(
% 2.79/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.79/0.98    inference(flattening,[],[f30])).
% 2.79/0.98  
% 2.79/0.98  fof(f32,plain,(
% 2.79/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.79/0.98    inference(rectify,[],[f31])).
% 2.79/0.98  
% 2.79/0.98  fof(f33,plain,(
% 2.79/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 2.79/0.98    introduced(choice_axiom,[])).
% 2.79/0.98  
% 2.79/0.98  fof(f34,plain,(
% 2.79/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.79/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 2.79/0.98  
% 2.79/0.98  fof(f52,plain,(
% 2.79/0.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.79/0.98    inference(cnf_transformation,[],[f34])).
% 2.79/0.98  
% 2.79/0.98  fof(f81,plain,(
% 2.79/0.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.79/0.98    inference(definition_unfolding,[],[f52,f67])).
% 2.79/0.98  
% 2.79/0.98  fof(f94,plain,(
% 2.79/0.98    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 2.79/0.98    inference(equality_resolution,[],[f81])).
% 2.79/0.98  
% 2.79/0.98  fof(f53,plain,(
% 2.79/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.79/0.98    inference(cnf_transformation,[],[f34])).
% 2.79/0.98  
% 2.79/0.98  fof(f80,plain,(
% 2.79/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.79/0.98    inference(definition_unfolding,[],[f53,f67])).
% 2.79/0.98  
% 2.79/0.98  fof(f92,plain,(
% 2.79/0.98    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 2.79/0.98    inference(equality_resolution,[],[f80])).
% 2.79/0.98  
% 2.79/0.98  fof(f93,plain,(
% 2.79/0.98    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 2.79/0.98    inference(equality_resolution,[],[f92])).
% 2.79/0.98  
% 2.79/0.98  fof(f40,plain,(
% 2.79/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.79/0.98    inference(cnf_transformation,[],[f29])).
% 2.79/0.98  
% 2.79/0.98  fof(f86,plain,(
% 2.79/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.79/0.98    inference(equality_resolution,[],[f40])).
% 2.79/0.98  
% 2.79/0.98  fof(f43,plain,(
% 2.79/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.79/0.98    inference(cnf_transformation,[],[f29])).
% 2.79/0.98  
% 2.79/0.98  cnf(c_2,plain,
% 2.79/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.79/0.98      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.79/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 2.79/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 2.79/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_4,plain,
% 2.79/0.98      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.79/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.79/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 2.79/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_22,negated_conjecture,
% 2.79/0.98      ( r2_hidden(sK3,sK2)
% 2.79/0.98      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2 ),
% 2.79/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_2499,plain,
% 2.79/0.98      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 2.79/0.98      | r2_hidden(sK3,sK2) ),
% 2.79/0.98      inference(resolution,[status(thm)],[c_4,c_22]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_4823,plain,
% 2.79/0.98      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.79/0.98      | ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 2.79/0.98      | r2_hidden(sK3,sK2)
% 2.79/0.98      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
% 2.79/0.98      inference(resolution,[status(thm)],[c_2,c_2499]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_23,negated_conjecture,
% 2.79/0.98      ( ~ r2_hidden(sK3,sK2)
% 2.79/0.98      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
% 2.79/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_20,plain,
% 2.79/0.98      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 2.79/0.98      | X0 = X1
% 2.79/0.98      | X0 = X2
% 2.79/0.98      | X0 = X3 ),
% 2.79/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_30,plain,
% 2.79/0.98      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 2.79/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_19,plain,
% 2.79/0.98      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 2.79/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_33,plain,
% 2.79/0.98      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 2.79/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_1173,plain,
% 2.79/0.98      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.79/0.98      | ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 2.79/0.98      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
% 2.79/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_482,plain,
% 2.79/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.79/0.98      theory(equality) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_1151,plain,
% 2.79/0.98      ( ~ r2_hidden(X0,X1)
% 2.79/0.98      | r2_hidden(X2,k4_xboole_0(X3,X4))
% 2.79/0.98      | X2 != X0
% 2.79/0.98      | k4_xboole_0(X3,X4) != X1 ),
% 2.79/0.98      inference(instantiation,[status(thm)],[c_482]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_1279,plain,
% 2.79/0.98      ( r2_hidden(X0,k4_xboole_0(X1,X2))
% 2.79/0.98      | ~ r2_hidden(sK3,sK2)
% 2.79/0.98      | X0 != sK3
% 2.79/0.98      | k4_xboole_0(X1,X2) != sK2 ),
% 2.79/0.98      inference(instantiation,[status(thm)],[c_1151]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_2047,plain,
% 2.79/0.98      ( r2_hidden(X0,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
% 2.79/0.98      | ~ r2_hidden(sK3,sK2)
% 2.79/0.98      | X0 != sK3
% 2.79/0.98      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2 ),
% 2.79/0.98      inference(instantiation,[status(thm)],[c_1279]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_2049,plain,
% 2.79/0.98      ( r2_hidden(sK3,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
% 2.79/0.98      | ~ r2_hidden(sK3,sK2)
% 2.79/0.98      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK2
% 2.79/0.98      | sK3 != sK3 ),
% 2.79/0.98      inference(instantiation,[status(thm)],[c_2047]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_6,plain,
% 2.79/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.79/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_3812,plain,
% 2.79/0.98      ( ~ r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.79/0.98      | ~ r2_hidden(X0,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 2.79/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_3814,plain,
% 2.79/0.98      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.79/0.98      | ~ r2_hidden(sK3,k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 2.79/0.98      inference(instantiation,[status(thm)],[c_3812]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_5676,plain,
% 2.79/0.98      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.79/0.98      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
% 2.79/0.98      inference(global_propositional_subsumption,
% 2.79/0.98                [status(thm)],
% 2.79/0.98                [c_4823,c_23,c_22,c_30,c_33,c_1173,c_2049,c_2499,c_3814]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_5680,plain,
% 2.79/0.98      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 2.79/0.98      inference(global_propositional_subsumption,
% 2.79/0.98                [status(thm)],
% 2.79/0.98                [c_5676,c_23,c_22,c_30,c_33,c_1173,c_2049,c_2499,c_3814]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_5694,plain,
% 2.79/0.98      ( sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = sK3 ),
% 2.79/0.98      inference(resolution,[status(thm)],[c_5680,c_20]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_479,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_478,plain,( X0 = X0 ),theory(equality) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_1960,plain,
% 2.79/0.98      ( X0 != X1 | X1 = X0 ),
% 2.79/0.98      inference(resolution,[status(thm)],[c_479,c_478]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_5697,plain,
% 2.79/0.98      ( sK3 = sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
% 2.79/0.98      inference(resolution,[status(thm)],[c_5694,c_1960]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_2265,plain,
% 2.79/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 2.79/0.98      inference(resolution,[status(thm)],[c_482,c_478]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_6303,plain,
% 2.79/0.98      ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),X0)
% 2.79/0.98      | r2_hidden(sK3,X0) ),
% 2.79/0.98      inference(resolution,[status(thm)],[c_5697,c_2265]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_3,plain,
% 2.79/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.79/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.79/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 2.79/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_5692,plain,
% 2.79/0.98      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 2.79/0.98      | k4_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK2 ),
% 2.79/0.98      inference(resolution,[status(thm)],[c_5680,c_3]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_6285,plain,
% 2.79/0.98      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2) ),
% 2.79/0.98      inference(global_propositional_subsumption,
% 2.79/0.98                [status(thm)],
% 2.79/0.98                [c_5692,c_23,c_30,c_33,c_2049,c_2499,c_3814]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(c_8459,plain,
% 2.79/0.98      ( r2_hidden(sK3,sK2) ),
% 2.79/0.98      inference(resolution,[status(thm)],[c_6303,c_6285]) ).
% 2.79/0.98  
% 2.79/0.98  cnf(contradiction,plain,
% 2.79/0.98      ( $false ),
% 2.79/0.98      inference(minisat,
% 2.79/0.98                [status(thm)],
% 2.79/0.98                [c_8459,c_3814,c_2049,c_33,c_30,c_23]) ).
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/0.98  
% 2.79/0.98  ------                               Statistics
% 2.79/0.98  
% 2.79/0.98  ------ Selected
% 2.79/0.98  
% 2.79/0.98  total_time:                             0.29
% 2.79/0.98  
%------------------------------------------------------------------------------
