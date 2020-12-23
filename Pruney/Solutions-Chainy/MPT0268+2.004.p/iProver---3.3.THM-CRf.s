%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:32 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 149 expanded)
%              Number of clauses        :   27 (  30 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  330 ( 752 expanded)
%              Number of equality atoms :  172 ( 405 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f94,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f109,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f107,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f108,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f107])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 )
    & ( ~ r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f39])).

fof(f73,plain,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f74])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f75])).

fof(f96,plain,
    ( r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK2 ),
    inference(definition_unfolding,[],[f73,f51,f76])).

fof(f72,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK2 ),
    inference(definition_unfolding,[],[f72,f51,f76])).

cnf(c_558,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1190,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_2390,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,sK2)
    | X0 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_4294,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))))
    | ~ r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2390])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1719,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0))
    | ~ r2_hidden(X0,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X1,X1,X1,X2,X0)))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3054,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK3,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
    inference(instantiation,[status(thm)],[c_1719])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2630,plain,
    ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(X0,X0,X0,X1,X2))
    | sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = X0
    | sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = X1
    | sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = X2 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2637,plain,
    ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_2630])).

cnf(c_554,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1762,plain,
    ( sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) != X0
    | sK3 != X0
    | sK3 = sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_1763,plain,
    ( sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) != sK3
    | sK3 = sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_553,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1715,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_1318,plain,
    ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | r2_hidden(sK3,X0)
    | X0 != sK2
    | sK3 != sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_1439,plain,
    ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | r2_hidden(sK3,sK2)
    | sK2 != sK2
    | sK3 != sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1110,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1112,plain,
    ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_23,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_37,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_34,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK2 ),
    inference(cnf_transformation,[],[f97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4294,c_3054,c_2637,c_1763,c_1715,c_1439,c_1110,c_1112,c_37,c_34,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:55:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.40/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/1.00  
% 3.40/1.00  ------  iProver source info
% 3.40/1.00  
% 3.40/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.40/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/1.00  git: non_committed_changes: false
% 3.40/1.00  git: last_make_outside_of_git: false
% 3.40/1.00  
% 3.40/1.00  ------ 
% 3.40/1.00  
% 3.40/1.00  ------ Input Options
% 3.40/1.00  
% 3.40/1.00  --out_options                           all
% 3.40/1.00  --tptp_safe_out                         true
% 3.40/1.00  --problem_path                          ""
% 3.40/1.00  --include_path                          ""
% 3.40/1.00  --clausifier                            res/vclausify_rel
% 3.40/1.00  --clausifier_options                    ""
% 3.40/1.00  --stdin                                 false
% 3.40/1.00  --stats_out                             all
% 3.40/1.00  
% 3.40/1.00  ------ General Options
% 3.40/1.00  
% 3.40/1.00  --fof                                   false
% 3.40/1.00  --time_out_real                         305.
% 3.40/1.00  --time_out_virtual                      -1.
% 3.40/1.00  --symbol_type_check                     false
% 3.40/1.00  --clausify_out                          false
% 3.40/1.00  --sig_cnt_out                           false
% 3.40/1.00  --trig_cnt_out                          false
% 3.40/1.00  --trig_cnt_out_tolerance                1.
% 3.40/1.00  --trig_cnt_out_sk_spl                   false
% 3.40/1.00  --abstr_cl_out                          false
% 3.40/1.00  
% 3.40/1.00  ------ Global Options
% 3.40/1.00  
% 3.40/1.00  --schedule                              default
% 3.40/1.00  --add_important_lit                     false
% 3.40/1.00  --prop_solver_per_cl                    1000
% 3.40/1.00  --min_unsat_core                        false
% 3.40/1.00  --soft_assumptions                      false
% 3.40/1.00  --soft_lemma_size                       3
% 3.40/1.00  --prop_impl_unit_size                   0
% 3.40/1.00  --prop_impl_unit                        []
% 3.40/1.00  --share_sel_clauses                     true
% 3.40/1.00  --reset_solvers                         false
% 3.40/1.00  --bc_imp_inh                            [conj_cone]
% 3.40/1.00  --conj_cone_tolerance                   3.
% 3.40/1.00  --extra_neg_conj                        none
% 3.40/1.00  --large_theory_mode                     true
% 3.40/1.00  --prolific_symb_bound                   200
% 3.40/1.00  --lt_threshold                          2000
% 3.40/1.00  --clause_weak_htbl                      true
% 3.40/1.00  --gc_record_bc_elim                     false
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing Options
% 3.40/1.00  
% 3.40/1.00  --preprocessing_flag                    true
% 3.40/1.00  --time_out_prep_mult                    0.1
% 3.40/1.00  --splitting_mode                        input
% 3.40/1.00  --splitting_grd                         true
% 3.40/1.00  --splitting_cvd                         false
% 3.40/1.00  --splitting_cvd_svl                     false
% 3.40/1.00  --splitting_nvd                         32
% 3.40/1.00  --sub_typing                            true
% 3.40/1.00  --prep_gs_sim                           true
% 3.40/1.00  --prep_unflatten                        true
% 3.40/1.00  --prep_res_sim                          true
% 3.40/1.00  --prep_upred                            true
% 3.40/1.00  --prep_sem_filter                       exhaustive
% 3.40/1.00  --prep_sem_filter_out                   false
% 3.40/1.00  --pred_elim                             true
% 3.40/1.00  --res_sim_input                         true
% 3.40/1.00  --eq_ax_congr_red                       true
% 3.40/1.00  --pure_diseq_elim                       true
% 3.40/1.00  --brand_transform                       false
% 3.40/1.00  --non_eq_to_eq                          false
% 3.40/1.00  --prep_def_merge                        true
% 3.40/1.00  --prep_def_merge_prop_impl              false
% 3.40/1.00  --prep_def_merge_mbd                    true
% 3.40/1.00  --prep_def_merge_tr_red                 false
% 3.40/1.00  --prep_def_merge_tr_cl                  false
% 3.40/1.00  --smt_preprocessing                     true
% 3.40/1.00  --smt_ac_axioms                         fast
% 3.40/1.00  --preprocessed_out                      false
% 3.40/1.00  --preprocessed_stats                    false
% 3.40/1.00  
% 3.40/1.00  ------ Abstraction refinement Options
% 3.40/1.00  
% 3.40/1.00  --abstr_ref                             []
% 3.40/1.00  --abstr_ref_prep                        false
% 3.40/1.00  --abstr_ref_until_sat                   false
% 3.40/1.00  --abstr_ref_sig_restrict                funpre
% 3.40/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/1.00  --abstr_ref_under                       []
% 3.40/1.00  
% 3.40/1.00  ------ SAT Options
% 3.40/1.00  
% 3.40/1.00  --sat_mode                              false
% 3.40/1.00  --sat_fm_restart_options                ""
% 3.40/1.00  --sat_gr_def                            false
% 3.40/1.00  --sat_epr_types                         true
% 3.40/1.00  --sat_non_cyclic_types                  false
% 3.40/1.00  --sat_finite_models                     false
% 3.40/1.00  --sat_fm_lemmas                         false
% 3.40/1.00  --sat_fm_prep                           false
% 3.40/1.00  --sat_fm_uc_incr                        true
% 3.40/1.00  --sat_out_model                         small
% 3.40/1.00  --sat_out_clauses                       false
% 3.40/1.00  
% 3.40/1.00  ------ QBF Options
% 3.40/1.00  
% 3.40/1.00  --qbf_mode                              false
% 3.40/1.00  --qbf_elim_univ                         false
% 3.40/1.00  --qbf_dom_inst                          none
% 3.40/1.00  --qbf_dom_pre_inst                      false
% 3.40/1.00  --qbf_sk_in                             false
% 3.40/1.00  --qbf_pred_elim                         true
% 3.40/1.00  --qbf_split                             512
% 3.40/1.00  
% 3.40/1.00  ------ BMC1 Options
% 3.40/1.00  
% 3.40/1.00  --bmc1_incremental                      false
% 3.40/1.00  --bmc1_axioms                           reachable_all
% 3.40/1.00  --bmc1_min_bound                        0
% 3.40/1.00  --bmc1_max_bound                        -1
% 3.40/1.00  --bmc1_max_bound_default                -1
% 3.40/1.00  --bmc1_symbol_reachability              true
% 3.40/1.00  --bmc1_property_lemmas                  false
% 3.40/1.00  --bmc1_k_induction                      false
% 3.40/1.00  --bmc1_non_equiv_states                 false
% 3.40/1.00  --bmc1_deadlock                         false
% 3.40/1.00  --bmc1_ucm                              false
% 3.40/1.00  --bmc1_add_unsat_core                   none
% 3.40/1.00  --bmc1_unsat_core_children              false
% 3.40/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/1.00  --bmc1_out_stat                         full
% 3.40/1.00  --bmc1_ground_init                      false
% 3.40/1.00  --bmc1_pre_inst_next_state              false
% 3.40/1.00  --bmc1_pre_inst_state                   false
% 3.40/1.00  --bmc1_pre_inst_reach_state             false
% 3.40/1.00  --bmc1_out_unsat_core                   false
% 3.40/1.00  --bmc1_aig_witness_out                  false
% 3.40/1.00  --bmc1_verbose                          false
% 3.40/1.00  --bmc1_dump_clauses_tptp                false
% 3.40/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.40/1.00  --bmc1_dump_file                        -
% 3.40/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.40/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.40/1.00  --bmc1_ucm_extend_mode                  1
% 3.40/1.00  --bmc1_ucm_init_mode                    2
% 3.40/1.00  --bmc1_ucm_cone_mode                    none
% 3.40/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.40/1.00  --bmc1_ucm_relax_model                  4
% 3.40/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.40/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/1.00  --bmc1_ucm_layered_model                none
% 3.40/1.00  --bmc1_ucm_max_lemma_size               10
% 3.40/1.00  
% 3.40/1.00  ------ AIG Options
% 3.40/1.00  
% 3.40/1.00  --aig_mode                              false
% 3.40/1.00  
% 3.40/1.00  ------ Instantiation Options
% 3.40/1.00  
% 3.40/1.00  --instantiation_flag                    true
% 3.40/1.00  --inst_sos_flag                         true
% 3.40/1.00  --inst_sos_phase                        true
% 3.40/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel_side                     num_symb
% 3.40/1.00  --inst_solver_per_active                1400
% 3.40/1.00  --inst_solver_calls_frac                1.
% 3.40/1.00  --inst_passive_queue_type               priority_queues
% 3.40/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/1.00  --inst_passive_queues_freq              [25;2]
% 3.40/1.00  --inst_dismatching                      true
% 3.40/1.00  --inst_eager_unprocessed_to_passive     true
% 3.40/1.00  --inst_prop_sim_given                   true
% 3.40/1.00  --inst_prop_sim_new                     false
% 3.40/1.00  --inst_subs_new                         false
% 3.40/1.00  --inst_eq_res_simp                      false
% 3.40/1.00  --inst_subs_given                       false
% 3.40/1.00  --inst_orphan_elimination               true
% 3.40/1.00  --inst_learning_loop_flag               true
% 3.40/1.00  --inst_learning_start                   3000
% 3.40/1.00  --inst_learning_factor                  2
% 3.40/1.00  --inst_start_prop_sim_after_learn       3
% 3.40/1.00  --inst_sel_renew                        solver
% 3.40/1.00  --inst_lit_activity_flag                true
% 3.40/1.00  --inst_restr_to_given                   false
% 3.40/1.00  --inst_activity_threshold               500
% 3.40/1.00  --inst_out_proof                        true
% 3.40/1.00  
% 3.40/1.00  ------ Resolution Options
% 3.40/1.00  
% 3.40/1.00  --resolution_flag                       true
% 3.40/1.00  --res_lit_sel                           adaptive
% 3.40/1.00  --res_lit_sel_side                      none
% 3.40/1.00  --res_ordering                          kbo
% 3.40/1.00  --res_to_prop_solver                    active
% 3.40/1.00  --res_prop_simpl_new                    false
% 3.40/1.00  --res_prop_simpl_given                  true
% 3.40/1.00  --res_passive_queue_type                priority_queues
% 3.40/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/1.00  --res_passive_queues_freq               [15;5]
% 3.40/1.00  --res_forward_subs                      full
% 3.40/1.00  --res_backward_subs                     full
% 3.40/1.00  --res_forward_subs_resolution           true
% 3.40/1.00  --res_backward_subs_resolution          true
% 3.40/1.00  --res_orphan_elimination                true
% 3.40/1.00  --res_time_limit                        2.
% 3.40/1.00  --res_out_proof                         true
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Options
% 3.40/1.00  
% 3.40/1.00  --superposition_flag                    true
% 3.40/1.00  --sup_passive_queue_type                priority_queues
% 3.40/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.40/1.00  --demod_completeness_check              fast
% 3.40/1.00  --demod_use_ground                      true
% 3.40/1.00  --sup_to_prop_solver                    passive
% 3.40/1.00  --sup_prop_simpl_new                    true
% 3.40/1.00  --sup_prop_simpl_given                  true
% 3.40/1.00  --sup_fun_splitting                     true
% 3.40/1.00  --sup_smt_interval                      50000
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Simplification Setup
% 3.40/1.00  
% 3.40/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.40/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.40/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.40/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.40/1.00  --sup_immed_triv                        [TrivRules]
% 3.40/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.00  --sup_immed_bw_main                     []
% 3.40/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.40/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.00  --sup_input_bw                          []
% 3.40/1.00  
% 3.40/1.00  ------ Combination Options
% 3.40/1.00  
% 3.40/1.00  --comb_res_mult                         3
% 3.40/1.00  --comb_sup_mult                         2
% 3.40/1.00  --comb_inst_mult                        10
% 3.40/1.00  
% 3.40/1.00  ------ Debug Options
% 3.40/1.00  
% 3.40/1.00  --dbg_backtrace                         false
% 3.40/1.00  --dbg_dump_prop_clauses                 false
% 3.40/1.00  --dbg_dump_prop_clauses_file            -
% 3.40/1.00  --dbg_out_stat                          false
% 3.40/1.00  ------ Parsing...
% 3.40/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/1.00  ------ Proving...
% 3.40/1.00  ------ Problem Properties 
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  clauses                                 27
% 3.40/1.00  conjectures                             2
% 3.40/1.00  EPR                                     2
% 3.40/1.00  Horn                                    20
% 3.40/1.00  unary                                   9
% 3.40/1.00  binary                                  8
% 3.40/1.00  lits                                    59
% 3.40/1.00  lits eq                                 26
% 3.40/1.00  fd_pure                                 0
% 3.40/1.00  fd_pseudo                               0
% 3.40/1.00  fd_cond                                 0
% 3.40/1.00  fd_pseudo_cond                          8
% 3.40/1.00  AC symbols                              0
% 3.40/1.00  
% 3.40/1.00  ------ Schedule dynamic 5 is on 
% 3.40/1.00  
% 3.40/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  ------ 
% 3.40/1.00  Current options:
% 3.40/1.00  ------ 
% 3.40/1.00  
% 3.40/1.00  ------ Input Options
% 3.40/1.00  
% 3.40/1.00  --out_options                           all
% 3.40/1.00  --tptp_safe_out                         true
% 3.40/1.00  --problem_path                          ""
% 3.40/1.00  --include_path                          ""
% 3.40/1.00  --clausifier                            res/vclausify_rel
% 3.40/1.00  --clausifier_options                    ""
% 3.40/1.00  --stdin                                 false
% 3.40/1.00  --stats_out                             all
% 3.40/1.00  
% 3.40/1.00  ------ General Options
% 3.40/1.00  
% 3.40/1.00  --fof                                   false
% 3.40/1.00  --time_out_real                         305.
% 3.40/1.00  --time_out_virtual                      -1.
% 3.40/1.00  --symbol_type_check                     false
% 3.40/1.00  --clausify_out                          false
% 3.40/1.00  --sig_cnt_out                           false
% 3.40/1.00  --trig_cnt_out                          false
% 3.40/1.00  --trig_cnt_out_tolerance                1.
% 3.40/1.00  --trig_cnt_out_sk_spl                   false
% 3.40/1.00  --abstr_cl_out                          false
% 3.40/1.00  
% 3.40/1.00  ------ Global Options
% 3.40/1.00  
% 3.40/1.00  --schedule                              default
% 3.40/1.00  --add_important_lit                     false
% 3.40/1.00  --prop_solver_per_cl                    1000
% 3.40/1.00  --min_unsat_core                        false
% 3.40/1.00  --soft_assumptions                      false
% 3.40/1.00  --soft_lemma_size                       3
% 3.40/1.00  --prop_impl_unit_size                   0
% 3.40/1.00  --prop_impl_unit                        []
% 3.40/1.00  --share_sel_clauses                     true
% 3.40/1.00  --reset_solvers                         false
% 3.40/1.00  --bc_imp_inh                            [conj_cone]
% 3.40/1.00  --conj_cone_tolerance                   3.
% 3.40/1.00  --extra_neg_conj                        none
% 3.40/1.00  --large_theory_mode                     true
% 3.40/1.00  --prolific_symb_bound                   200
% 3.40/1.00  --lt_threshold                          2000
% 3.40/1.00  --clause_weak_htbl                      true
% 3.40/1.00  --gc_record_bc_elim                     false
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing Options
% 3.40/1.00  
% 3.40/1.00  --preprocessing_flag                    true
% 3.40/1.00  --time_out_prep_mult                    0.1
% 3.40/1.00  --splitting_mode                        input
% 3.40/1.00  --splitting_grd                         true
% 3.40/1.00  --splitting_cvd                         false
% 3.40/1.00  --splitting_cvd_svl                     false
% 3.40/1.00  --splitting_nvd                         32
% 3.40/1.00  --sub_typing                            true
% 3.40/1.00  --prep_gs_sim                           true
% 3.40/1.00  --prep_unflatten                        true
% 3.40/1.00  --prep_res_sim                          true
% 3.40/1.00  --prep_upred                            true
% 3.40/1.00  --prep_sem_filter                       exhaustive
% 3.40/1.00  --prep_sem_filter_out                   false
% 3.40/1.00  --pred_elim                             true
% 3.40/1.00  --res_sim_input                         true
% 3.40/1.00  --eq_ax_congr_red                       true
% 3.40/1.00  --pure_diseq_elim                       true
% 3.40/1.00  --brand_transform                       false
% 3.40/1.00  --non_eq_to_eq                          false
% 3.40/1.00  --prep_def_merge                        true
% 3.40/1.00  --prep_def_merge_prop_impl              false
% 3.40/1.00  --prep_def_merge_mbd                    true
% 3.40/1.00  --prep_def_merge_tr_red                 false
% 3.40/1.00  --prep_def_merge_tr_cl                  false
% 3.40/1.00  --smt_preprocessing                     true
% 3.40/1.00  --smt_ac_axioms                         fast
% 3.40/1.00  --preprocessed_out                      false
% 3.40/1.00  --preprocessed_stats                    false
% 3.40/1.00  
% 3.40/1.00  ------ Abstraction refinement Options
% 3.40/1.00  
% 3.40/1.00  --abstr_ref                             []
% 3.40/1.00  --abstr_ref_prep                        false
% 3.40/1.00  --abstr_ref_until_sat                   false
% 3.40/1.00  --abstr_ref_sig_restrict                funpre
% 3.40/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/1.00  --abstr_ref_under                       []
% 3.40/1.00  
% 3.40/1.00  ------ SAT Options
% 3.40/1.00  
% 3.40/1.00  --sat_mode                              false
% 3.40/1.00  --sat_fm_restart_options                ""
% 3.40/1.00  --sat_gr_def                            false
% 3.40/1.00  --sat_epr_types                         true
% 3.40/1.00  --sat_non_cyclic_types                  false
% 3.40/1.00  --sat_finite_models                     false
% 3.40/1.00  --sat_fm_lemmas                         false
% 3.40/1.00  --sat_fm_prep                           false
% 3.40/1.00  --sat_fm_uc_incr                        true
% 3.40/1.00  --sat_out_model                         small
% 3.40/1.00  --sat_out_clauses                       false
% 3.40/1.00  
% 3.40/1.00  ------ QBF Options
% 3.40/1.00  
% 3.40/1.00  --qbf_mode                              false
% 3.40/1.00  --qbf_elim_univ                         false
% 3.40/1.00  --qbf_dom_inst                          none
% 3.40/1.00  --qbf_dom_pre_inst                      false
% 3.40/1.00  --qbf_sk_in                             false
% 3.40/1.00  --qbf_pred_elim                         true
% 3.40/1.00  --qbf_split                             512
% 3.40/1.00  
% 3.40/1.00  ------ BMC1 Options
% 3.40/1.00  
% 3.40/1.00  --bmc1_incremental                      false
% 3.40/1.00  --bmc1_axioms                           reachable_all
% 3.40/1.00  --bmc1_min_bound                        0
% 3.40/1.00  --bmc1_max_bound                        -1
% 3.40/1.00  --bmc1_max_bound_default                -1
% 3.40/1.00  --bmc1_symbol_reachability              true
% 3.40/1.00  --bmc1_property_lemmas                  false
% 3.40/1.00  --bmc1_k_induction                      false
% 3.40/1.00  --bmc1_non_equiv_states                 false
% 3.40/1.00  --bmc1_deadlock                         false
% 3.40/1.00  --bmc1_ucm                              false
% 3.40/1.00  --bmc1_add_unsat_core                   none
% 3.40/1.00  --bmc1_unsat_core_children              false
% 3.40/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/1.00  --bmc1_out_stat                         full
% 3.40/1.00  --bmc1_ground_init                      false
% 3.40/1.00  --bmc1_pre_inst_next_state              false
% 3.40/1.00  --bmc1_pre_inst_state                   false
% 3.40/1.00  --bmc1_pre_inst_reach_state             false
% 3.40/1.00  --bmc1_out_unsat_core                   false
% 3.40/1.00  --bmc1_aig_witness_out                  false
% 3.40/1.00  --bmc1_verbose                          false
% 3.40/1.00  --bmc1_dump_clauses_tptp                false
% 3.40/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.40/1.00  --bmc1_dump_file                        -
% 3.40/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.40/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.40/1.00  --bmc1_ucm_extend_mode                  1
% 3.40/1.00  --bmc1_ucm_init_mode                    2
% 3.40/1.00  --bmc1_ucm_cone_mode                    none
% 3.40/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.40/1.00  --bmc1_ucm_relax_model                  4
% 3.40/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.40/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/1.00  --bmc1_ucm_layered_model                none
% 3.40/1.00  --bmc1_ucm_max_lemma_size               10
% 3.40/1.00  
% 3.40/1.00  ------ AIG Options
% 3.40/1.00  
% 3.40/1.00  --aig_mode                              false
% 3.40/1.00  
% 3.40/1.00  ------ Instantiation Options
% 3.40/1.00  
% 3.40/1.00  --instantiation_flag                    true
% 3.40/1.00  --inst_sos_flag                         true
% 3.40/1.00  --inst_sos_phase                        true
% 3.40/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel_side                     none
% 3.40/1.00  --inst_solver_per_active                1400
% 3.40/1.00  --inst_solver_calls_frac                1.
% 3.40/1.00  --inst_passive_queue_type               priority_queues
% 3.40/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/1.00  --inst_passive_queues_freq              [25;2]
% 3.40/1.00  --inst_dismatching                      true
% 3.40/1.00  --inst_eager_unprocessed_to_passive     true
% 3.40/1.00  --inst_prop_sim_given                   true
% 3.40/1.00  --inst_prop_sim_new                     false
% 3.40/1.00  --inst_subs_new                         false
% 3.40/1.00  --inst_eq_res_simp                      false
% 3.40/1.00  --inst_subs_given                       false
% 3.40/1.00  --inst_orphan_elimination               true
% 3.40/1.00  --inst_learning_loop_flag               true
% 3.40/1.00  --inst_learning_start                   3000
% 3.40/1.00  --inst_learning_factor                  2
% 3.40/1.00  --inst_start_prop_sim_after_learn       3
% 3.40/1.00  --inst_sel_renew                        solver
% 3.40/1.00  --inst_lit_activity_flag                true
% 3.40/1.00  --inst_restr_to_given                   false
% 3.40/1.00  --inst_activity_threshold               500
% 3.40/1.00  --inst_out_proof                        true
% 3.40/1.00  
% 3.40/1.00  ------ Resolution Options
% 3.40/1.00  
% 3.40/1.00  --resolution_flag                       false
% 3.40/1.00  --res_lit_sel                           adaptive
% 3.40/1.00  --res_lit_sel_side                      none
% 3.40/1.00  --res_ordering                          kbo
% 3.40/1.00  --res_to_prop_solver                    active
% 3.40/1.00  --res_prop_simpl_new                    false
% 3.40/1.00  --res_prop_simpl_given                  true
% 3.40/1.00  --res_passive_queue_type                priority_queues
% 3.40/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/1.00  --res_passive_queues_freq               [15;5]
% 3.40/1.00  --res_forward_subs                      full
% 3.40/1.00  --res_backward_subs                     full
% 3.40/1.00  --res_forward_subs_resolution           true
% 3.40/1.00  --res_backward_subs_resolution          true
% 3.40/1.00  --res_orphan_elimination                true
% 3.40/1.00  --res_time_limit                        2.
% 3.40/1.00  --res_out_proof                         true
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Options
% 3.40/1.00  
% 3.40/1.00  --superposition_flag                    true
% 3.40/1.00  --sup_passive_queue_type                priority_queues
% 3.40/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.40/1.00  --demod_completeness_check              fast
% 3.40/1.00  --demod_use_ground                      true
% 3.40/1.00  --sup_to_prop_solver                    passive
% 3.40/1.00  --sup_prop_simpl_new                    true
% 3.40/1.00  --sup_prop_simpl_given                  true
% 3.40/1.00  --sup_fun_splitting                     true
% 3.40/1.00  --sup_smt_interval                      50000
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Simplification Setup
% 3.40/1.00  
% 3.40/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.40/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.40/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.40/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.40/1.00  --sup_immed_triv                        [TrivRules]
% 3.40/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.00  --sup_immed_bw_main                     []
% 3.40/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.40/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.00  --sup_input_bw                          []
% 3.40/1.00  
% 3.40/1.00  ------ Combination Options
% 3.40/1.00  
% 3.40/1.00  --comb_res_mult                         3
% 3.40/1.00  --comb_sup_mult                         2
% 3.40/1.00  --comb_inst_mult                        10
% 3.40/1.00  
% 3.40/1.00  ------ Debug Options
% 3.40/1.00  
% 3.40/1.00  --dbg_backtrace                         false
% 3.40/1.00  --dbg_dump_prop_clauses                 false
% 3.40/1.00  --dbg_dump_prop_clauses_file            -
% 3.40/1.00  --dbg_out_stat                          false
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  ------ Proving...
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  % SZS status Theorem for theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  fof(f2,axiom,(
% 3.40/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f26,plain,(
% 3.40/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.40/1.00    inference(nnf_transformation,[],[f2])).
% 3.40/1.00  
% 3.40/1.00  fof(f27,plain,(
% 3.40/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.40/1.00    inference(flattening,[],[f26])).
% 3.40/1.00  
% 3.40/1.00  fof(f28,plain,(
% 3.40/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.40/1.00    inference(rectify,[],[f27])).
% 3.40/1.00  
% 3.40/1.00  fof(f29,plain,(
% 3.40/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f30,plain,(
% 3.40/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.40/1.00  
% 3.40/1.00  fof(f43,plain,(
% 3.40/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.40/1.00    inference(cnf_transformation,[],[f30])).
% 3.40/1.00  
% 3.40/1.00  fof(f4,axiom,(
% 3.40/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f51,plain,(
% 3.40/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.40/1.00    inference(cnf_transformation,[],[f4])).
% 3.40/1.00  
% 3.40/1.00  fof(f82,plain,(
% 3.40/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.40/1.00    inference(definition_unfolding,[],[f43,f51])).
% 3.40/1.00  
% 3.40/1.00  fof(f99,plain,(
% 3.40/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.40/1.00    inference(equality_resolution,[],[f82])).
% 3.40/1.00  
% 3.40/1.00  fof(f12,axiom,(
% 3.40/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f23,plain,(
% 3.40/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.40/1.00    inference(ennf_transformation,[],[f12])).
% 3.40/1.00  
% 3.40/1.00  fof(f33,plain,(
% 3.40/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.40/1.00    inference(nnf_transformation,[],[f23])).
% 3.40/1.00  
% 3.40/1.00  fof(f34,plain,(
% 3.40/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.40/1.00    inference(flattening,[],[f33])).
% 3.40/1.00  
% 3.40/1.00  fof(f35,plain,(
% 3.40/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.40/1.00    inference(rectify,[],[f34])).
% 3.40/1.00  
% 3.40/1.00  fof(f36,plain,(
% 3.40/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f37,plain,(
% 3.40/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.40/1.00  
% 3.40/1.00  fof(f59,plain,(
% 3.40/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.40/1.00    inference(cnf_transformation,[],[f37])).
% 3.40/1.00  
% 3.40/1.00  fof(f15,axiom,(
% 3.40/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f69,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f15])).
% 3.40/1.00  
% 3.40/1.00  fof(f16,axiom,(
% 3.40/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f70,plain,(
% 3.40/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f16])).
% 3.40/1.00  
% 3.40/1.00  fof(f74,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f69,f70])).
% 3.40/1.00  
% 3.40/1.00  fof(f94,plain,(
% 3.40/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.40/1.00    inference(definition_unfolding,[],[f59,f74])).
% 3.40/1.00  
% 3.40/1.00  fof(f109,plain,(
% 3.40/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 3.40/1.00    inference(equality_resolution,[],[f94])).
% 3.40/1.00  
% 3.40/1.00  fof(f47,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f30])).
% 3.40/1.00  
% 3.40/1.00  fof(f78,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f47,f51])).
% 3.40/1.00  
% 3.40/1.00  fof(f45,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f30])).
% 3.40/1.00  
% 3.40/1.00  fof(f80,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f45,f51])).
% 3.40/1.00  
% 3.40/1.00  fof(f60,plain,(
% 3.40/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.40/1.00    inference(cnf_transformation,[],[f37])).
% 3.40/1.00  
% 3.40/1.00  fof(f93,plain,(
% 3.40/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.40/1.00    inference(definition_unfolding,[],[f60,f74])).
% 3.40/1.00  
% 3.40/1.00  fof(f107,plain,(
% 3.40/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 3.40/1.00    inference(equality_resolution,[],[f93])).
% 3.40/1.00  
% 3.40/1.00  fof(f108,plain,(
% 3.40/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 3.40/1.00    inference(equality_resolution,[],[f107])).
% 3.40/1.00  
% 3.40/1.00  fof(f18,conjecture,(
% 3.40/1.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f19,negated_conjecture,(
% 3.40/1.00    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.40/1.00    inference(negated_conjecture,[],[f18])).
% 3.40/1.00  
% 3.40/1.00  fof(f25,plain,(
% 3.40/1.00    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.40/1.00    inference(ennf_transformation,[],[f19])).
% 3.40/1.00  
% 3.40/1.00  fof(f38,plain,(
% 3.40/1.00    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 3.40/1.00    inference(nnf_transformation,[],[f25])).
% 3.40/1.00  
% 3.40/1.00  fof(f39,plain,(
% 3.40/1.00    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2))),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f40,plain,(
% 3.40/1.00    (r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2)),
% 3.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f39])).
% 3.40/1.00  
% 3.40/1.00  fof(f73,plain,(
% 3.40/1.00    r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2),
% 3.40/1.00    inference(cnf_transformation,[],[f40])).
% 3.40/1.00  
% 3.40/1.00  fof(f13,axiom,(
% 3.40/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f67,plain,(
% 3.40/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f13])).
% 3.40/1.00  
% 3.40/1.00  fof(f14,axiom,(
% 3.40/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f68,plain,(
% 3.40/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f14])).
% 3.40/1.00  
% 3.40/1.00  fof(f75,plain,(
% 3.40/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f68,f74])).
% 3.40/1.00  
% 3.40/1.00  fof(f76,plain,(
% 3.40/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.40/1.00    inference(definition_unfolding,[],[f67,f75])).
% 3.40/1.00  
% 3.40/1.00  fof(f96,plain,(
% 3.40/1.00    r2_hidden(sK3,sK2) | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK2),
% 3.40/1.00    inference(definition_unfolding,[],[f73,f51,f76])).
% 3.40/1.00  
% 3.40/1.00  fof(f72,plain,(
% 3.40/1.00    ~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2),
% 3.40/1.00    inference(cnf_transformation,[],[f40])).
% 3.40/1.00  
% 3.40/1.00  fof(f97,plain,(
% 3.40/1.00    ~r2_hidden(sK3,sK2) | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK2),
% 3.40/1.00    inference(definition_unfolding,[],[f72,f51,f76])).
% 3.40/1.00  
% 3.40/1.00  cnf(c_558,plain,
% 3.40/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.40/1.00      theory(equality) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1190,plain,
% 3.40/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_558]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2390,plain,
% 3.40/1.00      ( r2_hidden(sK3,X0)
% 3.40/1.00      | ~ r2_hidden(sK3,sK2)
% 3.40/1.00      | X0 != sK2
% 3.40/1.00      | sK3 != sK3 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_1190]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_4294,plain,
% 3.40/1.00      ( r2_hidden(sK3,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))))
% 3.40/1.00      | ~ r2_hidden(sK3,sK2)
% 3.40/1.00      | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK2
% 3.40/1.00      | sK3 != sK3 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2390]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_6,plain,
% 3.40/1.00      ( ~ r2_hidden(X0,X1)
% 3.40/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.40/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1719,plain,
% 3.40/1.00      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0))
% 3.40/1.00      | ~ r2_hidden(X0,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X1,X1,X1,X2,X0)))) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3054,plain,
% 3.40/1.00      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 3.40/1.00      | ~ r2_hidden(sK3,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_1719]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_24,plain,
% 3.40/1.00      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 3.40/1.00      | X0 = X1
% 3.40/1.00      | X0 = X2
% 3.40/1.00      | X0 = X3 ),
% 3.40/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2630,plain,
% 3.40/1.00      ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(X0,X0,X0,X1,X2))
% 3.40/1.00      | sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = X0
% 3.40/1.00      | sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = X1
% 3.40/1.00      | sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = X2 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2637,plain,
% 3.40/1.00      ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 3.40/1.00      | sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) = sK3 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2630]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_554,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1762,plain,
% 3.40/1.00      ( sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) != X0
% 3.40/1.00      | sK3 != X0
% 3.40/1.00      | sK3 = sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_554]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1763,plain,
% 3.40/1.00      ( sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) != sK3
% 3.40/1.00      | sK3 = sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2)
% 3.40/1.00      | sK3 != sK3 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_1762]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_553,plain,( X0 = X0 ),theory(equality) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1715,plain,
% 3.40/1.00      ( sK2 = sK2 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_553]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1318,plain,
% 3.40/1.00      ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 3.40/1.00      | r2_hidden(sK3,X0)
% 3.40/1.00      | X0 != sK2
% 3.40/1.00      | sK3 != sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_1190]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1439,plain,
% 3.40/1.00      ( ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 3.40/1.00      | r2_hidden(sK3,sK2)
% 3.40/1.00      | sK2 != sK2
% 3.40/1.00      | sK3 != sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_1318]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2,plain,
% 3.40/1.00      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.40/1.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.40/1.00      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.40/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 3.40/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1110,plain,
% 3.40/1.00      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 3.40/1.00      | ~ r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 3.40/1.00      | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK2 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_4,plain,
% 3.40/1.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.40/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.40/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 3.40/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1112,plain,
% 3.40/1.00      ( r2_hidden(sK0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK2),sK2)
% 3.40/1.00      | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK2 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_23,plain,
% 3.40/1.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 3.40/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_37,plain,
% 3.40/1.00      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_34,plain,
% 3.40/1.00      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_26,negated_conjecture,
% 3.40/1.00      ( r2_hidden(sK3,sK2)
% 3.40/1.00      | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK2 ),
% 3.40/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_27,negated_conjecture,
% 3.40/1.00      ( ~ r2_hidden(sK3,sK2)
% 3.40/1.00      | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK2 ),
% 3.40/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(contradiction,plain,
% 3.40/1.00      ( $false ),
% 3.40/1.00      inference(minisat,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_4294,c_3054,c_2637,c_1763,c_1715,c_1439,c_1110,c_1112,
% 3.40/1.00                 c_37,c_34,c_26,c_27]) ).
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  ------                               Statistics
% 3.40/1.00  
% 3.40/1.00  ------ General
% 3.40/1.00  
% 3.40/1.00  abstr_ref_over_cycles:                  0
% 3.40/1.00  abstr_ref_under_cycles:                 0
% 3.40/1.00  gc_basic_clause_elim:                   0
% 3.40/1.00  forced_gc_time:                         0
% 3.40/1.00  parsing_time:                           0.032
% 3.40/1.00  unif_index_cands_time:                  0.
% 3.40/1.00  unif_index_add_time:                    0.
% 3.40/1.00  orderings_time:                         0.
% 3.40/1.00  out_proof_time:                         0.008
% 3.40/1.00  total_time:                             0.237
% 3.40/1.00  num_of_symbols:                         43
% 3.40/1.00  num_of_terms:                           5164
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing
% 3.40/1.00  
% 3.40/1.00  num_of_splits:                          0
% 3.40/1.00  num_of_split_atoms:                     0
% 3.40/1.00  num_of_reused_defs:                     0
% 3.40/1.00  num_eq_ax_congr_red:                    27
% 3.40/1.00  num_of_sem_filtered_clauses:            1
% 3.40/1.00  num_of_subtypes:                        0
% 3.40/1.00  monotx_restored_types:                  0
% 3.40/1.00  sat_num_of_epr_types:                   0
% 3.40/1.00  sat_num_of_non_cyclic_types:            0
% 3.40/1.00  sat_guarded_non_collapsed_types:        0
% 3.40/1.00  num_pure_diseq_elim:                    0
% 3.40/1.00  simp_replaced_by:                       0
% 3.40/1.00  res_preprocessed:                       127
% 3.40/1.00  prep_upred:                             0
% 3.40/1.00  prep_unflattend:                        4
% 3.40/1.00  smt_new_axioms:                         0
% 3.40/1.00  pred_elim_cands:                        3
% 3.40/1.00  pred_elim:                              0
% 3.40/1.00  pred_elim_cl:                           0
% 3.40/1.00  pred_elim_cycles:                       2
% 3.40/1.00  merged_defs:                            8
% 3.40/1.00  merged_defs_ncl:                        0
% 3.40/1.00  bin_hyper_res:                          8
% 3.40/1.00  prep_cycles:                            4
% 3.40/1.00  pred_elim_time:                         0.002
% 3.40/1.00  splitting_time:                         0.
% 3.40/1.00  sem_filter_time:                        0.
% 3.40/1.00  monotx_time:                            0.
% 3.40/1.00  subtype_inf_time:                       0.
% 3.40/1.00  
% 3.40/1.00  ------ Problem properties
% 3.40/1.00  
% 3.40/1.00  clauses:                                27
% 3.40/1.00  conjectures:                            2
% 3.40/1.00  epr:                                    2
% 3.40/1.00  horn:                                   20
% 3.40/1.00  ground:                                 2
% 3.40/1.00  unary:                                  9
% 3.40/1.00  binary:                                 8
% 3.40/1.00  lits:                                   59
% 3.40/1.00  lits_eq:                                26
% 3.40/1.00  fd_pure:                                0
% 3.40/1.00  fd_pseudo:                              0
% 3.40/1.00  fd_cond:                                0
% 3.40/1.00  fd_pseudo_cond:                         8
% 3.40/1.00  ac_symbols:                             0
% 3.40/1.00  
% 3.40/1.00  ------ Propositional Solver
% 3.40/1.00  
% 3.40/1.00  prop_solver_calls:                      30
% 3.40/1.00  prop_fast_solver_calls:                 665
% 3.40/1.00  smt_solver_calls:                       0
% 3.40/1.00  smt_fast_solver_calls:                  0
% 3.40/1.00  prop_num_of_clauses:                    1552
% 3.40/1.00  prop_preprocess_simplified:             6553
% 3.40/1.00  prop_fo_subsumed:                       2
% 3.40/1.00  prop_solver_time:                       0.
% 3.40/1.00  smt_solver_time:                        0.
% 3.40/1.00  smt_fast_solver_time:                   0.
% 3.40/1.00  prop_fast_solver_time:                  0.
% 3.40/1.00  prop_unsat_core_time:                   0.
% 3.40/1.00  
% 3.40/1.00  ------ QBF
% 3.40/1.00  
% 3.40/1.00  qbf_q_res:                              0
% 3.40/1.00  qbf_num_tautologies:                    0
% 3.40/1.00  qbf_prep_cycles:                        0
% 3.40/1.00  
% 3.40/1.00  ------ BMC1
% 3.40/1.00  
% 3.40/1.00  bmc1_current_bound:                     -1
% 3.40/1.00  bmc1_last_solved_bound:                 -1
% 3.40/1.00  bmc1_unsat_core_size:                   -1
% 3.40/1.00  bmc1_unsat_core_parents_size:           -1
% 3.40/1.00  bmc1_merge_next_fun:                    0
% 3.40/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.40/1.00  
% 3.40/1.00  ------ Instantiation
% 3.40/1.00  
% 3.40/1.00  inst_num_of_clauses:                    421
% 3.40/1.00  inst_num_in_passive:                    247
% 3.40/1.00  inst_num_in_active:                     168
% 3.40/1.00  inst_num_in_unprocessed:                5
% 3.40/1.00  inst_num_of_loops:                      227
% 3.40/1.00  inst_num_of_learning_restarts:          0
% 3.40/1.00  inst_num_moves_active_passive:          56
% 3.40/1.00  inst_lit_activity:                      0
% 3.40/1.00  inst_lit_activity_moves:                0
% 3.40/1.00  inst_num_tautologies:                   0
% 3.40/1.00  inst_num_prop_implied:                  0
% 3.40/1.00  inst_num_existing_simplified:           0
% 3.40/1.00  inst_num_eq_res_simplified:             0
% 3.40/1.00  inst_num_child_elim:                    0
% 3.40/1.00  inst_num_of_dismatching_blockings:      235
% 3.40/1.00  inst_num_of_non_proper_insts:           388
% 3.40/1.00  inst_num_of_duplicates:                 0
% 3.40/1.00  inst_inst_num_from_inst_to_res:         0
% 3.40/1.00  inst_dismatching_checking_time:         0.
% 3.40/1.00  
% 3.40/1.00  ------ Resolution
% 3.40/1.00  
% 3.40/1.00  res_num_of_clauses:                     0
% 3.40/1.00  res_num_in_passive:                     0
% 3.40/1.00  res_num_in_active:                      0
% 3.40/1.00  res_num_of_loops:                       131
% 3.40/1.00  res_forward_subset_subsumed:            63
% 3.40/1.00  res_backward_subset_subsumed:           0
% 3.40/1.00  res_forward_subsumed:                   0
% 3.40/1.00  res_backward_subsumed:                  0
% 3.40/1.00  res_forward_subsumption_resolution:     0
% 3.40/1.00  res_backward_subsumption_resolution:    0
% 3.40/1.00  res_clause_to_clause_subsumption:       256
% 3.40/1.00  res_orphan_elimination:                 0
% 3.40/1.00  res_tautology_del:                      36
% 3.40/1.00  res_num_eq_res_simplified:              0
% 3.40/1.00  res_num_sel_changes:                    0
% 3.40/1.00  res_moves_from_active_to_pass:          0
% 3.40/1.00  
% 3.40/1.00  ------ Superposition
% 3.40/1.00  
% 3.40/1.00  sup_time_total:                         0.
% 3.40/1.00  sup_time_generating:                    0.
% 3.40/1.00  sup_time_sim_full:                      0.
% 3.40/1.00  sup_time_sim_immed:                     0.
% 3.40/1.00  
% 3.40/1.00  sup_num_of_clauses:                     64
% 3.40/1.00  sup_num_in_active:                      39
% 3.40/1.00  sup_num_in_passive:                     25
% 3.40/1.00  sup_num_of_loops:                       44
% 3.40/1.00  sup_fw_superposition:                   116
% 3.40/1.00  sup_bw_superposition:                   81
% 3.40/1.00  sup_immediate_simplified:               114
% 3.40/1.00  sup_given_eliminated:                   1
% 3.40/1.00  comparisons_done:                       0
% 3.40/1.00  comparisons_avoided:                    6
% 3.40/1.00  
% 3.40/1.00  ------ Simplifications
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  sim_fw_subset_subsumed:                 4
% 3.40/1.00  sim_bw_subset_subsumed:                 1
% 3.40/1.00  sim_fw_subsumed:                        36
% 3.40/1.00  sim_bw_subsumed:                        6
% 3.40/1.00  sim_fw_subsumption_res:                 0
% 3.40/1.00  sim_bw_subsumption_res:                 0
% 3.40/1.00  sim_tautology_del:                      6
% 3.40/1.00  sim_eq_tautology_del:                   31
% 3.40/1.00  sim_eq_res_simp:                        0
% 3.40/1.00  sim_fw_demodulated:                     49
% 3.40/1.00  sim_bw_demodulated:                     2
% 3.40/1.00  sim_light_normalised:                   37
% 3.40/1.00  sim_joinable_taut:                      0
% 3.40/1.00  sim_joinable_simp:                      0
% 3.40/1.00  sim_ac_normalised:                      0
% 3.40/1.00  sim_smt_subsumption:                    0
% 3.40/1.00  
%------------------------------------------------------------------------------
