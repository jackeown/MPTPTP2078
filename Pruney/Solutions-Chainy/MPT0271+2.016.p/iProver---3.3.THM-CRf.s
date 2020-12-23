%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:08 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 745 expanded)
%              Number of clauses        :   56 ( 157 expanded)
%              Number of leaves         :   19 ( 208 expanded)
%              Depth                    :   17
%              Number of atoms          :  449 (2509 expanded)
%              Number of equality atoms :  203 (1234 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f91])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
        & ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK4,sK5)
        | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0 )
      & ( r2_hidden(sK4,sK5)
        | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r2_hidden(sK4,sK5)
      | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0 )
    & ( r2_hidden(sK4,sK5)
      | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f41,f42])).

fof(f79,plain,
    ( r2_hidden(sK4,sK5)
    | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f115,plain,
    ( r2_hidden(sK4,sK5)
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f79,f52,f83])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f61,f82])).

fof(f126,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f104])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f62,f82])).

fof(f124,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f103])).

fof(f125,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f124])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f94,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f77,f52,f83])).

fof(f128,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ),
    inference(equality_resolution,[],[f112])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f116,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f80,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f80,f52,f83])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f83])).

fof(f121,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f56,f52])).

fof(f93,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f54,f52,f81])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_31008,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_31010,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
    | r2_hidden(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_31008])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_31001,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
    | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_31003,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
    | ~ r2_hidden(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)))) ),
    inference(instantiation,[status(thm)],[c_31001])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_355,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2476,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_359,c_355])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK4,sK5)
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_9153,plain,
    ( r2_hidden(k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)),X0)
    | r2_hidden(sK4,sK5)
    | ~ r2_hidden(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_2476,c_31])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_58,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_61,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_937,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1691,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_937])).

cnf(c_1693,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1691])).

cnf(c_1695,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1271,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(X0,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1743,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
    | r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_356,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1358,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_356,c_355])).

cnf(c_8947,plain,
    ( r2_hidden(sK4,sK5)
    | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1358,c_31])).

cnf(c_9665,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
    | r2_hidden(X1,k1_xboole_0)
    | r2_hidden(sK4,sK5)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_8947,c_359])).

cnf(c_9667,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
    | r2_hidden(sK4,sK5)
    | r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_9665])).

cnf(c_9675,plain,
    ( r2_hidden(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9153,c_58,c_61,c_1695,c_1743,c_9667])).

cnf(c_30,negated_conjecture,
    ( ~ r2_hidden(sK4,sK5)
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_9686,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_9675,c_30])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2474,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
    | ~ r2_hidden(X1,k1_xboole_0)
    | r2_hidden(sK4,sK5)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_359,c_31])).

cnf(c_2596,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
    | ~ r2_hidden(X0,k1_xboole_0)
    | r2_hidden(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_2474,c_355])).

cnf(c_2631,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2596,c_1693])).

cnf(c_3186,plain,
    ( r2_hidden(sK0(X0,X1,k1_xboole_0),X0)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_2631])).

cnf(c_9894,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_9686,c_3186])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_9900,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) = sK4 ),
    inference(resolution,[status(thm)],[c_9894,c_14])).

cnf(c_9905,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),X0)
    | ~ r2_hidden(sK4,X0) ),
    inference(resolution,[status(thm)],[c_9900,c_2476])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_12692,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK4,sK5)
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9905,c_3])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_956,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12023,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_956])).

cnf(c_12048,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))
    | r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12023])).

cnf(c_12050,plain,
    ( r2_hidden(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))
    | ~ r2_hidden(sK4,sK4)
    | r2_hidden(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12048])).

cnf(c_5323,plain,
    ( X0 != X1
    | X0 = sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_5324,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) != sK4
    | sK4 = sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_5323])).

cnf(c_1049,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1531,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
    | ~ r2_hidden(X3,k1_xboole_0)
    | X0 != X3
    | k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_3585,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
    | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
    | X0 != sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
    | k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_3587,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))) != k1_xboole_0
    | sK4 != sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3585])).

cnf(c_80,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31010,c_31003,c_12692,c_12050,c_9900,c_9675,c_5324,c_3587,c_1695,c_80,c_61,c_58,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.91/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/1.49  
% 7.91/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.91/1.49  
% 7.91/1.49  ------  iProver source info
% 7.91/1.49  
% 7.91/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.91/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.91/1.49  git: non_committed_changes: false
% 7.91/1.49  git: last_make_outside_of_git: false
% 7.91/1.49  
% 7.91/1.49  ------ 
% 7.91/1.49  ------ Parsing...
% 7.91/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.91/1.49  
% 7.91/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.91/1.49  
% 7.91/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.91/1.49  
% 7.91/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.49  ------ Proving...
% 7.91/1.49  ------ Problem Properties 
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  clauses                                 32
% 7.91/1.49  conjectures                             2
% 7.91/1.49  EPR                                     0
% 7.91/1.49  Horn                                    18
% 7.91/1.49  unary                                   9
% 7.91/1.49  binary                                  8
% 7.91/1.49  lits                                    72
% 7.91/1.49  lits eq                                 35
% 7.91/1.49  fd_pure                                 0
% 7.91/1.49  fd_pseudo                               0
% 7.91/1.49  fd_cond                                 0
% 7.91/1.49  fd_pseudo_cond                          12
% 7.91/1.49  AC symbols                              0
% 7.91/1.49  
% 7.91/1.49  ------ Input Options Time Limit: Unbounded
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  ------ 
% 7.91/1.49  Current options:
% 7.91/1.49  ------ 
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  ------ Proving...
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  % SZS status Theorem for theBenchmark.p
% 7.91/1.49  
% 7.91/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.91/1.49  
% 7.91/1.49  fof(f2,axiom,(
% 7.91/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f21,plain,(
% 7.91/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.91/1.49    inference(nnf_transformation,[],[f2])).
% 7.91/1.49  
% 7.91/1.49  fof(f22,plain,(
% 7.91/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.91/1.49    inference(flattening,[],[f21])).
% 7.91/1.49  
% 7.91/1.49  fof(f23,plain,(
% 7.91/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.91/1.49    inference(rectify,[],[f22])).
% 7.91/1.49  
% 7.91/1.49  fof(f24,plain,(
% 7.91/1.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.91/1.49    introduced(choice_axiom,[])).
% 7.91/1.49  
% 7.91/1.49  fof(f25,plain,(
% 7.91/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.91/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 7.91/1.49  
% 7.91/1.49  fof(f45,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.91/1.49    inference(cnf_transformation,[],[f25])).
% 7.91/1.49  
% 7.91/1.49  fof(f4,axiom,(
% 7.91/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f52,plain,(
% 7.91/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f4])).
% 7.91/1.49  
% 7.91/1.49  fof(f91,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.91/1.49    inference(definition_unfolding,[],[f45,f52])).
% 7.91/1.49  
% 7.91/1.49  fof(f118,plain,(
% 7.91/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.91/1.49    inference(equality_resolution,[],[f91])).
% 7.91/1.49  
% 7.91/1.49  fof(f46,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.91/1.49    inference(cnf_transformation,[],[f25])).
% 7.91/1.49  
% 7.91/1.49  fof(f90,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.91/1.49    inference(definition_unfolding,[],[f46,f52])).
% 7.91/1.49  
% 7.91/1.49  fof(f117,plain,(
% 7.91/1.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.91/1.49    inference(equality_resolution,[],[f90])).
% 7.91/1.49  
% 7.91/1.49  fof(f17,conjecture,(
% 7.91/1.49    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f18,negated_conjecture,(
% 7.91/1.49    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 7.91/1.49    inference(negated_conjecture,[],[f17])).
% 7.91/1.49  
% 7.91/1.49  fof(f20,plain,(
% 7.91/1.49    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <~> r2_hidden(X0,X1))),
% 7.91/1.49    inference(ennf_transformation,[],[f18])).
% 7.91/1.49  
% 7.91/1.49  fof(f41,plain,(
% 7.91/1.49    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0))),
% 7.91/1.49    inference(nnf_transformation,[],[f20])).
% 7.91/1.49  
% 7.91/1.49  fof(f42,plain,(
% 7.91/1.49    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)) => ((~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0) & (r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0))),
% 7.91/1.49    introduced(choice_axiom,[])).
% 7.91/1.49  
% 7.91/1.49  fof(f43,plain,(
% 7.91/1.49    (~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0) & (r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0)),
% 7.91/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f41,f42])).
% 7.91/1.49  
% 7.91/1.49  fof(f79,plain,(
% 7.91/1.49    r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0),
% 7.91/1.49    inference(cnf_transformation,[],[f43])).
% 7.91/1.49  
% 7.91/1.49  fof(f11,axiom,(
% 7.91/1.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f67,plain,(
% 7.91/1.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f11])).
% 7.91/1.49  
% 7.91/1.49  fof(f12,axiom,(
% 7.91/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f68,plain,(
% 7.91/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f12])).
% 7.91/1.49  
% 7.91/1.49  fof(f13,axiom,(
% 7.91/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f69,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f13])).
% 7.91/1.49  
% 7.91/1.49  fof(f82,plain,(
% 7.91/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.91/1.49    inference(definition_unfolding,[],[f68,f69])).
% 7.91/1.49  
% 7.91/1.49  fof(f83,plain,(
% 7.91/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.91/1.49    inference(definition_unfolding,[],[f67,f82])).
% 7.91/1.49  
% 7.91/1.49  fof(f115,plain,(
% 7.91/1.49    r2_hidden(sK4,sK5) | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0),
% 7.91/1.49    inference(definition_unfolding,[],[f79,f52,f83])).
% 7.91/1.49  
% 7.91/1.49  fof(f10,axiom,(
% 7.91/1.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f30,plain,(
% 7.91/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.91/1.49    inference(nnf_transformation,[],[f10])).
% 7.91/1.49  
% 7.91/1.49  fof(f31,plain,(
% 7.91/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.91/1.49    inference(flattening,[],[f30])).
% 7.91/1.49  
% 7.91/1.49  fof(f32,plain,(
% 7.91/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.91/1.49    inference(rectify,[],[f31])).
% 7.91/1.49  
% 7.91/1.49  fof(f33,plain,(
% 7.91/1.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.91/1.49    introduced(choice_axiom,[])).
% 7.91/1.49  
% 7.91/1.49  fof(f34,plain,(
% 7.91/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.91/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 7.91/1.49  
% 7.91/1.49  fof(f61,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.91/1.49    inference(cnf_transformation,[],[f34])).
% 7.91/1.49  
% 7.91/1.49  fof(f104,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.91/1.49    inference(definition_unfolding,[],[f61,f82])).
% 7.91/1.49  
% 7.91/1.49  fof(f126,plain,(
% 7.91/1.49    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.91/1.49    inference(equality_resolution,[],[f104])).
% 7.91/1.49  
% 7.91/1.49  fof(f62,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.91/1.49    inference(cnf_transformation,[],[f34])).
% 7.91/1.49  
% 7.91/1.49  fof(f103,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.91/1.49    inference(definition_unfolding,[],[f62,f82])).
% 7.91/1.49  
% 7.91/1.49  fof(f124,plain,(
% 7.91/1.49    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 7.91/1.49    inference(equality_resolution,[],[f103])).
% 7.91/1.49  
% 7.91/1.49  fof(f125,plain,(
% 7.91/1.49    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 7.91/1.49    inference(equality_resolution,[],[f124])).
% 7.91/1.49  
% 7.91/1.49  fof(f7,axiom,(
% 7.91/1.49    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f55,plain,(
% 7.91/1.49    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.91/1.49    inference(cnf_transformation,[],[f7])).
% 7.91/1.49  
% 7.91/1.49  fof(f94,plain,(
% 7.91/1.49    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0) )),
% 7.91/1.49    inference(definition_unfolding,[],[f55,f52])).
% 7.91/1.49  
% 7.91/1.49  fof(f16,axiom,(
% 7.91/1.49    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f39,plain,(
% 7.91/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.91/1.49    inference(nnf_transformation,[],[f16])).
% 7.91/1.49  
% 7.91/1.49  fof(f40,plain,(
% 7.91/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.91/1.49    inference(flattening,[],[f39])).
% 7.91/1.49  
% 7.91/1.49  fof(f77,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f40])).
% 7.91/1.49  
% 7.91/1.49  fof(f112,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 7.91/1.49    inference(definition_unfolding,[],[f77,f52,f83])).
% 7.91/1.49  
% 7.91/1.49  fof(f128,plain,(
% 7.91/1.49    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 7.91/1.49    inference(equality_resolution,[],[f112])).
% 7.91/1.49  
% 7.91/1.49  fof(f47,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.91/1.49    inference(cnf_transformation,[],[f25])).
% 7.91/1.49  
% 7.91/1.49  fof(f89,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.91/1.49    inference(definition_unfolding,[],[f47,f52])).
% 7.91/1.49  
% 7.91/1.49  fof(f116,plain,(
% 7.91/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.91/1.49    inference(equality_resolution,[],[f89])).
% 7.91/1.49  
% 7.91/1.49  fof(f80,plain,(
% 7.91/1.49    ~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0),
% 7.91/1.49    inference(cnf_transformation,[],[f43])).
% 7.91/1.49  
% 7.91/1.49  fof(f114,plain,(
% 7.91/1.49    ~r2_hidden(sK4,sK5) | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0),
% 7.91/1.49    inference(definition_unfolding,[],[f80,f52,f83])).
% 7.91/1.49  
% 7.91/1.49  fof(f48,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f25])).
% 7.91/1.49  
% 7.91/1.49  fof(f88,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.91/1.49    inference(definition_unfolding,[],[f48,f52])).
% 7.91/1.49  
% 7.91/1.49  fof(f9,axiom,(
% 7.91/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f26,plain,(
% 7.91/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.91/1.49    inference(nnf_transformation,[],[f9])).
% 7.91/1.49  
% 7.91/1.49  fof(f27,plain,(
% 7.91/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.91/1.49    inference(rectify,[],[f26])).
% 7.91/1.49  
% 7.91/1.49  fof(f28,plain,(
% 7.91/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.91/1.49    introduced(choice_axiom,[])).
% 7.91/1.49  
% 7.91/1.49  fof(f29,plain,(
% 7.91/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.91/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 7.91/1.49  
% 7.91/1.49  fof(f57,plain,(
% 7.91/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.91/1.49    inference(cnf_transformation,[],[f29])).
% 7.91/1.49  
% 7.91/1.49  fof(f98,plain,(
% 7.91/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.91/1.49    inference(definition_unfolding,[],[f57,f83])).
% 7.91/1.49  
% 7.91/1.49  fof(f121,plain,(
% 7.91/1.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.91/1.49    inference(equality_resolution,[],[f98])).
% 7.91/1.49  
% 7.91/1.49  fof(f49,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f25])).
% 7.91/1.49  
% 7.91/1.49  fof(f87,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.91/1.49    inference(definition_unfolding,[],[f49,f52])).
% 7.91/1.49  
% 7.91/1.49  fof(f6,axiom,(
% 7.91/1.49    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f54,plain,(
% 7.91/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 7.91/1.49    inference(cnf_transformation,[],[f6])).
% 7.91/1.49  
% 7.91/1.49  fof(f8,axiom,(
% 7.91/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f56,plain,(
% 7.91/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f8])).
% 7.91/1.49  
% 7.91/1.49  fof(f81,plain,(
% 7.91/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.91/1.49    inference(definition_unfolding,[],[f56,f52])).
% 7.91/1.49  
% 7.91/1.49  fof(f93,plain,(
% 7.91/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 7.91/1.49    inference(definition_unfolding,[],[f54,f52,f81])).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7,plain,
% 7.91/1.49      ( r2_hidden(X0,X1)
% 7.91/1.49      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f118]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_31008,plain,
% 7.91/1.49      ( r2_hidden(X0,X1)
% 7.91/1.49      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_31010,plain,
% 7.91/1.49      ( ~ r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
% 7.91/1.49      | r2_hidden(sK4,sK4) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_31008]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,X1)
% 7.91/1.49      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f117]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_31001,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
% 7.91/1.49      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_31003,plain,
% 7.91/1.49      ( ~ r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
% 7.91/1.49      | ~ r2_hidden(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)))) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_31001]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_359,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.91/1.49      theory(equality) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_355,plain,( X0 = X0 ),theory(equality) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2476,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_359,c_355]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_31,negated_conjecture,
% 7.91/1.49      ( r2_hidden(sK4,sK5)
% 7.91/1.49      | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f115]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9153,plain,
% 7.91/1.49      ( r2_hidden(k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)),X0)
% 7.91/1.49      | r2_hidden(sK4,sK5)
% 7.91/1.49      | ~ r2_hidden(k1_xboole_0,X0) ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_2476,c_31]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_20,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.91/1.49      inference(cnf_transformation,[],[f126]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_58,plain,
% 7.91/1.49      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_19,plain,
% 7.91/1.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f125]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_61,plain,
% 7.91/1.49      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_10,plain,
% 7.91/1.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_28,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f128]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_937,plain,
% 7.91/1.49      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1691,plain,
% 7.91/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_10,c_937]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1693,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.91/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1691]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1695,plain,
% 7.91/1.49      ( ~ r2_hidden(sK4,k1_xboole_0) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_1693]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,X1)
% 7.91/1.49      | r2_hidden(X0,X2)
% 7.91/1.49      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1271,plain,
% 7.91/1.49      ( r2_hidden(X0,X1)
% 7.91/1.49      | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 7.91/1.49      | r2_hidden(X0,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1743,plain,
% 7.91/1.49      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.91/1.49      | r2_hidden(sK4,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
% 7.91/1.49      | r2_hidden(sK4,sK5) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_1271]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_356,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1358,plain,
% 7.91/1.49      ( X0 != X1 | X1 = X0 ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_356,c_355]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_8947,plain,
% 7.91/1.49      ( r2_hidden(sK4,sK5)
% 7.91/1.49      | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_1358,c_31]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9665,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
% 7.91/1.49      | r2_hidden(X1,k1_xboole_0)
% 7.91/1.49      | r2_hidden(sK4,sK5)
% 7.91/1.49      | X1 != X0 ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_8947,c_359]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9667,plain,
% 7.91/1.49      ( ~ r2_hidden(sK4,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
% 7.91/1.49      | r2_hidden(sK4,sK5)
% 7.91/1.49      | r2_hidden(sK4,k1_xboole_0)
% 7.91/1.49      | sK4 != sK4 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_9665]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9675,plain,
% 7.91/1.49      ( r2_hidden(sK4,sK5) ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_9153,c_58,c_61,c_1695,c_1743,c_9667]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_30,negated_conjecture,
% 7.91/1.49      ( ~ r2_hidden(sK4,sK5)
% 7.91/1.49      | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f114]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9686,plain,
% 7.91/1.49      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
% 7.91/1.49      inference(backward_subsumption_resolution,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_9675,c_30]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4,plain,
% 7.91/1.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.91/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.91/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.91/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2474,plain,
% 7.91/1.49      ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
% 7.91/1.49      | ~ r2_hidden(X1,k1_xboole_0)
% 7.91/1.49      | r2_hidden(sK4,sK5)
% 7.91/1.49      | X0 != X1 ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_359,c_31]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2596,plain,
% 7.91/1.49      ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
% 7.91/1.49      | ~ r2_hidden(X0,k1_xboole_0)
% 7.91/1.49      | r2_hidden(sK4,sK5) ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_2474,c_355]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2631,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_2596,c_1693]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3186,plain,
% 7.91/1.49      ( r2_hidden(sK0(X0,X1,k1_xboole_0),X0)
% 7.91/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_4,c_2631]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9894,plain,
% 7.91/1.49      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_9686,c_3186]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.91/1.49      inference(cnf_transformation,[],[f121]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9900,plain,
% 7.91/1.49      ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) = sK4 ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_9894,c_14]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9905,plain,
% 7.91/1.49      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),X0)
% 7.91/1.49      | ~ r2_hidden(sK4,X0) ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_9900,c_2476]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3,plain,
% 7.91/1.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.91/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.91/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.91/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12692,plain,
% 7.91/1.49      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
% 7.91/1.49      | ~ r2_hidden(sK4,sK5)
% 7.91/1.49      | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
% 7.91/1.49      inference(resolution,[status(thm)],[c_9905,c_3]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9,plain,
% 7.91/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_956,plain,
% 7.91/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.91/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.91/1.49      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12023,plain,
% 7.91/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.91/1.49      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = iProver_top
% 7.91/1.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_9,c_956]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12048,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,X1)
% 7.91/1.49      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))
% 7.91/1.49      | r2_hidden(X0,k1_xboole_0) ),
% 7.91/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_12023]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12050,plain,
% 7.91/1.49      ( r2_hidden(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))
% 7.91/1.49      | ~ r2_hidden(sK4,sK4)
% 7.91/1.49      | r2_hidden(sK4,k1_xboole_0) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_12048]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5323,plain,
% 7.91/1.49      ( X0 != X1
% 7.91/1.49      | X0 = sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
% 7.91/1.49      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) != X1 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_356]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5324,plain,
% 7.91/1.49      ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) != sK4
% 7.91/1.49      | sK4 = sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
% 7.91/1.49      | sK4 != sK4 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_5323]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1049,plain,
% 7.91/1.49      ( ~ r2_hidden(X0,X1)
% 7.91/1.49      | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
% 7.91/1.49      | X2 != X0
% 7.91/1.49      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_359]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1531,plain,
% 7.91/1.49      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
% 7.91/1.49      | ~ r2_hidden(X3,k1_xboole_0)
% 7.91/1.49      | X0 != X3
% 7.91/1.49      | k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) != k1_xboole_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_1049]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3585,plain,
% 7.91/1.49      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
% 7.91/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
% 7.91/1.49      | X0 != sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
% 7.91/1.49      | k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) != k1_xboole_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_1531]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3587,plain,
% 7.91/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
% 7.91/1.49      | r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
% 7.91/1.49      | k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))) != k1_xboole_0
% 7.91/1.49      | sK4 != sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_3585]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_80,plain,
% 7.91/1.49      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))) = k1_xboole_0 ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(contradiction,plain,
% 7.91/1.49      ( $false ),
% 7.91/1.49      inference(minisat,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_31010,c_31003,c_12692,c_12050,c_9900,c_9675,c_5324,
% 7.91/1.49                 c_3587,c_1695,c_80,c_61,c_58,c_30]) ).
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.91/1.49  
% 7.91/1.49  ------                               Statistics
% 7.91/1.49  
% 7.91/1.49  ------ Selected
% 7.91/1.49  
% 7.91/1.49  total_time:                             0.898
% 7.91/1.49  
%------------------------------------------------------------------------------
