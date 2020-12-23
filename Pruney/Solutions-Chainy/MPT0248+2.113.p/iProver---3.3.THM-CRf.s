%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:26 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  115 (1395 expanded)
%              Number of clauses        :   46 ( 147 expanded)
%              Number of leaves         :   18 ( 418 expanded)
%              Depth                    :   17
%              Number of atoms          :  357 (3290 expanded)
%              Number of equality atoms :  200 (2425 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f29])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK6
        | k1_tarski(sK4) != sK5 )
      & ( k1_tarski(sK4) != sK6
        | k1_xboole_0 != sK5 )
      & ( k1_tarski(sK4) != sK6
        | k1_tarski(sK4) != sK5 )
      & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_xboole_0 != sK6
      | k1_tarski(sK4) != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_xboole_0 != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_tarski(sK4) != sK5 )
    & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f37])).

fof(f63,plain,(
    k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f68])).

fof(f89,plain,(
    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f63,f69,f70])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f69])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f95,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f59,f70,f70])).

fof(f64,plain,
    ( k1_tarski(sK4) != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f64,f70,f70])).

fof(f65,plain,
    ( k1_tarski(sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,
    ( k1_xboole_0 != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,
    ( k1_xboole_0 != sK6
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f66,f70])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f69])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_699,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_22,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_702,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2112,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_702])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_693,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2384,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2112,c_693])).

cnf(c_2483,plain,
    ( sK2(sK6) = sK4
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_699,c_2384])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_697,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_974,plain,
    ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_697])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_690,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1029,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_974,c_690])).

cnf(c_21,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1249,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1029,c_21])).

cnf(c_20,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_903,plain,
    ( ~ r1_tarski(sK5,k3_enumset1(X0,X0,X0,X0,X0))
    | k3_enumset1(X0,X0,X0,X0,X0) = sK5
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_905,plain,
    ( ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_975,plain,
    ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_974])).

cnf(c_1349,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1249,c_21,c_20,c_905,c_975])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_707,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_708,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2383,plain,
    ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
    | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2112,c_708])).

cnf(c_2686,plain,
    ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_2383])).

cnf(c_3579,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2686,c_690])).

cnf(c_5343,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2483,c_21,c_20,c_905,c_975,c_3579])).

cnf(c_2382,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_2112])).

cnf(c_19,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_898,plain,
    ( ~ r1_tarski(sK6,k3_enumset1(X0,X0,X0,X0,X0))
    | k3_enumset1(X0,X0,X0,X0,X0) = sK6
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_899,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = sK6
    | k1_xboole_0 = sK6
    | r1_tarski(sK6,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_898])).

cnf(c_901,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
    | k1_xboole_0 = sK6
    | r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_2790,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2382,c_21,c_20,c_19,c_901,c_905,c_975,c_1029,c_2686])).

cnf(c_2801,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6)) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_2790,c_22])).

cnf(c_5355,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_5343,c_2801])).

cnf(c_1124,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_708])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_698,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4316,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1124,c_698])).

cnf(c_5493,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5355,c_4316])).

cnf(c_5359,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5343,c_1349])).

cnf(c_5495,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5493,c_5359])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.30  % Computer   : n006.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 19:49:37 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running in FOF mode
% 2.04/0.94  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/0.94  
% 2.04/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.04/0.94  
% 2.04/0.94  ------  iProver source info
% 2.04/0.94  
% 2.04/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.04/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.04/0.94  git: non_committed_changes: false
% 2.04/0.94  git: last_make_outside_of_git: false
% 2.04/0.94  
% 2.04/0.94  ------ 
% 2.04/0.94  
% 2.04/0.94  ------ Input Options
% 2.04/0.94  
% 2.04/0.94  --out_options                           all
% 2.04/0.94  --tptp_safe_out                         true
% 2.04/0.94  --problem_path                          ""
% 2.04/0.94  --include_path                          ""
% 2.04/0.94  --clausifier                            res/vclausify_rel
% 2.04/0.94  --clausifier_options                    --mode clausify
% 2.04/0.94  --stdin                                 false
% 2.04/0.94  --stats_out                             all
% 2.04/0.94  
% 2.04/0.94  ------ General Options
% 2.04/0.94  
% 2.04/0.94  --fof                                   false
% 2.04/0.94  --time_out_real                         305.
% 2.04/0.94  --time_out_virtual                      -1.
% 2.04/0.94  --symbol_type_check                     false
% 2.04/0.94  --clausify_out                          false
% 2.04/0.94  --sig_cnt_out                           false
% 2.04/0.94  --trig_cnt_out                          false
% 2.04/0.94  --trig_cnt_out_tolerance                1.
% 2.04/0.94  --trig_cnt_out_sk_spl                   false
% 2.04/0.94  --abstr_cl_out                          false
% 2.04/0.94  
% 2.04/0.94  ------ Global Options
% 2.04/0.94  
% 2.04/0.94  --schedule                              default
% 2.04/0.94  --add_important_lit                     false
% 2.04/0.94  --prop_solver_per_cl                    1000
% 2.04/0.94  --min_unsat_core                        false
% 2.04/0.94  --soft_assumptions                      false
% 2.04/0.94  --soft_lemma_size                       3
% 2.04/0.94  --prop_impl_unit_size                   0
% 2.04/0.94  --prop_impl_unit                        []
% 2.04/0.94  --share_sel_clauses                     true
% 2.04/0.94  --reset_solvers                         false
% 2.04/0.94  --bc_imp_inh                            [conj_cone]
% 2.04/0.94  --conj_cone_tolerance                   3.
% 2.04/0.94  --extra_neg_conj                        none
% 2.04/0.94  --large_theory_mode                     true
% 2.04/0.94  --prolific_symb_bound                   200
% 2.04/0.94  --lt_threshold                          2000
% 2.04/0.94  --clause_weak_htbl                      true
% 2.04/0.94  --gc_record_bc_elim                     false
% 2.04/0.94  
% 2.04/0.94  ------ Preprocessing Options
% 2.04/0.94  
% 2.04/0.94  --preprocessing_flag                    true
% 2.04/0.94  --time_out_prep_mult                    0.1
% 2.04/0.94  --splitting_mode                        input
% 2.04/0.94  --splitting_grd                         true
% 2.04/0.94  --splitting_cvd                         false
% 2.04/0.94  --splitting_cvd_svl                     false
% 2.04/0.94  --splitting_nvd                         32
% 2.04/0.94  --sub_typing                            true
% 2.04/0.94  --prep_gs_sim                           true
% 2.04/0.94  --prep_unflatten                        true
% 2.04/0.94  --prep_res_sim                          true
% 2.04/0.94  --prep_upred                            true
% 2.04/0.94  --prep_sem_filter                       exhaustive
% 2.04/0.94  --prep_sem_filter_out                   false
% 2.04/0.94  --pred_elim                             true
% 2.04/0.94  --res_sim_input                         true
% 2.04/0.94  --eq_ax_congr_red                       true
% 2.04/0.94  --pure_diseq_elim                       true
% 2.04/0.94  --brand_transform                       false
% 2.04/0.94  --non_eq_to_eq                          false
% 2.04/0.94  --prep_def_merge                        true
% 2.04/0.94  --prep_def_merge_prop_impl              false
% 2.04/0.94  --prep_def_merge_mbd                    true
% 2.04/0.94  --prep_def_merge_tr_red                 false
% 2.04/0.94  --prep_def_merge_tr_cl                  false
% 2.04/0.94  --smt_preprocessing                     true
% 2.04/0.94  --smt_ac_axioms                         fast
% 2.04/0.94  --preprocessed_out                      false
% 2.04/0.94  --preprocessed_stats                    false
% 2.04/0.94  
% 2.04/0.94  ------ Abstraction refinement Options
% 2.04/0.94  
% 2.04/0.94  --abstr_ref                             []
% 2.04/0.94  --abstr_ref_prep                        false
% 2.04/0.94  --abstr_ref_until_sat                   false
% 2.04/0.94  --abstr_ref_sig_restrict                funpre
% 2.04/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/0.94  --abstr_ref_under                       []
% 2.04/0.94  
% 2.04/0.94  ------ SAT Options
% 2.04/0.94  
% 2.04/0.94  --sat_mode                              false
% 2.04/0.94  --sat_fm_restart_options                ""
% 2.04/0.94  --sat_gr_def                            false
% 2.04/0.94  --sat_epr_types                         true
% 2.04/0.94  --sat_non_cyclic_types                  false
% 2.04/0.94  --sat_finite_models                     false
% 2.04/0.94  --sat_fm_lemmas                         false
% 2.04/0.94  --sat_fm_prep                           false
% 2.04/0.94  --sat_fm_uc_incr                        true
% 2.04/0.94  --sat_out_model                         small
% 2.04/0.94  --sat_out_clauses                       false
% 2.04/0.94  
% 2.04/0.94  ------ QBF Options
% 2.04/0.94  
% 2.04/0.94  --qbf_mode                              false
% 2.04/0.94  --qbf_elim_univ                         false
% 2.04/0.94  --qbf_dom_inst                          none
% 2.04/0.94  --qbf_dom_pre_inst                      false
% 2.04/0.94  --qbf_sk_in                             false
% 2.04/0.94  --qbf_pred_elim                         true
% 2.04/0.94  --qbf_split                             512
% 2.04/0.94  
% 2.04/0.94  ------ BMC1 Options
% 2.04/0.94  
% 2.04/0.94  --bmc1_incremental                      false
% 2.04/0.94  --bmc1_axioms                           reachable_all
% 2.04/0.94  --bmc1_min_bound                        0
% 2.04/0.94  --bmc1_max_bound                        -1
% 2.04/0.94  --bmc1_max_bound_default                -1
% 2.04/0.94  --bmc1_symbol_reachability              true
% 2.04/0.94  --bmc1_property_lemmas                  false
% 2.04/0.94  --bmc1_k_induction                      false
% 2.04/0.94  --bmc1_non_equiv_states                 false
% 2.04/0.94  --bmc1_deadlock                         false
% 2.04/0.94  --bmc1_ucm                              false
% 2.04/0.94  --bmc1_add_unsat_core                   none
% 2.04/0.94  --bmc1_unsat_core_children              false
% 2.04/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/0.94  --bmc1_out_stat                         full
% 2.04/0.94  --bmc1_ground_init                      false
% 2.04/0.94  --bmc1_pre_inst_next_state              false
% 2.04/0.94  --bmc1_pre_inst_state                   false
% 2.04/0.94  --bmc1_pre_inst_reach_state             false
% 2.04/0.94  --bmc1_out_unsat_core                   false
% 2.04/0.94  --bmc1_aig_witness_out                  false
% 2.04/0.94  --bmc1_verbose                          false
% 2.04/0.94  --bmc1_dump_clauses_tptp                false
% 2.04/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.04/0.94  --bmc1_dump_file                        -
% 2.04/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.04/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.04/0.94  --bmc1_ucm_extend_mode                  1
% 2.04/0.94  --bmc1_ucm_init_mode                    2
% 2.04/0.94  --bmc1_ucm_cone_mode                    none
% 2.04/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.04/0.94  --bmc1_ucm_relax_model                  4
% 2.04/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.04/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/0.94  --bmc1_ucm_layered_model                none
% 2.04/0.94  --bmc1_ucm_max_lemma_size               10
% 2.04/0.94  
% 2.04/0.94  ------ AIG Options
% 2.04/0.94  
% 2.04/0.94  --aig_mode                              false
% 2.04/0.94  
% 2.04/0.94  ------ Instantiation Options
% 2.04/0.94  
% 2.04/0.94  --instantiation_flag                    true
% 2.04/0.94  --inst_sos_flag                         false
% 2.04/0.94  --inst_sos_phase                        true
% 2.04/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/0.94  --inst_lit_sel_side                     num_symb
% 2.04/0.94  --inst_solver_per_active                1400
% 2.04/0.94  --inst_solver_calls_frac                1.
% 2.04/0.94  --inst_passive_queue_type               priority_queues
% 2.04/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/0.94  --inst_passive_queues_freq              [25;2]
% 2.04/0.94  --inst_dismatching                      true
% 2.04/0.94  --inst_eager_unprocessed_to_passive     true
% 2.04/0.94  --inst_prop_sim_given                   true
% 2.04/0.94  --inst_prop_sim_new                     false
% 2.04/0.94  --inst_subs_new                         false
% 2.04/0.94  --inst_eq_res_simp                      false
% 2.04/0.94  --inst_subs_given                       false
% 2.04/0.94  --inst_orphan_elimination               true
% 2.04/0.94  --inst_learning_loop_flag               true
% 2.04/0.94  --inst_learning_start                   3000
% 2.04/0.94  --inst_learning_factor                  2
% 2.04/0.94  --inst_start_prop_sim_after_learn       3
% 2.04/0.94  --inst_sel_renew                        solver
% 2.04/0.94  --inst_lit_activity_flag                true
% 2.04/0.94  --inst_restr_to_given                   false
% 2.04/0.94  --inst_activity_threshold               500
% 2.04/0.94  --inst_out_proof                        true
% 2.04/0.94  
% 2.04/0.94  ------ Resolution Options
% 2.04/0.94  
% 2.04/0.94  --resolution_flag                       true
% 2.04/0.94  --res_lit_sel                           adaptive
% 2.04/0.94  --res_lit_sel_side                      none
% 2.04/0.94  --res_ordering                          kbo
% 2.04/0.94  --res_to_prop_solver                    active
% 2.04/0.94  --res_prop_simpl_new                    false
% 2.04/0.94  --res_prop_simpl_given                  true
% 2.04/0.94  --res_passive_queue_type                priority_queues
% 2.04/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/0.94  --res_passive_queues_freq               [15;5]
% 2.04/0.94  --res_forward_subs                      full
% 2.04/0.94  --res_backward_subs                     full
% 2.04/0.94  --res_forward_subs_resolution           true
% 2.04/0.94  --res_backward_subs_resolution          true
% 2.04/0.94  --res_orphan_elimination                true
% 2.04/0.94  --res_time_limit                        2.
% 2.04/0.94  --res_out_proof                         true
% 2.04/0.94  
% 2.04/0.94  ------ Superposition Options
% 2.04/0.94  
% 2.04/0.94  --superposition_flag                    true
% 2.04/0.94  --sup_passive_queue_type                priority_queues
% 2.04/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.04/0.94  --demod_completeness_check              fast
% 2.04/0.94  --demod_use_ground                      true
% 2.04/0.94  --sup_to_prop_solver                    passive
% 2.04/0.94  --sup_prop_simpl_new                    true
% 2.04/0.94  --sup_prop_simpl_given                  true
% 2.04/0.94  --sup_fun_splitting                     false
% 2.04/0.94  --sup_smt_interval                      50000
% 2.04/0.94  
% 2.04/0.94  ------ Superposition Simplification Setup
% 2.04/0.94  
% 2.04/0.94  --sup_indices_passive                   []
% 2.04/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/0.94  --sup_full_bw                           [BwDemod]
% 2.04/0.94  --sup_immed_triv                        [TrivRules]
% 2.04/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/0.94  --sup_immed_bw_main                     []
% 2.04/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/0.94  
% 2.04/0.94  ------ Combination Options
% 2.04/0.94  
% 2.04/0.94  --comb_res_mult                         3
% 2.04/0.94  --comb_sup_mult                         2
% 2.04/0.94  --comb_inst_mult                        10
% 2.04/0.94  
% 2.04/0.94  ------ Debug Options
% 2.04/0.94  
% 2.04/0.94  --dbg_backtrace                         false
% 2.04/0.94  --dbg_dump_prop_clauses                 false
% 2.04/0.94  --dbg_dump_prop_clauses_file            -
% 2.04/0.94  --dbg_out_stat                          false
% 2.04/0.94  ------ Parsing...
% 2.04/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.04/0.94  
% 2.04/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.04/0.94  
% 2.04/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.04/0.94  
% 2.04/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.04/0.94  ------ Proving...
% 2.04/0.94  ------ Problem Properties 
% 2.04/0.94  
% 2.04/0.94  
% 2.04/0.94  clauses                                 23
% 2.04/0.94  conjectures                             4
% 2.04/0.94  EPR                                     1
% 2.04/0.94  Horn                                    17
% 2.04/0.94  unary                                   5
% 2.04/0.94  binary                                  10
% 2.04/0.94  lits                                    50
% 2.04/0.94  lits eq                                 19
% 2.04/0.94  fd_pure                                 0
% 2.04/0.94  fd_pseudo                               0
% 2.04/0.94  fd_cond                                 1
% 2.04/0.94  fd_pseudo_cond                          6
% 2.04/0.94  AC symbols                              0
% 2.04/0.94  
% 2.04/0.94  ------ Schedule dynamic 5 is on 
% 2.04/0.94  
% 2.04/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.04/0.94  
% 2.04/0.94  
% 2.04/0.94  ------ 
% 2.04/0.94  Current options:
% 2.04/0.94  ------ 
% 2.04/0.94  
% 2.04/0.94  ------ Input Options
% 2.04/0.94  
% 2.04/0.94  --out_options                           all
% 2.04/0.94  --tptp_safe_out                         true
% 2.04/0.94  --problem_path                          ""
% 2.04/0.94  --include_path                          ""
% 2.04/0.94  --clausifier                            res/vclausify_rel
% 2.04/0.94  --clausifier_options                    --mode clausify
% 2.04/0.94  --stdin                                 false
% 2.04/0.94  --stats_out                             all
% 2.04/0.94  
% 2.04/0.94  ------ General Options
% 2.04/0.94  
% 2.04/0.94  --fof                                   false
% 2.04/0.94  --time_out_real                         305.
% 2.04/0.94  --time_out_virtual                      -1.
% 2.04/0.94  --symbol_type_check                     false
% 2.04/0.94  --clausify_out                          false
% 2.04/0.94  --sig_cnt_out                           false
% 2.04/0.94  --trig_cnt_out                          false
% 2.04/0.94  --trig_cnt_out_tolerance                1.
% 2.04/0.94  --trig_cnt_out_sk_spl                   false
% 2.04/0.94  --abstr_cl_out                          false
% 2.04/0.94  
% 2.04/0.94  ------ Global Options
% 2.04/0.94  
% 2.04/0.94  --schedule                              default
% 2.04/0.94  --add_important_lit                     false
% 2.04/0.94  --prop_solver_per_cl                    1000
% 2.04/0.94  --min_unsat_core                        false
% 2.04/0.94  --soft_assumptions                      false
% 2.04/0.94  --soft_lemma_size                       3
% 2.04/0.94  --prop_impl_unit_size                   0
% 2.04/0.94  --prop_impl_unit                        []
% 2.04/0.94  --share_sel_clauses                     true
% 2.04/0.94  --reset_solvers                         false
% 2.04/0.94  --bc_imp_inh                            [conj_cone]
% 2.04/0.94  --conj_cone_tolerance                   3.
% 2.04/0.94  --extra_neg_conj                        none
% 2.04/0.94  --large_theory_mode                     true
% 2.04/0.94  --prolific_symb_bound                   200
% 2.04/0.94  --lt_threshold                          2000
% 2.04/0.94  --clause_weak_htbl                      true
% 2.04/0.94  --gc_record_bc_elim                     false
% 2.04/0.94  
% 2.04/0.94  ------ Preprocessing Options
% 2.04/0.94  
% 2.04/0.94  --preprocessing_flag                    true
% 2.04/0.94  --time_out_prep_mult                    0.1
% 2.04/0.94  --splitting_mode                        input
% 2.04/0.94  --splitting_grd                         true
% 2.04/0.94  --splitting_cvd                         false
% 2.04/0.94  --splitting_cvd_svl                     false
% 2.04/0.94  --splitting_nvd                         32
% 2.04/0.94  --sub_typing                            true
% 2.04/0.94  --prep_gs_sim                           true
% 2.04/0.94  --prep_unflatten                        true
% 2.04/0.94  --prep_res_sim                          true
% 2.04/0.94  --prep_upred                            true
% 2.04/0.94  --prep_sem_filter                       exhaustive
% 2.04/0.94  --prep_sem_filter_out                   false
% 2.04/0.94  --pred_elim                             true
% 2.04/0.94  --res_sim_input                         true
% 2.04/0.94  --eq_ax_congr_red                       true
% 2.04/0.94  --pure_diseq_elim                       true
% 2.04/0.94  --brand_transform                       false
% 2.04/0.94  --non_eq_to_eq                          false
% 2.04/0.94  --prep_def_merge                        true
% 2.04/0.94  --prep_def_merge_prop_impl              false
% 2.04/0.94  --prep_def_merge_mbd                    true
% 2.04/0.94  --prep_def_merge_tr_red                 false
% 2.04/0.94  --prep_def_merge_tr_cl                  false
% 2.04/0.94  --smt_preprocessing                     true
% 2.04/0.94  --smt_ac_axioms                         fast
% 2.04/0.94  --preprocessed_out                      false
% 2.04/0.94  --preprocessed_stats                    false
% 2.04/0.94  
% 2.04/0.94  ------ Abstraction refinement Options
% 2.04/0.94  
% 2.04/0.94  --abstr_ref                             []
% 2.04/0.94  --abstr_ref_prep                        false
% 2.04/0.94  --abstr_ref_until_sat                   false
% 2.04/0.94  --abstr_ref_sig_restrict                funpre
% 2.04/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/0.94  --abstr_ref_under                       []
% 2.04/0.94  
% 2.04/0.94  ------ SAT Options
% 2.04/0.94  
% 2.04/0.94  --sat_mode                              false
% 2.04/0.94  --sat_fm_restart_options                ""
% 2.04/0.94  --sat_gr_def                            false
% 2.04/0.94  --sat_epr_types                         true
% 2.04/0.94  --sat_non_cyclic_types                  false
% 2.04/0.94  --sat_finite_models                     false
% 2.04/0.94  --sat_fm_lemmas                         false
% 2.04/0.94  --sat_fm_prep                           false
% 2.04/0.94  --sat_fm_uc_incr                        true
% 2.04/0.94  --sat_out_model                         small
% 2.04/0.94  --sat_out_clauses                       false
% 2.04/0.94  
% 2.04/0.94  ------ QBF Options
% 2.04/0.94  
% 2.04/0.94  --qbf_mode                              false
% 2.04/0.94  --qbf_elim_univ                         false
% 2.04/0.94  --qbf_dom_inst                          none
% 2.04/0.94  --qbf_dom_pre_inst                      false
% 2.04/0.94  --qbf_sk_in                             false
% 2.04/0.94  --qbf_pred_elim                         true
% 2.04/0.94  --qbf_split                             512
% 2.04/0.94  
% 2.04/0.94  ------ BMC1 Options
% 2.04/0.94  
% 2.04/0.94  --bmc1_incremental                      false
% 2.04/0.94  --bmc1_axioms                           reachable_all
% 2.04/0.94  --bmc1_min_bound                        0
% 2.04/0.94  --bmc1_max_bound                        -1
% 2.04/0.94  --bmc1_max_bound_default                -1
% 2.04/0.94  --bmc1_symbol_reachability              true
% 2.04/0.94  --bmc1_property_lemmas                  false
% 2.04/0.94  --bmc1_k_induction                      false
% 2.04/0.94  --bmc1_non_equiv_states                 false
% 2.04/0.94  --bmc1_deadlock                         false
% 2.04/0.94  --bmc1_ucm                              false
% 2.04/0.94  --bmc1_add_unsat_core                   none
% 2.04/0.94  --bmc1_unsat_core_children              false
% 2.04/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/0.94  --bmc1_out_stat                         full
% 2.04/0.94  --bmc1_ground_init                      false
% 2.04/0.94  --bmc1_pre_inst_next_state              false
% 2.04/0.94  --bmc1_pre_inst_state                   false
% 2.04/0.94  --bmc1_pre_inst_reach_state             false
% 2.04/0.94  --bmc1_out_unsat_core                   false
% 2.04/0.94  --bmc1_aig_witness_out                  false
% 2.04/0.94  --bmc1_verbose                          false
% 2.04/0.94  --bmc1_dump_clauses_tptp                false
% 2.04/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.04/0.94  --bmc1_dump_file                        -
% 2.04/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.04/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.04/0.94  --bmc1_ucm_extend_mode                  1
% 2.04/0.94  --bmc1_ucm_init_mode                    2
% 2.04/0.94  --bmc1_ucm_cone_mode                    none
% 2.04/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.04/0.94  --bmc1_ucm_relax_model                  4
% 2.04/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.04/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/0.94  --bmc1_ucm_layered_model                none
% 2.04/0.94  --bmc1_ucm_max_lemma_size               10
% 2.04/0.94  
% 2.04/0.94  ------ AIG Options
% 2.04/0.94  
% 2.04/0.94  --aig_mode                              false
% 2.04/0.94  
% 2.04/0.94  ------ Instantiation Options
% 2.04/0.94  
% 2.04/0.94  --instantiation_flag                    true
% 2.04/0.94  --inst_sos_flag                         false
% 2.04/0.94  --inst_sos_phase                        true
% 2.04/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/0.94  --inst_lit_sel_side                     none
% 2.04/0.94  --inst_solver_per_active                1400
% 2.04/0.94  --inst_solver_calls_frac                1.
% 2.04/0.94  --inst_passive_queue_type               priority_queues
% 2.04/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/0.94  --inst_passive_queues_freq              [25;2]
% 2.04/0.94  --inst_dismatching                      true
% 2.04/0.94  --inst_eager_unprocessed_to_passive     true
% 2.04/0.94  --inst_prop_sim_given                   true
% 2.04/0.94  --inst_prop_sim_new                     false
% 2.04/0.94  --inst_subs_new                         false
% 2.04/0.94  --inst_eq_res_simp                      false
% 2.04/0.94  --inst_subs_given                       false
% 2.04/0.94  --inst_orphan_elimination               true
% 2.04/0.94  --inst_learning_loop_flag               true
% 2.04/0.94  --inst_learning_start                   3000
% 2.04/0.94  --inst_learning_factor                  2
% 2.04/0.94  --inst_start_prop_sim_after_learn       3
% 2.04/0.94  --inst_sel_renew                        solver
% 2.04/0.94  --inst_lit_activity_flag                true
% 2.04/0.94  --inst_restr_to_given                   false
% 2.04/0.94  --inst_activity_threshold               500
% 2.04/0.94  --inst_out_proof                        true
% 2.04/0.94  
% 2.04/0.94  ------ Resolution Options
% 2.04/0.94  
% 2.04/0.94  --resolution_flag                       false
% 2.04/0.94  --res_lit_sel                           adaptive
% 2.04/0.94  --res_lit_sel_side                      none
% 2.04/0.94  --res_ordering                          kbo
% 2.04/0.94  --res_to_prop_solver                    active
% 2.04/0.94  --res_prop_simpl_new                    false
% 2.04/0.94  --res_prop_simpl_given                  true
% 2.04/0.94  --res_passive_queue_type                priority_queues
% 2.04/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/0.94  --res_passive_queues_freq               [15;5]
% 2.04/0.94  --res_forward_subs                      full
% 2.04/0.94  --res_backward_subs                     full
% 2.04/0.94  --res_forward_subs_resolution           true
% 2.04/0.94  --res_backward_subs_resolution          true
% 2.04/0.94  --res_orphan_elimination                true
% 2.04/0.94  --res_time_limit                        2.
% 2.04/0.94  --res_out_proof                         true
% 2.04/0.94  
% 2.04/0.94  ------ Superposition Options
% 2.04/0.94  
% 2.04/0.94  --superposition_flag                    true
% 2.04/0.94  --sup_passive_queue_type                priority_queues
% 2.04/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.04/0.94  --demod_completeness_check              fast
% 2.04/0.94  --demod_use_ground                      true
% 2.04/0.94  --sup_to_prop_solver                    passive
% 2.04/0.94  --sup_prop_simpl_new                    true
% 2.04/0.94  --sup_prop_simpl_given                  true
% 2.04/0.94  --sup_fun_splitting                     false
% 2.04/0.94  --sup_smt_interval                      50000
% 2.04/0.94  
% 2.04/0.94  ------ Superposition Simplification Setup
% 2.04/0.94  
% 2.04/0.94  --sup_indices_passive                   []
% 2.04/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/0.94  --sup_full_bw                           [BwDemod]
% 2.04/0.94  --sup_immed_triv                        [TrivRules]
% 2.04/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/0.94  --sup_immed_bw_main                     []
% 2.04/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/0.94  
% 2.04/0.94  ------ Combination Options
% 2.04/0.94  
% 2.04/0.94  --comb_res_mult                         3
% 2.04/0.94  --comb_sup_mult                         2
% 2.04/0.94  --comb_inst_mult                        10
% 2.04/0.94  
% 2.04/0.94  ------ Debug Options
% 2.04/0.94  
% 2.04/0.94  --dbg_backtrace                         false
% 2.04/0.94  --dbg_dump_prop_clauses                 false
% 2.04/0.94  --dbg_dump_prop_clauses_file            -
% 2.04/0.94  --dbg_out_stat                          false
% 2.04/0.94  
% 2.04/0.94  
% 2.04/0.94  
% 2.04/0.94  
% 2.04/0.94  ------ Proving...
% 2.04/0.94  
% 2.04/0.94  
% 2.04/0.94  % SZS status Theorem for theBenchmark.p
% 2.04/0.94  
% 2.04/0.94   Resolution empty clause
% 2.04/0.94  
% 2.04/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.04/0.94  
% 2.04/0.94  fof(f4,axiom,(
% 2.04/0.94    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f17,plain,(
% 2.04/0.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.04/0.94    inference(ennf_transformation,[],[f4])).
% 2.04/0.94  
% 2.04/0.94  fof(f29,plain,(
% 2.04/0.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.04/0.94    introduced(choice_axiom,[])).
% 2.04/0.94  
% 2.04/0.94  fof(f30,plain,(
% 2.04/0.94    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.04/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f29])).
% 2.04/0.94  
% 2.04/0.94  fof(f48,plain,(
% 2.04/0.94    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.04/0.94    inference(cnf_transformation,[],[f30])).
% 2.04/0.94  
% 2.04/0.94  fof(f14,conjecture,(
% 2.04/0.94    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f15,negated_conjecture,(
% 2.04/0.94    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.04/0.94    inference(negated_conjecture,[],[f14])).
% 2.04/0.94  
% 2.04/0.94  fof(f19,plain,(
% 2.04/0.94    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.04/0.94    inference(ennf_transformation,[],[f15])).
% 2.04/0.94  
% 2.04/0.94  fof(f37,plain,(
% 2.04/0.94    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4))),
% 2.04/0.94    introduced(choice_axiom,[])).
% 2.04/0.94  
% 2.04/0.94  fof(f38,plain,(
% 2.04/0.94    (k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 2.04/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f37])).
% 2.04/0.94  
% 2.04/0.94  fof(f63,plain,(
% 2.04/0.94    k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 2.04/0.94    inference(cnf_transformation,[],[f38])).
% 2.04/0.94  
% 2.04/0.94  fof(f13,axiom,(
% 2.04/0.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f62,plain,(
% 2.04/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.04/0.94    inference(cnf_transformation,[],[f13])).
% 2.04/0.94  
% 2.04/0.94  fof(f69,plain,(
% 2.04/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.04/0.94    inference(definition_unfolding,[],[f62,f68])).
% 2.04/0.94  
% 2.04/0.94  fof(f8,axiom,(
% 2.04/0.94    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f55,plain,(
% 2.04/0.94    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.04/0.94    inference(cnf_transformation,[],[f8])).
% 2.04/0.94  
% 2.04/0.94  fof(f9,axiom,(
% 2.04/0.94    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f56,plain,(
% 2.04/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.04/0.94    inference(cnf_transformation,[],[f9])).
% 2.04/0.94  
% 2.04/0.94  fof(f10,axiom,(
% 2.04/0.94    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f57,plain,(
% 2.04/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.04/0.94    inference(cnf_transformation,[],[f10])).
% 2.04/0.94  
% 2.04/0.94  fof(f11,axiom,(
% 2.04/0.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f58,plain,(
% 2.04/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.04/0.94    inference(cnf_transformation,[],[f11])).
% 2.04/0.94  
% 2.04/0.94  fof(f67,plain,(
% 2.04/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.04/0.94    inference(definition_unfolding,[],[f57,f58])).
% 2.04/0.94  
% 2.04/0.94  fof(f68,plain,(
% 2.04/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.04/0.94    inference(definition_unfolding,[],[f56,f67])).
% 2.04/0.94  
% 2.04/0.94  fof(f70,plain,(
% 2.04/0.94    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.04/0.94    inference(definition_unfolding,[],[f55,f68])).
% 2.04/0.94  
% 2.04/0.94  fof(f89,plain,(
% 2.04/0.94    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))),
% 2.04/0.94    inference(definition_unfolding,[],[f63,f69,f70])).
% 2.04/0.94  
% 2.04/0.94  fof(f3,axiom,(
% 2.04/0.94    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f24,plain,(
% 2.04/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.04/0.94    inference(nnf_transformation,[],[f3])).
% 2.04/0.94  
% 2.04/0.94  fof(f25,plain,(
% 2.04/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.04/0.94    inference(flattening,[],[f24])).
% 2.04/0.94  
% 2.04/0.94  fof(f26,plain,(
% 2.04/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.04/0.94    inference(rectify,[],[f25])).
% 2.04/0.94  
% 2.04/0.94  fof(f27,plain,(
% 2.04/0.94    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.04/0.94    introduced(choice_axiom,[])).
% 2.04/0.94  
% 2.04/0.94  fof(f28,plain,(
% 2.04/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.04/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.04/0.94  
% 2.04/0.94  fof(f44,plain,(
% 2.04/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.04/0.94    inference(cnf_transformation,[],[f28])).
% 2.04/0.94  
% 2.04/0.94  fof(f74,plain,(
% 2.04/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 2.04/0.94    inference(definition_unfolding,[],[f44,f69])).
% 2.04/0.94  
% 2.04/0.94  fof(f90,plain,(
% 2.04/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.04/0.94    inference(equality_resolution,[],[f74])).
% 2.04/0.94  
% 2.04/0.94  fof(f7,axiom,(
% 2.04/0.94    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f31,plain,(
% 2.04/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.94    inference(nnf_transformation,[],[f7])).
% 2.04/0.94  
% 2.04/0.94  fof(f32,plain,(
% 2.04/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.94    inference(rectify,[],[f31])).
% 2.04/0.94  
% 2.04/0.94  fof(f33,plain,(
% 2.04/0.94    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 2.04/0.94    introduced(choice_axiom,[])).
% 2.04/0.94  
% 2.04/0.94  fof(f34,plain,(
% 2.04/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 2.04/0.94  
% 2.04/0.94  fof(f51,plain,(
% 2.04/0.94    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.04/0.94    inference(cnf_transformation,[],[f34])).
% 2.04/0.94  
% 2.04/0.94  fof(f82,plain,(
% 2.04/0.94    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.04/0.94    inference(definition_unfolding,[],[f51,f70])).
% 2.04/0.94  
% 2.04/0.94  fof(f95,plain,(
% 2.04/0.94    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 2.04/0.94    inference(equality_resolution,[],[f82])).
% 2.04/0.94  
% 2.04/0.94  fof(f6,axiom,(
% 2.04/0.94    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f50,plain,(
% 2.04/0.94    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.04/0.94    inference(cnf_transformation,[],[f6])).
% 2.04/0.94  
% 2.04/0.94  fof(f78,plain,(
% 2.04/0.94    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 2.04/0.94    inference(definition_unfolding,[],[f50,f69])).
% 2.04/0.94  
% 2.04/0.94  fof(f12,axiom,(
% 2.04/0.94    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f35,plain,(
% 2.04/0.94    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.04/0.94    inference(nnf_transformation,[],[f12])).
% 2.04/0.94  
% 2.04/0.94  fof(f36,plain,(
% 2.04/0.94    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.04/0.94    inference(flattening,[],[f35])).
% 2.04/0.94  
% 2.04/0.94  fof(f59,plain,(
% 2.04/0.94    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.04/0.94    inference(cnf_transformation,[],[f36])).
% 2.04/0.94  
% 2.04/0.94  fof(f85,plain,(
% 2.04/0.94    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 2.04/0.94    inference(definition_unfolding,[],[f59,f70,f70])).
% 2.04/0.94  
% 2.04/0.94  fof(f64,plain,(
% 2.04/0.94    k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5),
% 2.04/0.94    inference(cnf_transformation,[],[f38])).
% 2.04/0.94  
% 2.04/0.94  fof(f88,plain,(
% 2.04/0.94    k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5),
% 2.04/0.94    inference(definition_unfolding,[],[f64,f70,f70])).
% 2.04/0.94  
% 2.04/0.94  fof(f65,plain,(
% 2.04/0.94    k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5),
% 2.04/0.94    inference(cnf_transformation,[],[f38])).
% 2.04/0.94  
% 2.04/0.94  fof(f87,plain,(
% 2.04/0.94    k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 | k1_xboole_0 != sK5),
% 2.04/0.94    inference(definition_unfolding,[],[f65,f70])).
% 2.04/0.94  
% 2.04/0.94  fof(f2,axiom,(
% 2.04/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f16,plain,(
% 2.04/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.04/0.94    inference(ennf_transformation,[],[f2])).
% 2.04/0.94  
% 2.04/0.94  fof(f20,plain,(
% 2.04/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.94    inference(nnf_transformation,[],[f16])).
% 2.04/0.94  
% 2.04/0.94  fof(f21,plain,(
% 2.04/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.94    inference(rectify,[],[f20])).
% 2.04/0.94  
% 2.04/0.94  fof(f22,plain,(
% 2.04/0.94    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.04/0.94    introduced(choice_axiom,[])).
% 2.04/0.94  
% 2.04/0.94  fof(f23,plain,(
% 2.04/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.04/0.94  
% 2.04/0.94  fof(f40,plain,(
% 2.04/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.04/0.94    inference(cnf_transformation,[],[f23])).
% 2.04/0.94  
% 2.04/0.94  fof(f41,plain,(
% 2.04/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.04/0.94    inference(cnf_transformation,[],[f23])).
% 2.04/0.94  
% 2.04/0.94  fof(f66,plain,(
% 2.04/0.94    k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5),
% 2.04/0.94    inference(cnf_transformation,[],[f38])).
% 2.04/0.94  
% 2.04/0.94  fof(f86,plain,(
% 2.04/0.94    k1_xboole_0 != sK6 | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5),
% 2.04/0.94    inference(definition_unfolding,[],[f66,f70])).
% 2.04/0.94  
% 2.04/0.94  fof(f5,axiom,(
% 2.04/0.94    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.04/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/0.94  
% 2.04/0.94  fof(f18,plain,(
% 2.04/0.94    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.04/0.94    inference(ennf_transformation,[],[f5])).
% 2.04/0.94  
% 2.04/0.94  fof(f49,plain,(
% 2.04/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.04/0.94    inference(cnf_transformation,[],[f18])).
% 2.04/0.94  
% 2.04/0.94  fof(f77,plain,(
% 2.04/0.94    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.04/0.94    inference(definition_unfolding,[],[f49,f69])).
% 2.04/0.94  
% 2.04/0.94  cnf(c_9,plain,
% 2.04/0.94      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.04/0.94      inference(cnf_transformation,[],[f48]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_699,plain,
% 2.04/0.94      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.04/0.94      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_22,negated_conjecture,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
% 2.04/0.94      inference(cnf_transformation,[],[f89]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_6,plain,
% 2.04/0.94      ( ~ r2_hidden(X0,X1)
% 2.04/0.94      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 2.04/0.94      inference(cnf_transformation,[],[f90]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_702,plain,
% 2.04/0.94      ( r2_hidden(X0,X1) != iProver_top
% 2.04/0.94      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 2.04/0.94      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_2112,plain,
% 2.04/0.94      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 2.04/0.94      | r2_hidden(X0,sK6) != iProver_top ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_22,c_702]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_15,plain,
% 2.04/0.94      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 2.04/0.94      inference(cnf_transformation,[],[f95]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_693,plain,
% 2.04/0.94      ( X0 = X1 | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 2.04/0.94      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_2384,plain,
% 2.04/0.94      ( sK4 = X0 | r2_hidden(X0,sK6) != iProver_top ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_2112,c_693]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_2483,plain,
% 2.04/0.94      ( sK2(sK6) = sK4 | sK6 = k1_xboole_0 ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_699,c_2384]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_11,plain,
% 2.04/0.94      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 2.04/0.94      inference(cnf_transformation,[],[f78]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_697,plain,
% 2.04/0.94      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 2.04/0.94      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_974,plain,
% 2.04/0.94      ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_22,c_697]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_18,plain,
% 2.04/0.94      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 2.04/0.94      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 2.04/0.94      | k1_xboole_0 = X0 ),
% 2.04/0.94      inference(cnf_transformation,[],[f85]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_690,plain,
% 2.04/0.94      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.04/0.94      | k1_xboole_0 = X1
% 2.04/0.94      | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.04/0.94      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_1029,plain,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5 | sK5 = k1_xboole_0 ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_974,c_690]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_21,negated_conjecture,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5
% 2.04/0.94      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 2.04/0.94      inference(cnf_transformation,[],[f88]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_1249,plain,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 | sK5 = k1_xboole_0 ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_1029,c_21]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_20,negated_conjecture,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 | k1_xboole_0 != sK5 ),
% 2.04/0.94      inference(cnf_transformation,[],[f87]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_903,plain,
% 2.04/0.94      ( ~ r1_tarski(sK5,k3_enumset1(X0,X0,X0,X0,X0))
% 2.04/0.94      | k3_enumset1(X0,X0,X0,X0,X0) = sK5
% 2.04/0.94      | k1_xboole_0 = sK5 ),
% 2.04/0.94      inference(instantiation,[status(thm)],[c_18]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_905,plain,
% 2.04/0.94      ( ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 2.04/0.94      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
% 2.04/0.94      | k1_xboole_0 = sK5 ),
% 2.04/0.94      inference(instantiation,[status(thm)],[c_903]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_975,plain,
% 2.04/0.94      ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 2.04/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_974]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_1349,plain,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 2.04/0.94      inference(global_propositional_subsumption,
% 2.04/0.94                [status(thm)],
% 2.04/0.94                [c_1249,c_21,c_20,c_905,c_975]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_1,plain,
% 2.04/0.94      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.04/0.94      inference(cnf_transformation,[],[f40]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_707,plain,
% 2.04/0.94      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.04/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 2.04/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_0,plain,
% 2.04/0.94      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.04/0.94      inference(cnf_transformation,[],[f41]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_708,plain,
% 2.04/0.94      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.04/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 2.04/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_2383,plain,
% 2.04/0.94      ( r2_hidden(sK0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
% 2.04/0.94      | r1_tarski(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_2112,c_708]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_2686,plain,
% 2.04/0.94      ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_707,c_2383]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_3579,plain,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6 | sK6 = k1_xboole_0 ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_2686,c_690]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_5343,plain,
% 2.04/0.94      ( sK6 = k1_xboole_0 ),
% 2.04/0.94      inference(global_propositional_subsumption,
% 2.04/0.94                [status(thm)],
% 2.04/0.94                [c_2483,c_21,c_20,c_905,c_975,c_3579]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_2382,plain,
% 2.04/0.94      ( sK5 = k1_xboole_0
% 2.04/0.94      | r2_hidden(X0,sK5) = iProver_top
% 2.04/0.94      | r2_hidden(X0,sK6) != iProver_top ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_1029,c_2112]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_19,negated_conjecture,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5 | k1_xboole_0 != sK6 ),
% 2.04/0.94      inference(cnf_transformation,[],[f86]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_898,plain,
% 2.04/0.94      ( ~ r1_tarski(sK6,k3_enumset1(X0,X0,X0,X0,X0))
% 2.04/0.94      | k3_enumset1(X0,X0,X0,X0,X0) = sK6
% 2.04/0.94      | k1_xboole_0 = sK6 ),
% 2.04/0.94      inference(instantiation,[status(thm)],[c_18]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_899,plain,
% 2.04/0.94      ( k3_enumset1(X0,X0,X0,X0,X0) = sK6
% 2.04/0.94      | k1_xboole_0 = sK6
% 2.04/0.94      | r1_tarski(sK6,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.04/0.94      inference(predicate_to_equality,[status(thm)],[c_898]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_901,plain,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK6
% 2.04/0.94      | k1_xboole_0 = sK6
% 2.04/0.94      | r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 2.04/0.94      inference(instantiation,[status(thm)],[c_899]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_2790,plain,
% 2.04/0.94      ( sK5 = k1_xboole_0 ),
% 2.04/0.94      inference(global_propositional_subsumption,
% 2.04/0.94                [status(thm)],
% 2.04/0.94                [c_2382,c_21,c_20,c_19,c_901,c_905,c_975,c_1029,c_2686]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_2801,plain,
% 2.04/0.94      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6)) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 2.04/0.94      inference(demodulation,[status(thm)],[c_2790,c_22]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_5355,plain,
% 2.04/0.94      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 2.04/0.94      inference(demodulation,[status(thm)],[c_5343,c_2801]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_1124,plain,
% 2.04/0.94      ( r1_tarski(X0,X0) = iProver_top ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_707,c_708]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_10,plain,
% 2.04/0.94      ( ~ r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
% 2.04/0.94      inference(cnf_transformation,[],[f77]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_698,plain,
% 2.04/0.94      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
% 2.04/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 2.04/0.94      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_4316,plain,
% 2.04/0.94      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
% 2.04/0.94      inference(superposition,[status(thm)],[c_1124,c_698]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_5493,plain,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k1_xboole_0 ),
% 2.04/0.94      inference(demodulation,[status(thm)],[c_5355,c_4316]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_5359,plain,
% 2.04/0.94      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k1_xboole_0 ),
% 2.04/0.94      inference(demodulation,[status(thm)],[c_5343,c_1349]) ).
% 2.04/0.94  
% 2.04/0.94  cnf(c_5495,plain,
% 2.04/0.94      ( $false ),
% 2.04/0.94      inference(forward_subsumption_resolution,[status(thm)],[c_5493,c_5359]) ).
% 2.04/0.94  
% 2.04/0.94  
% 2.04/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.04/0.94  
% 2.04/0.94  ------                               Statistics
% 2.04/0.94  
% 2.04/0.94  ------ General
% 2.04/0.94  
% 2.04/0.94  abstr_ref_over_cycles:                  0
% 2.04/0.94  abstr_ref_under_cycles:                 0
% 2.04/0.94  gc_basic_clause_elim:                   0
% 2.04/0.94  forced_gc_time:                         0
% 2.04/0.94  parsing_time:                           0.01
% 2.04/0.94  unif_index_cands_time:                  0.
% 2.04/0.94  unif_index_add_time:                    0.
% 2.04/0.94  orderings_time:                         0.
% 2.04/0.94  out_proof_time:                         0.007
% 2.04/0.94  total_time:                             0.182
% 2.04/0.94  num_of_symbols:                         43
% 2.04/0.94  num_of_terms:                           4589
% 2.04/0.94  
% 2.04/0.94  ------ Preprocessing
% 2.04/0.94  
% 2.04/0.94  num_of_splits:                          0
% 2.04/0.94  num_of_split_atoms:                     0
% 2.04/0.94  num_of_reused_defs:                     0
% 2.04/0.94  num_eq_ax_congr_red:                    16
% 2.04/0.94  num_of_sem_filtered_clauses:            1
% 2.04/0.94  num_of_subtypes:                        0
% 2.04/0.94  monotx_restored_types:                  0
% 2.04/0.94  sat_num_of_epr_types:                   0
% 2.04/0.94  sat_num_of_non_cyclic_types:            0
% 2.04/0.94  sat_guarded_non_collapsed_types:        0
% 2.04/0.94  num_pure_diseq_elim:                    0
% 2.04/0.94  simp_replaced_by:                       0
% 2.04/0.94  res_preprocessed:                       82
% 2.04/0.94  prep_upred:                             0
% 2.04/0.94  prep_unflattend:                        23
% 2.04/0.94  smt_new_axioms:                         0
% 2.04/0.94  pred_elim_cands:                        2
% 2.04/0.94  pred_elim:                              0
% 2.04/0.94  pred_elim_cl:                           0
% 2.04/0.94  pred_elim_cycles:                       1
% 2.04/0.94  merged_defs:                            0
% 2.04/0.94  merged_defs_ncl:                        0
% 2.04/0.94  bin_hyper_res:                          0
% 2.04/0.94  prep_cycles:                            3
% 2.04/0.94  pred_elim_time:                         0.003
% 2.04/0.94  splitting_time:                         0.
% 2.04/0.94  sem_filter_time:                        0.
% 2.04/0.94  monotx_time:                            0.
% 2.04/0.94  subtype_inf_time:                       0.
% 2.04/0.94  
% 2.04/0.94  ------ Problem properties
% 2.04/0.94  
% 2.04/0.94  clauses:                                23
% 2.04/0.94  conjectures:                            4
% 2.04/0.94  epr:                                    1
% 2.04/0.94  horn:                                   17
% 2.04/0.94  ground:                                 4
% 2.04/0.94  unary:                                  5
% 2.04/0.94  binary:                                 10
% 2.04/0.94  lits:                                   50
% 2.04/0.94  lits_eq:                                19
% 2.04/0.94  fd_pure:                                0
% 2.04/0.94  fd_pseudo:                              0
% 2.04/0.94  fd_cond:                                1
% 2.04/0.94  fd_pseudo_cond:                         6
% 2.04/0.94  ac_symbols:                             0
% 2.04/0.94  
% 2.04/0.94  ------ Propositional Solver
% 2.04/0.94  
% 2.04/0.94  prop_solver_calls:                      24
% 2.04/0.94  prop_fast_solver_calls:                 545
% 2.04/0.94  smt_solver_calls:                       0
% 2.04/0.94  smt_fast_solver_calls:                  0
% 2.04/0.94  prop_num_of_clauses:                    2134
% 2.04/0.94  prop_preprocess_simplified:             5720
% 2.04/0.94  prop_fo_subsumed:                       5
% 2.04/0.94  prop_solver_time:                       0.
% 2.04/0.94  smt_solver_time:                        0.
% 2.04/0.94  smt_fast_solver_time:                   0.
% 2.04/0.94  prop_fast_solver_time:                  0.
% 2.04/0.94  prop_unsat_core_time:                   0.
% 2.04/0.94  
% 2.04/0.94  ------ QBF
% 2.04/0.94  
% 2.04/0.94  qbf_q_res:                              0
% 2.04/0.94  qbf_num_tautologies:                    0
% 2.04/0.94  qbf_prep_cycles:                        0
% 2.04/0.94  
% 2.04/0.94  ------ BMC1
% 2.04/0.94  
% 2.04/0.94  bmc1_current_bound:                     -1
% 2.04/0.94  bmc1_last_solved_bound:                 -1
% 2.04/0.94  bmc1_unsat_core_size:                   -1
% 2.04/0.94  bmc1_unsat_core_parents_size:           -1
% 2.04/0.94  bmc1_merge_next_fun:                    0
% 2.04/0.94  bmc1_unsat_core_clauses_time:           0.
% 2.04/0.94  
% 2.04/0.94  ------ Instantiation
% 2.04/0.94  
% 2.04/0.94  inst_num_of_clauses:                    559
% 2.04/0.94  inst_num_in_passive:                    290
% 2.04/0.94  inst_num_in_active:                     222
% 2.04/0.94  inst_num_in_unprocessed:                52
% 2.04/0.94  inst_num_of_loops:                      320
% 2.04/0.94  inst_num_of_learning_restarts:          0
% 2.04/0.94  inst_num_moves_active_passive:          96
% 2.04/0.94  inst_lit_activity:                      0
% 2.04/0.94  inst_lit_activity_moves:                0
% 2.04/0.94  inst_num_tautologies:                   0
% 2.04/0.94  inst_num_prop_implied:                  0
% 2.04/0.94  inst_num_existing_simplified:           0
% 2.04/0.94  inst_num_eq_res_simplified:             0
% 2.04/0.94  inst_num_child_elim:                    0
% 2.04/0.94  inst_num_of_dismatching_blockings:      213
% 2.04/0.94  inst_num_of_non_proper_insts:           612
% 2.04/0.94  inst_num_of_duplicates:                 0
% 2.04/0.94  inst_inst_num_from_inst_to_res:         0
% 2.04/0.94  inst_dismatching_checking_time:         0.
% 2.04/0.94  
% 2.04/0.94  ------ Resolution
% 2.04/0.94  
% 2.04/0.94  res_num_of_clauses:                     0
% 2.04/0.94  res_num_in_passive:                     0
% 2.04/0.94  res_num_in_active:                      0
% 2.04/0.94  res_num_of_loops:                       85
% 2.04/0.94  res_forward_subset_subsumed:            44
% 2.04/0.94  res_backward_subset_subsumed:           18
% 2.04/0.94  res_forward_subsumed:                   0
% 2.04/0.94  res_backward_subsumed:                  0
% 2.04/0.94  res_forward_subsumption_resolution:     0
% 2.04/0.94  res_backward_subsumption_resolution:    0
% 2.04/0.94  res_clause_to_clause_subsumption:       668
% 2.04/0.94  res_orphan_elimination:                 0
% 2.04/0.94  res_tautology_del:                      46
% 2.04/0.94  res_num_eq_res_simplified:              0
% 2.04/0.94  res_num_sel_changes:                    0
% 2.04/0.94  res_moves_from_active_to_pass:          0
% 2.04/0.94  
% 2.04/0.94  ------ Superposition
% 2.04/0.94  
% 2.04/0.94  sup_time_total:                         0.
% 2.04/0.94  sup_time_generating:                    0.
% 2.04/0.94  sup_time_sim_full:                      0.
% 2.04/0.94  sup_time_sim_immed:                     0.
% 2.04/0.94  
% 2.04/0.94  sup_num_of_clauses:                     110
% 2.04/0.94  sup_num_in_active:                      32
% 2.04/0.94  sup_num_in_passive:                     78
% 2.04/0.94  sup_num_of_loops:                       62
% 2.04/0.94  sup_fw_superposition:                   106
% 2.04/0.94  sup_bw_superposition:                   67
% 2.04/0.94  sup_immediate_simplified:               25
% 2.04/0.94  sup_given_eliminated:                   0
% 2.04/0.94  comparisons_done:                       0
% 2.04/0.94  comparisons_avoided:                    2
% 2.04/0.94  
% 2.04/0.94  ------ Simplifications
% 2.04/0.94  
% 2.04/0.94  
% 2.04/0.94  sim_fw_subset_subsumed:                 12
% 2.04/0.94  sim_bw_subset_subsumed:                 10
% 2.04/0.94  sim_fw_subsumed:                        13
% 2.04/0.94  sim_bw_subsumed:                        0
% 2.04/0.94  sim_fw_subsumption_res:                 5
% 2.04/0.94  sim_bw_subsumption_res:                 0
% 2.04/0.94  sim_tautology_del:                      15
% 2.04/0.94  sim_eq_tautology_del:                   7
% 2.04/0.94  sim_eq_res_simp:                        7
% 2.04/0.94  sim_fw_demodulated:                     1
% 2.04/0.94  sim_bw_demodulated:                     24
% 2.04/0.94  sim_light_normalised:                   2
% 2.04/0.94  sim_joinable_taut:                      0
% 2.04/0.94  sim_joinable_simp:                      0
% 2.04/0.94  sim_ac_normalised:                      0
% 2.04/0.94  sim_smt_subsumption:                    0
% 2.04/0.94  
%------------------------------------------------------------------------------
