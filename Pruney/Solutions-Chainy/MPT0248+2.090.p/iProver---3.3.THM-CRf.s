%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:22 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  155 (3372 expanded)
%              Number of clauses        :   70 ( 597 expanded)
%              Number of leaves         :   22 ( 930 expanded)
%              Depth                    :   21
%              Number of atoms          :  430 (8315 expanded)
%              Number of equality atoms :  269 (5992 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f41])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK7
        | k1_tarski(sK5) != sK6 )
      & ( k1_tarski(sK5) != sK7
        | k1_xboole_0 != sK6 )
      & ( k1_tarski(sK5) != sK7
        | k1_tarski(sK5) != sK6 )
      & k2_xboole_0(sK6,sK7) = k1_tarski(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( k1_xboole_0 != sK7
      | k1_tarski(sK5) != sK6 )
    & ( k1_tarski(sK5) != sK7
      | k1_xboole_0 != sK6 )
    & ( k1_tarski(sK5) != sK7
      | k1_tarski(sK5) != sK6 )
    & k2_xboole_0(sK6,sK7) = k1_tarski(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f51])).

fof(f89,plain,(
    k2_xboole_0(sK6,sK7) = k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f88,f93])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f83,f84])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f82,f93])).

fof(f119,plain,(
    k2_enumset1(sK5,sK5,sK5,sK5) = k3_tarski(k2_enumset1(sK6,sK6,sK6,sK7)) ),
    inference(definition_unfolding,[],[f89,f94,f95])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f108,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f75,f94])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f101])).

fof(f10,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f74,f76])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f112,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f78,f95])).

fof(f127,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f112])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f81,f95])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f124,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f80,f95])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f94])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f49])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f85,f95,f95])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f86,f95])).

fof(f129,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f114])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f94])).

fof(f90,plain,
    ( k1_tarski(sK5) != sK7
    | k1_tarski(sK5) != sK6 ),
    inference(cnf_transformation,[],[f52])).

fof(f118,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != sK7
    | k2_enumset1(sK5,sK5,sK5,sK5) != sK6 ),
    inference(definition_unfolding,[],[f90,f95,f95])).

fof(f91,plain,
    ( k1_tarski(sK5) != sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f52])).

fof(f117,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != sK7
    | k1_xboole_0 != sK6 ),
    inference(definition_unfolding,[],[f91,f95])).

fof(f92,plain,
    ( k1_xboole_0 != sK7
    | k1_tarski(sK5) != sK6 ),
    inference(cnf_transformation,[],[f52])).

fof(f116,plain,
    ( k1_xboole_0 != sK7
    | k2_enumset1(sK5,sK5,sK5,sK5) != sK6 ),
    inference(definition_unfolding,[],[f92,f95])).

cnf(c_15,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1348,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_34,negated_conjecture,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k3_tarski(k2_enumset1(sK6,sK6,sK6,sK7)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_22,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1780,plain,
    ( k4_xboole_0(sK6,k2_enumset1(sK5,sK5,sK5,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34,c_22])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1355,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3595,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
    | r2_hidden(X0,k4_xboole_0(sK6,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1355])).

cnf(c_21,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1794,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_21,c_0])).

cnf(c_23,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1803,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1794,c_23])).

cnf(c_3599,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3595,c_1803])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1340,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3736,plain,
    ( sK5 = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3599,c_1340])).

cnf(c_6868,plain,
    ( sK3(sK6) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1348,c_3736])).

cnf(c_8713,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6868,c_1348])).

cnf(c_24,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | k2_enumset1(X0,X0,X0,X0) = X1
    | sK4(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1613,plain,
    ( ~ r2_hidden(sK4(sK5,sK6),sK6)
    | k2_enumset1(sK5,sK5,sK5,sK5) = sK6
    | sK4(sK5,sK6) != sK5 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1614,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = sK6
    | sK4(sK5,sK6) != sK5
    | r2_hidden(sK4(sK5,sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1613])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2361,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3887,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_18,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_3888,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_25,plain,
    ( r2_hidden(sK4(X0,X1),X1)
    | k2_enumset1(X0,X0,X0,X0) = X1
    | sK4(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1342,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK4(X0,X1) = X0
    | r2_hidden(sK4(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6869,plain,
    ( k2_enumset1(X0,X0,X0,X0) = sK6
    | sK4(X0,sK6) = X0
    | sK4(X0,sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_1342,c_3736])).

cnf(c_6935,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = sK6
    | sK4(sK5,sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_6869])).

cnf(c_759,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2887,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4(sK5,sK6),sK6)
    | sK4(sK5,sK6) != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_8658,plain,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(sK4(sK5,sK6),sK6)
    | sK4(sK5,sK6) != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2887])).

cnf(c_8660,plain,
    ( sK4(sK5,sK6) != X0
    | sK6 != sK6
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK4(sK5,sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8658])).

cnf(c_8662,plain,
    ( sK4(sK5,sK6) != sK5
    | sK6 != sK6
    | r2_hidden(sK4(sK5,sK6),sK6) = iProver_top
    | r2_hidden(sK5,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8660])).

cnf(c_1346,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1345,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3644,plain,
    ( r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
    | r1_tarski(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_34,c_1345])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1337,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3699,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_1337])).

cnf(c_3731,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = sK7
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1346,c_3699])).

cnf(c_29,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1338,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3814,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3731,c_1338])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1344,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3698,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK5,sK5,sK5,sK5)
    | r1_tarski(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_1344])).

cnf(c_6844,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK5,sK5,sK5,sK5)
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3814,c_3698])).

cnf(c_2774,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_1338,c_1344])).

cnf(c_2780,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2774])).

cnf(c_7853,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6844,c_2780])).

cnf(c_7861,plain,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(sK5,sK5,sK5,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7853,c_22])).

cnf(c_8566,plain,
    ( k4_xboole_0(k1_xboole_0,sK7) = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3731,c_7861])).

cnf(c_33,negated_conjecture,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != sK6
    | k2_enumset1(sK5,sK5,sK5,sK5) != sK7 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_32,negated_conjecture,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3821,plain,
    ( sK6 != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3731,c_32])).

cnf(c_8715,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8566,c_33,c_1614,c_3731,c_3821,c_3887,c_3888,c_6935,c_8662,c_8713])).

cnf(c_31,negated_conjecture,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != sK6
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_8740,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8715,c_31])).

cnf(c_8744,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_8740])).

cnf(c_9694,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8713,c_1614,c_3887,c_3888,c_6935,c_8662,c_8744])).

cnf(c_8741,plain,
    ( k3_tarski(k2_enumset1(sK6,sK6,sK6,k1_xboole_0)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(demodulation,[status(thm)],[c_8715,c_34])).

cnf(c_9698,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(demodulation,[status(thm)],[c_9694,c_8741])).

cnf(c_2773,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1346,c_1344])).

cnf(c_9741,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9698,c_2773])).

cnf(c_8739,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != k1_xboole_0
    | sK6 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8715,c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9741,c_8744,c_8739,c_8713,c_8662,c_6935,c_3888,c_3887,c_1614])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:02:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.63/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/0.98  
% 3.63/0.98  ------  iProver source info
% 3.63/0.98  
% 3.63/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.63/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/0.98  git: non_committed_changes: false
% 3.63/0.98  git: last_make_outside_of_git: false
% 3.63/0.98  
% 3.63/0.98  ------ 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options
% 3.63/0.98  
% 3.63/0.98  --out_options                           all
% 3.63/0.98  --tptp_safe_out                         true
% 3.63/0.98  --problem_path                          ""
% 3.63/0.98  --include_path                          ""
% 3.63/0.98  --clausifier                            res/vclausify_rel
% 3.63/0.98  --clausifier_options                    --mode clausify
% 3.63/0.98  --stdin                                 false
% 3.63/0.98  --stats_out                             all
% 3.63/0.98  
% 3.63/0.98  ------ General Options
% 3.63/0.98  
% 3.63/0.98  --fof                                   false
% 3.63/0.98  --time_out_real                         305.
% 3.63/0.98  --time_out_virtual                      -1.
% 3.63/0.98  --symbol_type_check                     false
% 3.63/0.98  --clausify_out                          false
% 3.63/0.98  --sig_cnt_out                           false
% 3.63/0.98  --trig_cnt_out                          false
% 3.63/0.98  --trig_cnt_out_tolerance                1.
% 3.63/0.98  --trig_cnt_out_sk_spl                   false
% 3.63/0.98  --abstr_cl_out                          false
% 3.63/0.98  
% 3.63/0.98  ------ Global Options
% 3.63/0.98  
% 3.63/0.98  --schedule                              default
% 3.63/0.98  --add_important_lit                     false
% 3.63/0.98  --prop_solver_per_cl                    1000
% 3.63/0.98  --min_unsat_core                        false
% 3.63/0.98  --soft_assumptions                      false
% 3.63/0.98  --soft_lemma_size                       3
% 3.63/0.98  --prop_impl_unit_size                   0
% 3.63/0.98  --prop_impl_unit                        []
% 3.63/0.98  --share_sel_clauses                     true
% 3.63/0.98  --reset_solvers                         false
% 3.63/0.98  --bc_imp_inh                            [conj_cone]
% 3.63/0.98  --conj_cone_tolerance                   3.
% 3.63/0.98  --extra_neg_conj                        none
% 3.63/0.98  --large_theory_mode                     true
% 3.63/0.98  --prolific_symb_bound                   200
% 3.63/0.98  --lt_threshold                          2000
% 3.63/0.98  --clause_weak_htbl                      true
% 3.63/0.98  --gc_record_bc_elim                     false
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing Options
% 3.63/0.98  
% 3.63/0.98  --preprocessing_flag                    true
% 3.63/0.98  --time_out_prep_mult                    0.1
% 3.63/0.98  --splitting_mode                        input
% 3.63/0.98  --splitting_grd                         true
% 3.63/0.98  --splitting_cvd                         false
% 3.63/0.98  --splitting_cvd_svl                     false
% 3.63/0.98  --splitting_nvd                         32
% 3.63/0.98  --sub_typing                            true
% 3.63/0.98  --prep_gs_sim                           true
% 3.63/0.98  --prep_unflatten                        true
% 3.63/0.98  --prep_res_sim                          true
% 3.63/0.98  --prep_upred                            true
% 3.63/0.98  --prep_sem_filter                       exhaustive
% 3.63/0.98  --prep_sem_filter_out                   false
% 3.63/0.98  --pred_elim                             true
% 3.63/0.98  --res_sim_input                         true
% 3.63/0.98  --eq_ax_congr_red                       true
% 3.63/0.98  --pure_diseq_elim                       true
% 3.63/0.98  --brand_transform                       false
% 3.63/0.98  --non_eq_to_eq                          false
% 3.63/0.98  --prep_def_merge                        true
% 3.63/0.98  --prep_def_merge_prop_impl              false
% 3.63/0.98  --prep_def_merge_mbd                    true
% 3.63/0.98  --prep_def_merge_tr_red                 false
% 3.63/0.98  --prep_def_merge_tr_cl                  false
% 3.63/0.98  --smt_preprocessing                     true
% 3.63/0.98  --smt_ac_axioms                         fast
% 3.63/0.98  --preprocessed_out                      false
% 3.63/0.98  --preprocessed_stats                    false
% 3.63/0.98  
% 3.63/0.98  ------ Abstraction refinement Options
% 3.63/0.98  
% 3.63/0.98  --abstr_ref                             []
% 3.63/0.98  --abstr_ref_prep                        false
% 3.63/0.98  --abstr_ref_until_sat                   false
% 3.63/0.98  --abstr_ref_sig_restrict                funpre
% 3.63/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.98  --abstr_ref_under                       []
% 3.63/0.98  
% 3.63/0.98  ------ SAT Options
% 3.63/0.98  
% 3.63/0.98  --sat_mode                              false
% 3.63/0.98  --sat_fm_restart_options                ""
% 3.63/0.98  --sat_gr_def                            false
% 3.63/0.98  --sat_epr_types                         true
% 3.63/0.98  --sat_non_cyclic_types                  false
% 3.63/0.98  --sat_finite_models                     false
% 3.63/0.98  --sat_fm_lemmas                         false
% 3.63/0.98  --sat_fm_prep                           false
% 3.63/0.98  --sat_fm_uc_incr                        true
% 3.63/0.98  --sat_out_model                         small
% 3.63/0.98  --sat_out_clauses                       false
% 3.63/0.98  
% 3.63/0.98  ------ QBF Options
% 3.63/0.98  
% 3.63/0.98  --qbf_mode                              false
% 3.63/0.98  --qbf_elim_univ                         false
% 3.63/0.98  --qbf_dom_inst                          none
% 3.63/0.98  --qbf_dom_pre_inst                      false
% 3.63/0.98  --qbf_sk_in                             false
% 3.63/0.98  --qbf_pred_elim                         true
% 3.63/0.98  --qbf_split                             512
% 3.63/0.98  
% 3.63/0.98  ------ BMC1 Options
% 3.63/0.98  
% 3.63/0.98  --bmc1_incremental                      false
% 3.63/0.98  --bmc1_axioms                           reachable_all
% 3.63/0.98  --bmc1_min_bound                        0
% 3.63/0.98  --bmc1_max_bound                        -1
% 3.63/0.98  --bmc1_max_bound_default                -1
% 3.63/0.98  --bmc1_symbol_reachability              true
% 3.63/0.98  --bmc1_property_lemmas                  false
% 3.63/0.98  --bmc1_k_induction                      false
% 3.63/0.98  --bmc1_non_equiv_states                 false
% 3.63/0.98  --bmc1_deadlock                         false
% 3.63/0.98  --bmc1_ucm                              false
% 3.63/0.98  --bmc1_add_unsat_core                   none
% 3.63/0.98  --bmc1_unsat_core_children              false
% 3.63/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.98  --bmc1_out_stat                         full
% 3.63/0.98  --bmc1_ground_init                      false
% 3.63/0.98  --bmc1_pre_inst_next_state              false
% 3.63/0.98  --bmc1_pre_inst_state                   false
% 3.63/0.98  --bmc1_pre_inst_reach_state             false
% 3.63/0.98  --bmc1_out_unsat_core                   false
% 3.63/0.98  --bmc1_aig_witness_out                  false
% 3.63/0.98  --bmc1_verbose                          false
% 3.63/0.98  --bmc1_dump_clauses_tptp                false
% 3.63/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.98  --bmc1_dump_file                        -
% 3.63/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.98  --bmc1_ucm_extend_mode                  1
% 3.63/0.98  --bmc1_ucm_init_mode                    2
% 3.63/0.98  --bmc1_ucm_cone_mode                    none
% 3.63/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.98  --bmc1_ucm_relax_model                  4
% 3.63/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.98  --bmc1_ucm_layered_model                none
% 3.63/0.98  --bmc1_ucm_max_lemma_size               10
% 3.63/0.98  
% 3.63/0.98  ------ AIG Options
% 3.63/0.98  
% 3.63/0.98  --aig_mode                              false
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation Options
% 3.63/0.98  
% 3.63/0.98  --instantiation_flag                    true
% 3.63/0.98  --inst_sos_flag                         false
% 3.63/0.98  --inst_sos_phase                        true
% 3.63/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel_side                     num_symb
% 3.63/0.98  --inst_solver_per_active                1400
% 3.63/0.98  --inst_solver_calls_frac                1.
% 3.63/0.98  --inst_passive_queue_type               priority_queues
% 3.63/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.98  --inst_passive_queues_freq              [25;2]
% 3.63/0.98  --inst_dismatching                      true
% 3.63/0.98  --inst_eager_unprocessed_to_passive     true
% 3.63/0.98  --inst_prop_sim_given                   true
% 3.63/0.98  --inst_prop_sim_new                     false
% 3.63/0.98  --inst_subs_new                         false
% 3.63/0.98  --inst_eq_res_simp                      false
% 3.63/0.98  --inst_subs_given                       false
% 3.63/0.98  --inst_orphan_elimination               true
% 3.63/0.98  --inst_learning_loop_flag               true
% 3.63/0.98  --inst_learning_start                   3000
% 3.63/0.98  --inst_learning_factor                  2
% 3.63/0.98  --inst_start_prop_sim_after_learn       3
% 3.63/0.98  --inst_sel_renew                        solver
% 3.63/0.98  --inst_lit_activity_flag                true
% 3.63/0.98  --inst_restr_to_given                   false
% 3.63/0.98  --inst_activity_threshold               500
% 3.63/0.98  --inst_out_proof                        true
% 3.63/0.98  
% 3.63/0.98  ------ Resolution Options
% 3.63/0.98  
% 3.63/0.98  --resolution_flag                       true
% 3.63/0.98  --res_lit_sel                           adaptive
% 3.63/0.98  --res_lit_sel_side                      none
% 3.63/0.98  --res_ordering                          kbo
% 3.63/0.98  --res_to_prop_solver                    active
% 3.63/0.98  --res_prop_simpl_new                    false
% 3.63/0.98  --res_prop_simpl_given                  true
% 3.63/0.98  --res_passive_queue_type                priority_queues
% 3.63/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.98  --res_passive_queues_freq               [15;5]
% 3.63/0.98  --res_forward_subs                      full
% 3.63/0.98  --res_backward_subs                     full
% 3.63/0.98  --res_forward_subs_resolution           true
% 3.63/0.98  --res_backward_subs_resolution          true
% 3.63/0.98  --res_orphan_elimination                true
% 3.63/0.98  --res_time_limit                        2.
% 3.63/0.98  --res_out_proof                         true
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Options
% 3.63/0.98  
% 3.63/0.98  --superposition_flag                    true
% 3.63/0.98  --sup_passive_queue_type                priority_queues
% 3.63/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.98  --demod_completeness_check              fast
% 3.63/0.98  --demod_use_ground                      true
% 3.63/0.98  --sup_to_prop_solver                    passive
% 3.63/0.98  --sup_prop_simpl_new                    true
% 3.63/0.98  --sup_prop_simpl_given                  true
% 3.63/0.98  --sup_fun_splitting                     false
% 3.63/0.98  --sup_smt_interval                      50000
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Simplification Setup
% 3.63/0.98  
% 3.63/0.98  --sup_indices_passive                   []
% 3.63/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_full_bw                           [BwDemod]
% 3.63/0.98  --sup_immed_triv                        [TrivRules]
% 3.63/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_immed_bw_main                     []
% 3.63/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  
% 3.63/0.98  ------ Combination Options
% 3.63/0.98  
% 3.63/0.98  --comb_res_mult                         3
% 3.63/0.98  --comb_sup_mult                         2
% 3.63/0.98  --comb_inst_mult                        10
% 3.63/0.98  
% 3.63/0.98  ------ Debug Options
% 3.63/0.98  
% 3.63/0.98  --dbg_backtrace                         false
% 3.63/0.98  --dbg_dump_prop_clauses                 false
% 3.63/0.98  --dbg_dump_prop_clauses_file            -
% 3.63/0.98  --dbg_out_stat                          false
% 3.63/0.98  ------ Parsing...
% 3.63/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.98  ------ Proving...
% 3.63/0.98  ------ Problem Properties 
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  clauses                                 34
% 3.63/0.98  conjectures                             4
% 3.63/0.98  EPR                                     4
% 3.63/0.98  Horn                                    26
% 3.63/0.98  unary                                   9
% 3.63/0.98  binary                                  15
% 3.63/0.98  lits                                    70
% 3.63/0.98  lits eq                                 26
% 3.63/0.98  fd_pure                                 0
% 3.63/0.98  fd_pseudo                               0
% 3.63/0.98  fd_cond                                 1
% 3.63/0.98  fd_pseudo_cond                          7
% 3.63/0.98  AC symbols                              0
% 3.63/0.98  
% 3.63/0.98  ------ Schedule dynamic 5 is on 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  ------ 
% 3.63/0.98  Current options:
% 3.63/0.98  ------ 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options
% 3.63/0.98  
% 3.63/0.98  --out_options                           all
% 3.63/0.98  --tptp_safe_out                         true
% 3.63/0.98  --problem_path                          ""
% 3.63/0.98  --include_path                          ""
% 3.63/0.98  --clausifier                            res/vclausify_rel
% 3.63/0.98  --clausifier_options                    --mode clausify
% 3.63/0.98  --stdin                                 false
% 3.63/0.98  --stats_out                             all
% 3.63/0.98  
% 3.63/0.98  ------ General Options
% 3.63/0.98  
% 3.63/0.98  --fof                                   false
% 3.63/0.98  --time_out_real                         305.
% 3.63/0.98  --time_out_virtual                      -1.
% 3.63/0.98  --symbol_type_check                     false
% 3.63/0.98  --clausify_out                          false
% 3.63/0.98  --sig_cnt_out                           false
% 3.63/0.98  --trig_cnt_out                          false
% 3.63/0.98  --trig_cnt_out_tolerance                1.
% 3.63/0.98  --trig_cnt_out_sk_spl                   false
% 3.63/0.98  --abstr_cl_out                          false
% 3.63/0.98  
% 3.63/0.98  ------ Global Options
% 3.63/0.98  
% 3.63/0.98  --schedule                              default
% 3.63/0.98  --add_important_lit                     false
% 3.63/0.98  --prop_solver_per_cl                    1000
% 3.63/0.98  --min_unsat_core                        false
% 3.63/0.98  --soft_assumptions                      false
% 3.63/0.98  --soft_lemma_size                       3
% 3.63/0.98  --prop_impl_unit_size                   0
% 3.63/0.98  --prop_impl_unit                        []
% 3.63/0.98  --share_sel_clauses                     true
% 3.63/0.98  --reset_solvers                         false
% 3.63/0.98  --bc_imp_inh                            [conj_cone]
% 3.63/0.98  --conj_cone_tolerance                   3.
% 3.63/0.98  --extra_neg_conj                        none
% 3.63/0.98  --large_theory_mode                     true
% 3.63/0.98  --prolific_symb_bound                   200
% 3.63/0.98  --lt_threshold                          2000
% 3.63/0.98  --clause_weak_htbl                      true
% 3.63/0.98  --gc_record_bc_elim                     false
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing Options
% 3.63/0.98  
% 3.63/0.98  --preprocessing_flag                    true
% 3.63/0.98  --time_out_prep_mult                    0.1
% 3.63/0.98  --splitting_mode                        input
% 3.63/0.98  --splitting_grd                         true
% 3.63/0.98  --splitting_cvd                         false
% 3.63/0.98  --splitting_cvd_svl                     false
% 3.63/0.98  --splitting_nvd                         32
% 3.63/0.98  --sub_typing                            true
% 3.63/0.98  --prep_gs_sim                           true
% 3.63/0.98  --prep_unflatten                        true
% 3.63/0.98  --prep_res_sim                          true
% 3.63/0.98  --prep_upred                            true
% 3.63/0.98  --prep_sem_filter                       exhaustive
% 3.63/0.98  --prep_sem_filter_out                   false
% 3.63/0.98  --pred_elim                             true
% 3.63/0.98  --res_sim_input                         true
% 3.63/0.98  --eq_ax_congr_red                       true
% 3.63/0.98  --pure_diseq_elim                       true
% 3.63/0.98  --brand_transform                       false
% 3.63/0.98  --non_eq_to_eq                          false
% 3.63/0.98  --prep_def_merge                        true
% 3.63/0.98  --prep_def_merge_prop_impl              false
% 3.63/0.98  --prep_def_merge_mbd                    true
% 3.63/0.98  --prep_def_merge_tr_red                 false
% 3.63/0.98  --prep_def_merge_tr_cl                  false
% 3.63/0.98  --smt_preprocessing                     true
% 3.63/0.98  --smt_ac_axioms                         fast
% 3.63/0.98  --preprocessed_out                      false
% 3.63/0.98  --preprocessed_stats                    false
% 3.63/0.98  
% 3.63/0.98  ------ Abstraction refinement Options
% 3.63/0.98  
% 3.63/0.98  --abstr_ref                             []
% 3.63/0.98  --abstr_ref_prep                        false
% 3.63/0.98  --abstr_ref_until_sat                   false
% 3.63/0.98  --abstr_ref_sig_restrict                funpre
% 3.63/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.98  --abstr_ref_under                       []
% 3.63/0.98  
% 3.63/0.98  ------ SAT Options
% 3.63/0.98  
% 3.63/0.98  --sat_mode                              false
% 3.63/0.98  --sat_fm_restart_options                ""
% 3.63/0.98  --sat_gr_def                            false
% 3.63/0.98  --sat_epr_types                         true
% 3.63/0.98  --sat_non_cyclic_types                  false
% 3.63/0.98  --sat_finite_models                     false
% 3.63/0.98  --sat_fm_lemmas                         false
% 3.63/0.98  --sat_fm_prep                           false
% 3.63/0.98  --sat_fm_uc_incr                        true
% 3.63/0.98  --sat_out_model                         small
% 3.63/0.98  --sat_out_clauses                       false
% 3.63/0.98  
% 3.63/0.98  ------ QBF Options
% 3.63/0.98  
% 3.63/0.98  --qbf_mode                              false
% 3.63/0.98  --qbf_elim_univ                         false
% 3.63/0.98  --qbf_dom_inst                          none
% 3.63/0.98  --qbf_dom_pre_inst                      false
% 3.63/0.98  --qbf_sk_in                             false
% 3.63/0.98  --qbf_pred_elim                         true
% 3.63/0.98  --qbf_split                             512
% 3.63/0.98  
% 3.63/0.98  ------ BMC1 Options
% 3.63/0.98  
% 3.63/0.98  --bmc1_incremental                      false
% 3.63/0.98  --bmc1_axioms                           reachable_all
% 3.63/0.98  --bmc1_min_bound                        0
% 3.63/0.98  --bmc1_max_bound                        -1
% 3.63/0.98  --bmc1_max_bound_default                -1
% 3.63/0.98  --bmc1_symbol_reachability              true
% 3.63/0.98  --bmc1_property_lemmas                  false
% 3.63/0.98  --bmc1_k_induction                      false
% 3.63/0.98  --bmc1_non_equiv_states                 false
% 3.63/0.98  --bmc1_deadlock                         false
% 3.63/0.98  --bmc1_ucm                              false
% 3.63/0.98  --bmc1_add_unsat_core                   none
% 3.63/0.98  --bmc1_unsat_core_children              false
% 3.63/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.98  --bmc1_out_stat                         full
% 3.63/0.98  --bmc1_ground_init                      false
% 3.63/0.98  --bmc1_pre_inst_next_state              false
% 3.63/0.98  --bmc1_pre_inst_state                   false
% 3.63/0.98  --bmc1_pre_inst_reach_state             false
% 3.63/0.98  --bmc1_out_unsat_core                   false
% 3.63/0.98  --bmc1_aig_witness_out                  false
% 3.63/0.98  --bmc1_verbose                          false
% 3.63/0.98  --bmc1_dump_clauses_tptp                false
% 3.63/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.98  --bmc1_dump_file                        -
% 3.63/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.98  --bmc1_ucm_extend_mode                  1
% 3.63/0.98  --bmc1_ucm_init_mode                    2
% 3.63/0.98  --bmc1_ucm_cone_mode                    none
% 3.63/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.98  --bmc1_ucm_relax_model                  4
% 3.63/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.98  --bmc1_ucm_layered_model                none
% 3.63/0.98  --bmc1_ucm_max_lemma_size               10
% 3.63/0.98  
% 3.63/0.98  ------ AIG Options
% 3.63/0.98  
% 3.63/0.98  --aig_mode                              false
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation Options
% 3.63/0.98  
% 3.63/0.98  --instantiation_flag                    true
% 3.63/0.98  --inst_sos_flag                         false
% 3.63/0.98  --inst_sos_phase                        true
% 3.63/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel_side                     none
% 3.63/0.98  --inst_solver_per_active                1400
% 3.63/0.98  --inst_solver_calls_frac                1.
% 3.63/0.98  --inst_passive_queue_type               priority_queues
% 3.63/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.98  --inst_passive_queues_freq              [25;2]
% 3.63/0.98  --inst_dismatching                      true
% 3.63/0.98  --inst_eager_unprocessed_to_passive     true
% 3.63/0.98  --inst_prop_sim_given                   true
% 3.63/0.98  --inst_prop_sim_new                     false
% 3.63/0.98  --inst_subs_new                         false
% 3.63/0.98  --inst_eq_res_simp                      false
% 3.63/0.98  --inst_subs_given                       false
% 3.63/0.98  --inst_orphan_elimination               true
% 3.63/0.98  --inst_learning_loop_flag               true
% 3.63/0.98  --inst_learning_start                   3000
% 3.63/0.98  --inst_learning_factor                  2
% 3.63/0.98  --inst_start_prop_sim_after_learn       3
% 3.63/0.98  --inst_sel_renew                        solver
% 3.63/0.98  --inst_lit_activity_flag                true
% 3.63/0.98  --inst_restr_to_given                   false
% 3.63/0.98  --inst_activity_threshold               500
% 3.63/0.98  --inst_out_proof                        true
% 3.63/0.98  
% 3.63/0.98  ------ Resolution Options
% 3.63/0.98  
% 3.63/0.98  --resolution_flag                       false
% 3.63/0.98  --res_lit_sel                           adaptive
% 3.63/0.98  --res_lit_sel_side                      none
% 3.63/0.98  --res_ordering                          kbo
% 3.63/0.98  --res_to_prop_solver                    active
% 3.63/0.98  --res_prop_simpl_new                    false
% 3.63/0.98  --res_prop_simpl_given                  true
% 3.63/0.98  --res_passive_queue_type                priority_queues
% 3.63/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.98  --res_passive_queues_freq               [15;5]
% 3.63/0.98  --res_forward_subs                      full
% 3.63/0.98  --res_backward_subs                     full
% 3.63/0.98  --res_forward_subs_resolution           true
% 3.63/0.98  --res_backward_subs_resolution          true
% 3.63/0.98  --res_orphan_elimination                true
% 3.63/0.98  --res_time_limit                        2.
% 3.63/0.98  --res_out_proof                         true
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Options
% 3.63/0.98  
% 3.63/0.98  --superposition_flag                    true
% 3.63/0.98  --sup_passive_queue_type                priority_queues
% 3.63/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.98  --demod_completeness_check              fast
% 3.63/0.98  --demod_use_ground                      true
% 3.63/0.98  --sup_to_prop_solver                    passive
% 3.63/0.98  --sup_prop_simpl_new                    true
% 3.63/0.98  --sup_prop_simpl_given                  true
% 3.63/0.98  --sup_fun_splitting                     false
% 3.63/0.98  --sup_smt_interval                      50000
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Simplification Setup
% 3.63/0.98  
% 3.63/0.98  --sup_indices_passive                   []
% 3.63/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_full_bw                           [BwDemod]
% 3.63/0.98  --sup_immed_triv                        [TrivRules]
% 3.63/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_immed_bw_main                     []
% 3.63/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  
% 3.63/0.98  ------ Combination Options
% 3.63/0.98  
% 3.63/0.98  --comb_res_mult                         3
% 3.63/0.98  --comb_sup_mult                         2
% 3.63/0.98  --comb_inst_mult                        10
% 3.63/0.98  
% 3.63/0.98  ------ Debug Options
% 3.63/0.98  
% 3.63/0.98  --dbg_backtrace                         false
% 3.63/0.98  --dbg_dump_prop_clauses                 false
% 3.63/0.98  --dbg_dump_prop_clauses_file            -
% 3.63/0.98  --dbg_out_stat                          false
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  ------ Proving...
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  % SZS status Theorem for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  fof(f5,axiom,(
% 3.63/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f25,plain,(
% 3.63/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.63/0.98    inference(ennf_transformation,[],[f5])).
% 3.63/0.98  
% 3.63/0.98  fof(f41,plain,(
% 3.63/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f42,plain,(
% 3.63/0.98    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f41])).
% 3.63/0.98  
% 3.63/0.98  fof(f67,plain,(
% 3.63/0.98    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 3.63/0.98    inference(cnf_transformation,[],[f42])).
% 3.63/0.98  
% 3.63/0.98  fof(f20,conjecture,(
% 3.63/0.98    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f21,negated_conjecture,(
% 3.63/0.98    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.63/0.98    inference(negated_conjecture,[],[f20])).
% 3.63/0.98  
% 3.63/0.98  fof(f28,plain,(
% 3.63/0.98    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.63/0.98    inference(ennf_transformation,[],[f21])).
% 3.63/0.98  
% 3.63/0.98  fof(f51,plain,(
% 3.63/0.98    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK7 | k1_tarski(sK5) != sK6) & (k1_tarski(sK5) != sK7 | k1_xboole_0 != sK6) & (k1_tarski(sK5) != sK7 | k1_tarski(sK5) != sK6) & k2_xboole_0(sK6,sK7) = k1_tarski(sK5))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f52,plain,(
% 3.63/0.98    (k1_xboole_0 != sK7 | k1_tarski(sK5) != sK6) & (k1_tarski(sK5) != sK7 | k1_xboole_0 != sK6) & (k1_tarski(sK5) != sK7 | k1_tarski(sK5) != sK6) & k2_xboole_0(sK6,sK7) = k1_tarski(sK5)),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f51])).
% 3.63/0.98  
% 3.63/0.98  fof(f89,plain,(
% 3.63/0.98    k2_xboole_0(sK6,sK7) = k1_tarski(sK5)),
% 3.63/0.98    inference(cnf_transformation,[],[f52])).
% 3.63/0.98  
% 3.63/0.98  fof(f19,axiom,(
% 3.63/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f88,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f19])).
% 3.63/0.98  
% 3.63/0.98  fof(f94,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.63/0.98    inference(definition_unfolding,[],[f88,f93])).
% 3.63/0.98  
% 3.63/0.98  fof(f15,axiom,(
% 3.63/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f82,plain,(
% 3.63/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f15])).
% 3.63/0.98  
% 3.63/0.98  fof(f16,axiom,(
% 3.63/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f83,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f16])).
% 3.63/0.98  
% 3.63/0.98  fof(f17,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f84,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f17])).
% 3.63/0.98  
% 3.63/0.98  fof(f93,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.63/0.98    inference(definition_unfolding,[],[f83,f84])).
% 3.63/0.98  
% 3.63/0.98  fof(f95,plain,(
% 3.63/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.63/0.98    inference(definition_unfolding,[],[f82,f93])).
% 3.63/0.98  
% 3.63/0.98  fof(f119,plain,(
% 3.63/0.98    k2_enumset1(sK5,sK5,sK5,sK5) = k3_tarski(k2_enumset1(sK6,sK6,sK6,sK7))),
% 3.63/0.98    inference(definition_unfolding,[],[f89,f94,f95])).
% 3.63/0.98  
% 3.63/0.98  fof(f11,axiom,(
% 3.63/0.98    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f75,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f11])).
% 3.63/0.98  
% 3.63/0.98  fof(f108,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.63/0.98    inference(definition_unfolding,[],[f75,f94])).
% 3.63/0.98  
% 3.63/0.98  fof(f2,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f33,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.63/0.98    inference(nnf_transformation,[],[f2])).
% 3.63/0.98  
% 3.63/0.98  fof(f34,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.63/0.98    inference(flattening,[],[f33])).
% 3.63/0.98  
% 3.63/0.98  fof(f35,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.63/0.98    inference(rectify,[],[f34])).
% 3.63/0.98  
% 3.63/0.98  fof(f36,plain,(
% 3.63/0.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f37,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.63/0.98  
% 3.63/0.98  fof(f57,plain,(
% 3.63/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.63/0.98    inference(cnf_transformation,[],[f37])).
% 3.63/0.98  
% 3.63/0.98  fof(f12,axiom,(
% 3.63/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f76,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f12])).
% 3.63/0.98  
% 3.63/0.98  fof(f101,plain,(
% 3.63/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 3.63/0.98    inference(definition_unfolding,[],[f57,f76])).
% 3.63/0.98  
% 3.63/0.98  fof(f121,plain,(
% 3.63/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.63/0.98    inference(equality_resolution,[],[f101])).
% 3.63/0.98  
% 3.63/0.98  fof(f10,axiom,(
% 3.63/0.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f74,plain,(
% 3.63/0.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.63/0.98    inference(cnf_transformation,[],[f10])).
% 3.63/0.98  
% 3.63/0.98  fof(f107,plain,(
% 3.63/0.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.63/0.98    inference(definition_unfolding,[],[f74,f76])).
% 3.63/0.98  
% 3.63/0.98  fof(f7,axiom,(
% 3.63/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f71,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f7])).
% 3.63/0.98  
% 3.63/0.98  fof(f96,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.63/0.98    inference(definition_unfolding,[],[f71,f76])).
% 3.63/0.98  
% 3.63/0.98  fof(f13,axiom,(
% 3.63/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f77,plain,(
% 3.63/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.63/0.98    inference(cnf_transformation,[],[f13])).
% 3.63/0.98  
% 3.63/0.98  fof(f14,axiom,(
% 3.63/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f45,plain,(
% 3.63/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.63/0.98    inference(nnf_transformation,[],[f14])).
% 3.63/0.98  
% 3.63/0.98  fof(f46,plain,(
% 3.63/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.63/0.98    inference(rectify,[],[f45])).
% 3.63/0.98  
% 3.63/0.98  fof(f47,plain,(
% 3.63/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f48,plain,(
% 3.63/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 3.63/0.98  
% 3.63/0.98  fof(f78,plain,(
% 3.63/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.63/0.98    inference(cnf_transformation,[],[f48])).
% 3.63/0.98  
% 3.63/0.98  fof(f112,plain,(
% 3.63/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.63/0.98    inference(definition_unfolding,[],[f78,f95])).
% 3.63/0.98  
% 3.63/0.98  fof(f127,plain,(
% 3.63/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.63/0.98    inference(equality_resolution,[],[f112])).
% 3.63/0.98  
% 3.63/0.98  fof(f81,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f48])).
% 3.63/0.98  
% 3.63/0.98  fof(f109,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) )),
% 3.63/0.98    inference(definition_unfolding,[],[f81,f95])).
% 3.63/0.98  
% 3.63/0.98  fof(f6,axiom,(
% 3.63/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f43,plain,(
% 3.63/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.63/0.98    inference(nnf_transformation,[],[f6])).
% 3.63/0.98  
% 3.63/0.98  fof(f44,plain,(
% 3.63/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.63/0.98    inference(flattening,[],[f43])).
% 3.63/0.98  
% 3.63/0.98  fof(f70,plain,(
% 3.63/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f44])).
% 3.63/0.98  
% 3.63/0.98  fof(f68,plain,(
% 3.63/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.63/0.98    inference(cnf_transformation,[],[f44])).
% 3.63/0.98  
% 3.63/0.98  fof(f124,plain,(
% 3.63/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.63/0.98    inference(equality_resolution,[],[f68])).
% 3.63/0.98  
% 3.63/0.98  fof(f80,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f48])).
% 3.63/0.98  
% 3.63/0.98  fof(f110,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)) )),
% 3.63/0.98    inference(definition_unfolding,[],[f80,f95])).
% 3.63/0.98  
% 3.63/0.98  fof(f8,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f26,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.63/0.98    inference(ennf_transformation,[],[f8])).
% 3.63/0.98  
% 3.63/0.98  fof(f72,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f26])).
% 3.63/0.98  
% 3.63/0.98  fof(f105,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.63/0.98    inference(definition_unfolding,[],[f72,f94])).
% 3.63/0.98  
% 3.63/0.98  fof(f18,axiom,(
% 3.63/0.98    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f49,plain,(
% 3.63/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.63/0.98    inference(nnf_transformation,[],[f18])).
% 3.63/0.98  
% 3.63/0.98  fof(f50,plain,(
% 3.63/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.63/0.98    inference(flattening,[],[f49])).
% 3.63/0.98  
% 3.63/0.98  fof(f85,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f50])).
% 3.63/0.98  
% 3.63/0.98  fof(f115,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.63/0.98    inference(definition_unfolding,[],[f85,f95,f95])).
% 3.63/0.98  
% 3.63/0.98  fof(f86,plain,(
% 3.63/0.98    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 3.63/0.98    inference(cnf_transformation,[],[f50])).
% 3.63/0.98  
% 3.63/0.98  fof(f114,plain,(
% 3.63/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 3.63/0.98    inference(definition_unfolding,[],[f86,f95])).
% 3.63/0.98  
% 3.63/0.98  fof(f129,plain,(
% 3.63/0.98    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.63/0.98    inference(equality_resolution,[],[f114])).
% 3.63/0.98  
% 3.63/0.98  fof(f9,axiom,(
% 3.63/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f27,plain,(
% 3.63/0.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.63/0.98    inference(ennf_transformation,[],[f9])).
% 3.63/0.98  
% 3.63/0.98  fof(f73,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f27])).
% 3.63/0.98  
% 3.63/0.98  fof(f106,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.63/0.98    inference(definition_unfolding,[],[f73,f94])).
% 3.63/0.98  
% 3.63/0.98  fof(f90,plain,(
% 3.63/0.98    k1_tarski(sK5) != sK7 | k1_tarski(sK5) != sK6),
% 3.63/0.98    inference(cnf_transformation,[],[f52])).
% 3.63/0.98  
% 3.63/0.98  fof(f118,plain,(
% 3.63/0.98    k2_enumset1(sK5,sK5,sK5,sK5) != sK7 | k2_enumset1(sK5,sK5,sK5,sK5) != sK6),
% 3.63/0.98    inference(definition_unfolding,[],[f90,f95,f95])).
% 3.63/0.98  
% 3.63/0.98  fof(f91,plain,(
% 3.63/0.98    k1_tarski(sK5) != sK7 | k1_xboole_0 != sK6),
% 3.63/0.98    inference(cnf_transformation,[],[f52])).
% 3.63/0.98  
% 3.63/0.98  fof(f117,plain,(
% 3.63/0.98    k2_enumset1(sK5,sK5,sK5,sK5) != sK7 | k1_xboole_0 != sK6),
% 3.63/0.98    inference(definition_unfolding,[],[f91,f95])).
% 3.63/0.98  
% 3.63/0.98  fof(f92,plain,(
% 3.63/0.98    k1_xboole_0 != sK7 | k1_tarski(sK5) != sK6),
% 3.63/0.98    inference(cnf_transformation,[],[f52])).
% 3.63/0.98  
% 3.63/0.98  fof(f116,plain,(
% 3.63/0.98    k1_xboole_0 != sK7 | k2_enumset1(sK5,sK5,sK5,sK5) != sK6),
% 3.63/0.98    inference(definition_unfolding,[],[f92,f95])).
% 3.63/0.98  
% 3.63/0.98  cnf(c_15,plain,
% 3.63/0.98      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1348,plain,
% 3.63/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_34,negated_conjecture,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) = k3_tarski(k2_enumset1(sK6,sK6,sK6,sK7)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f119]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_22,plain,
% 3.63/0.98      ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1780,plain,
% 3.63/0.98      ( k4_xboole_0(sK6,k2_enumset1(sK5,sK5,sK5,sK5)) = k1_xboole_0 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_34,c_22]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8,plain,
% 3.63/0.98      ( r2_hidden(X0,X1)
% 3.63/0.98      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 3.63/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1355,plain,
% 3.63/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.63/0.98      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3595,plain,
% 3.63/0.98      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
% 3.63/0.98      | r2_hidden(X0,k4_xboole_0(sK6,k1_xboole_0)) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_1780,c_1355]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_21,plain,
% 3.63/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_0,plain,
% 3.63/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1794,plain,
% 3.63/0.98      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_21,c_0]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_23,plain,
% 3.63/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1803,plain,
% 3.63/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.63/0.98      inference(light_normalisation,[status(thm)],[c_1794,c_23]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3599,plain,
% 3.63/0.98      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
% 3.63/0.98      | r2_hidden(X0,sK6) != iProver_top ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_3595,c_1803]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_27,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.63/0.98      inference(cnf_transformation,[],[f127]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1340,plain,
% 3.63/0.98      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3736,plain,
% 3.63/0.98      ( sK5 = X0 | r2_hidden(X0,sK6) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3599,c_1340]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6868,plain,
% 3.63/0.98      ( sK3(sK6) = sK5 | sK6 = k1_xboole_0 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_1348,c_3736]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8713,plain,
% 3.63/0.98      ( sK6 = k1_xboole_0 | r2_hidden(sK5,sK6) = iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_6868,c_1348]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_24,plain,
% 3.63/0.98      ( ~ r2_hidden(sK4(X0,X1),X1)
% 3.63/0.98      | k2_enumset1(X0,X0,X0,X0) = X1
% 3.63/0.98      | sK4(X0,X1) != X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1613,plain,
% 3.63/0.98      ( ~ r2_hidden(sK4(sK5,sK6),sK6)
% 3.63/0.98      | k2_enumset1(sK5,sK5,sK5,sK5) = sK6
% 3.63/0.98      | sK4(sK5,sK6) != sK5 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1614,plain,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) = sK6
% 3.63/0.98      | sK4(sK5,sK6) != sK5
% 3.63/0.98      | r2_hidden(sK4(sK5,sK6),sK6) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_1613]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_16,plain,
% 3.63/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2361,plain,
% 3.63/0.98      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3887,plain,
% 3.63/0.98      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_2361]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_18,plain,
% 3.63/0.98      ( r1_tarski(X0,X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f124]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3888,plain,
% 3.63/0.98      ( r1_tarski(sK6,sK6) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_25,plain,
% 3.63/0.98      ( r2_hidden(sK4(X0,X1),X1)
% 3.63/0.98      | k2_enumset1(X0,X0,X0,X0) = X1
% 3.63/0.98      | sK4(X0,X1) = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1342,plain,
% 3.63/0.98      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.63/0.98      | sK4(X0,X1) = X0
% 3.63/0.98      | r2_hidden(sK4(X0,X1),X1) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6869,plain,
% 3.63/0.98      ( k2_enumset1(X0,X0,X0,X0) = sK6
% 3.63/0.98      | sK4(X0,sK6) = X0
% 3.63/0.98      | sK4(X0,sK6) = sK5 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_1342,c_3736]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6935,plain,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) = sK6 | sK4(sK5,sK6) = sK5 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_6869]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_759,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.63/0.98      theory(equality) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2887,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,X1)
% 3.63/0.98      | r2_hidden(sK4(sK5,sK6),sK6)
% 3.63/0.98      | sK4(sK5,sK6) != X0
% 3.63/0.98      | sK6 != X1 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_759]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8658,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,sK6)
% 3.63/0.98      | r2_hidden(sK4(sK5,sK6),sK6)
% 3.63/0.98      | sK4(sK5,sK6) != X0
% 3.63/0.98      | sK6 != sK6 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_2887]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8660,plain,
% 3.63/0.98      ( sK4(sK5,sK6) != X0
% 3.63/0.98      | sK6 != sK6
% 3.63/0.98      | r2_hidden(X0,sK6) != iProver_top
% 3.63/0.98      | r2_hidden(sK4(sK5,sK6),sK6) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_8658]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8662,plain,
% 3.63/0.98      ( sK4(sK5,sK6) != sK5
% 3.63/0.98      | sK6 != sK6
% 3.63/0.98      | r2_hidden(sK4(sK5,sK6),sK6) = iProver_top
% 3.63/0.98      | r2_hidden(sK5,sK6) != iProver_top ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_8660]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1346,plain,
% 3.63/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_19,plain,
% 3.63/0.98      ( ~ r1_tarski(X0,X1)
% 3.63/0.98      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
% 3.63/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1345,plain,
% 3.63/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.63/0.98      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3644,plain,
% 3.63/0.98      ( r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
% 3.63/0.98      | r1_tarski(X0,sK7) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_34,c_1345]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_30,plain,
% 3.63/0.98      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 3.63/0.98      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.63/0.98      | k1_xboole_0 = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f115]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1337,plain,
% 3.63/0.98      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.63/0.98      | k1_xboole_0 = X1
% 3.63/0.98      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3699,plain,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) = X0
% 3.63/0.98      | k1_xboole_0 = X0
% 3.63/0.98      | r1_tarski(X0,sK7) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3644,c_1337]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3731,plain,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) = sK7 | sK7 = k1_xboole_0 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_1346,c_3699]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_29,plain,
% 3.63/0.98      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f129]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1338,plain,
% 3.63/0.98      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3814,plain,
% 3.63/0.98      ( sK7 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK7) = iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3731,c_1338]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_20,plain,
% 3.63/0.98      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
% 3.63/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1344,plain,
% 3.63/0.98      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
% 3.63/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3698,plain,
% 3.63/0.98      ( k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK5,sK5,sK5,sK5)
% 3.63/0.98      | r1_tarski(X0,sK7) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3644,c_1344]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6844,plain,
% 3.63/0.98      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK5,sK5,sK5,sK5)
% 3.63/0.98      | sK7 = k1_xboole_0 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3814,c_3698]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2774,plain,
% 3.63/0.98      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0) ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_1338,c_1344]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2780,plain,
% 3.63/0.98      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_2774]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7853,plain,
% 3.63/0.98      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_6844,c_2780]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7861,plain,
% 3.63/0.98      ( k4_xboole_0(k1_xboole_0,k2_enumset1(sK5,sK5,sK5,sK5)) = k1_xboole_0 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_7853,c_22]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8566,plain,
% 3.63/0.98      ( k4_xboole_0(k1_xboole_0,sK7) = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3731,c_7861]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_33,negated_conjecture,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) != sK6
% 3.63/0.98      | k2_enumset1(sK5,sK5,sK5,sK5) != sK7 ),
% 3.63/0.98      inference(cnf_transformation,[],[f118]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_32,negated_conjecture,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) != sK7 | k1_xboole_0 != sK6 ),
% 3.63/0.98      inference(cnf_transformation,[],[f117]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3821,plain,
% 3.63/0.98      ( sK6 != k1_xboole_0 | sK7 = k1_xboole_0 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3731,c_32]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8715,plain,
% 3.63/0.98      ( sK7 = k1_xboole_0 ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_8566,c_33,c_1614,c_3731,c_3821,c_3887,c_3888,c_6935,
% 3.63/0.98                 c_8662,c_8713]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_31,negated_conjecture,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) != sK6 | k1_xboole_0 != sK7 ),
% 3.63/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8740,plain,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) != sK6
% 3.63/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_8715,c_31]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8744,plain,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) != sK6 ),
% 3.63/0.98      inference(equality_resolution_simp,[status(thm)],[c_8740]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_9694,plain,
% 3.63/0.98      ( sK6 = k1_xboole_0 ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_8713,c_1614,c_3887,c_3888,c_6935,c_8662,c_8744]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8741,plain,
% 3.63/0.98      ( k3_tarski(k2_enumset1(sK6,sK6,sK6,k1_xboole_0)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_8715,c_34]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_9698,plain,
% 3.63/0.98      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_9694,c_8741]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2773,plain,
% 3.63/0.98      ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_1346,c_1344]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_9741,plain,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0 ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_9698,c_2773]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8739,plain,
% 3.63/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) != k1_xboole_0
% 3.63/0.98      | sK6 != k1_xboole_0 ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_8715,c_32]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(contradiction,plain,
% 3.63/0.98      ( $false ),
% 3.63/0.98      inference(minisat,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_9741,c_8744,c_8739,c_8713,c_8662,c_6935,c_3888,c_3887,
% 3.63/0.98                 c_1614]) ).
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  ------                               Statistics
% 3.63/0.98  
% 3.63/0.98  ------ General
% 3.63/0.98  
% 3.63/0.98  abstr_ref_over_cycles:                  0
% 3.63/0.98  abstr_ref_under_cycles:                 0
% 3.63/0.98  gc_basic_clause_elim:                   0
% 3.63/0.98  forced_gc_time:                         0
% 3.63/0.98  parsing_time:                           0.011
% 3.63/0.98  unif_index_cands_time:                  0.
% 3.63/0.98  unif_index_add_time:                    0.
% 3.63/0.98  orderings_time:                         0.
% 3.63/0.98  out_proof_time:                         0.011
% 3.63/0.98  total_time:                             0.273
% 3.63/0.98  num_of_symbols:                         47
% 3.63/0.98  num_of_terms:                           7966
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing
% 3.63/0.98  
% 3.63/0.98  num_of_splits:                          0
% 3.63/0.98  num_of_split_atoms:                     0
% 3.63/0.98  num_of_reused_defs:                     0
% 3.63/0.98  num_eq_ax_congr_red:                    42
% 3.63/0.98  num_of_sem_filtered_clauses:            1
% 3.63/0.98  num_of_subtypes:                        0
% 3.63/0.98  monotx_restored_types:                  0
% 3.63/0.98  sat_num_of_epr_types:                   0
% 3.63/0.98  sat_num_of_non_cyclic_types:            0
% 3.63/0.98  sat_guarded_non_collapsed_types:        0
% 3.63/0.98  num_pure_diseq_elim:                    0
% 3.63/0.98  simp_replaced_by:                       0
% 3.63/0.98  res_preprocessed:                       153
% 3.63/0.98  prep_upred:                             0
% 3.63/0.98  prep_unflattend:                        0
% 3.63/0.98  smt_new_axioms:                         0
% 3.63/0.98  pred_elim_cands:                        3
% 3.63/0.98  pred_elim:                              0
% 3.63/0.98  pred_elim_cl:                           0
% 3.63/0.98  pred_elim_cycles:                       2
% 3.63/0.98  merged_defs:                            8
% 3.63/0.98  merged_defs_ncl:                        0
% 3.63/0.98  bin_hyper_res:                          8
% 3.63/0.99  prep_cycles:                            4
% 3.63/0.99  pred_elim_time:                         0.002
% 3.63/0.99  splitting_time:                         0.
% 3.63/0.99  sem_filter_time:                        0.
% 3.63/0.99  monotx_time:                            0.
% 3.63/0.99  subtype_inf_time:                       0.
% 3.63/0.99  
% 3.63/0.99  ------ Problem properties
% 3.63/0.99  
% 3.63/0.99  clauses:                                34
% 3.63/0.99  conjectures:                            4
% 3.63/0.99  epr:                                    4
% 3.63/0.99  horn:                                   26
% 3.63/0.99  ground:                                 4
% 3.63/0.99  unary:                                  9
% 3.63/0.99  binary:                                 15
% 3.63/0.99  lits:                                   70
% 3.63/0.99  lits_eq:                                26
% 3.63/0.99  fd_pure:                                0
% 3.63/0.99  fd_pseudo:                              0
% 3.63/0.99  fd_cond:                                1
% 3.63/0.99  fd_pseudo_cond:                         7
% 3.63/0.99  ac_symbols:                             0
% 3.63/0.99  
% 3.63/0.99  ------ Propositional Solver
% 3.63/0.99  
% 3.63/0.99  prop_solver_calls:                      27
% 3.63/0.99  prop_fast_solver_calls:                 938
% 3.63/0.99  smt_solver_calls:                       0
% 3.63/0.99  smt_fast_solver_calls:                  0
% 3.63/0.99  prop_num_of_clauses:                    3424
% 3.63/0.99  prop_preprocess_simplified:             10090
% 3.63/0.99  prop_fo_subsumed:                       8
% 3.63/0.99  prop_solver_time:                       0.
% 3.63/0.99  smt_solver_time:                        0.
% 3.63/0.99  smt_fast_solver_time:                   0.
% 3.63/0.99  prop_fast_solver_time:                  0.
% 3.63/0.99  prop_unsat_core_time:                   0.
% 3.63/0.99  
% 3.63/0.99  ------ QBF
% 3.63/0.99  
% 3.63/0.99  qbf_q_res:                              0
% 3.63/0.99  qbf_num_tautologies:                    0
% 3.63/0.99  qbf_prep_cycles:                        0
% 3.63/0.99  
% 3.63/0.99  ------ BMC1
% 3.63/0.99  
% 3.63/0.99  bmc1_current_bound:                     -1
% 3.63/0.99  bmc1_last_solved_bound:                 -1
% 3.63/0.99  bmc1_unsat_core_size:                   -1
% 3.63/0.99  bmc1_unsat_core_parents_size:           -1
% 3.63/0.99  bmc1_merge_next_fun:                    0
% 3.63/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.63/0.99  
% 3.63/0.99  ------ Instantiation
% 3.63/0.99  
% 3.63/0.99  inst_num_of_clauses:                    888
% 3.63/0.99  inst_num_in_passive:                    374
% 3.63/0.99  inst_num_in_active:                     349
% 3.63/0.99  inst_num_in_unprocessed:                165
% 3.63/0.99  inst_num_of_loops:                      480
% 3.63/0.99  inst_num_of_learning_restarts:          0
% 3.63/0.99  inst_num_moves_active_passive:          130
% 3.63/0.99  inst_lit_activity:                      0
% 3.63/0.99  inst_lit_activity_moves:                0
% 3.63/0.99  inst_num_tautologies:                   0
% 3.63/0.99  inst_num_prop_implied:                  0
% 3.63/0.99  inst_num_existing_simplified:           0
% 3.63/0.99  inst_num_eq_res_simplified:             0
% 3.63/0.99  inst_num_child_elim:                    0
% 3.63/0.99  inst_num_of_dismatching_blockings:      292
% 3.63/0.99  inst_num_of_non_proper_insts:           855
% 3.63/0.99  inst_num_of_duplicates:                 0
% 3.63/0.99  inst_inst_num_from_inst_to_res:         0
% 3.63/0.99  inst_dismatching_checking_time:         0.
% 3.63/0.99  
% 3.63/0.99  ------ Resolution
% 3.63/0.99  
% 3.63/0.99  res_num_of_clauses:                     0
% 3.63/0.99  res_num_in_passive:                     0
% 3.63/0.99  res_num_in_active:                      0
% 3.63/0.99  res_num_of_loops:                       157
% 3.63/0.99  res_forward_subset_subsumed:            39
% 3.63/0.99  res_backward_subset_subsumed:           0
% 3.63/0.99  res_forward_subsumed:                   0
% 3.63/0.99  res_backward_subsumed:                  0
% 3.63/0.99  res_forward_subsumption_resolution:     0
% 3.63/0.99  res_backward_subsumption_resolution:    0
% 3.63/0.99  res_clause_to_clause_subsumption:       1552
% 3.63/0.99  res_orphan_elimination:                 0
% 3.63/0.99  res_tautology_del:                      50
% 3.63/0.99  res_num_eq_res_simplified:              0
% 3.63/0.99  res_num_sel_changes:                    0
% 3.63/0.99  res_moves_from_active_to_pass:          0
% 3.63/0.99  
% 3.63/0.99  ------ Superposition
% 3.63/0.99  
% 3.63/0.99  sup_time_total:                         0.
% 3.63/0.99  sup_time_generating:                    0.
% 3.63/0.99  sup_time_sim_full:                      0.
% 3.63/0.99  sup_time_sim_immed:                     0.
% 3.63/0.99  
% 3.63/0.99  sup_num_of_clauses:                     229
% 3.63/0.99  sup_num_in_active:                      48
% 3.63/0.99  sup_num_in_passive:                     181
% 3.63/0.99  sup_num_of_loops:                       94
% 3.63/0.99  sup_fw_superposition:                   193
% 3.63/0.99  sup_bw_superposition:                   163
% 3.63/0.99  sup_immediate_simplified:               106
% 3.63/0.99  sup_given_eliminated:                   0
% 3.63/0.99  comparisons_done:                       0
% 3.63/0.99  comparisons_avoided:                    22
% 3.63/0.99  
% 3.63/0.99  ------ Simplifications
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  sim_fw_subset_subsumed:                 28
% 3.63/0.99  sim_bw_subset_subsumed:                 14
% 3.63/0.99  sim_fw_subsumed:                        14
% 3.63/0.99  sim_bw_subsumed:                        0
% 3.63/0.99  sim_fw_subsumption_res:                 3
% 3.63/0.99  sim_bw_subsumption_res:                 0
% 3.63/0.99  sim_tautology_del:                      30
% 3.63/0.99  sim_eq_tautology_del:                   17
% 3.63/0.99  sim_eq_res_simp:                        6
% 3.63/0.99  sim_fw_demodulated:                     49
% 3.63/0.99  sim_bw_demodulated:                     47
% 3.63/0.99  sim_light_normalised:                   15
% 3.63/0.99  sim_joinable_taut:                      0
% 3.63/0.99  sim_joinable_simp:                      0
% 3.63/0.99  sim_ac_normalised:                      0
% 3.63/0.99  sim_smt_subsumption:                    0
% 3.63/0.99  
%------------------------------------------------------------------------------
