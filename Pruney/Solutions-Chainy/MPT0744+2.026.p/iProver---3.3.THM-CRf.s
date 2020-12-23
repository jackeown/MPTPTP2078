%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:51 EST 2020

% Result     : Theorem 27.88s
% Output     : CNFRefutation 27.88s
% Verified   : 
% Statistics : Number of formulae       :  209 (2055 expanded)
%              Number of clauses        :  114 ( 452 expanded)
%              Number of leaves         :   30 ( 527 expanded)
%              Depth                    :   20
%              Number of atoms          :  727 (7685 expanded)
%              Number of equality atoms :  329 (1013 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f23,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f57])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK5)
          | ~ r2_hidden(X0,k1_ordinal1(sK5)) )
        & ( r1_ordinal1(X0,sK5)
          | r2_hidden(X0,k1_ordinal1(sK5)) )
        & v3_ordinal1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK4,X1)
            | ~ r2_hidden(sK4,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK4,X1)
            | r2_hidden(sK4,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ r1_ordinal1(sK4,sK5)
      | ~ r2_hidden(sK4,k1_ordinal1(sK5)) )
    & ( r1_ordinal1(sK4,sK5)
      | r2_hidden(sK4,k1_ordinal1(sK5)) )
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f58,f60,f59])).

fof(f111,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f61])).

fof(f17,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f113,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f83,f85])).

fof(f114,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f82,f113])).

fof(f115,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f81,f114])).

fof(f116,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f102,f80,f115])).

fof(f122,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(definition_unfolding,[],[f111,f116])).

fof(f109,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f110,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f19,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f120,plain,(
    ! [X0] : r2_hidden(X0,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0))) ),
    inference(definition_unfolding,[],[f105,f116])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f20,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f117,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f112,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f61])).

fof(f121,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(definition_unfolding,[],[f112,f116])).

fof(f21,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f40,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f50,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f51,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(flattening,[],[f50])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7
                & X5 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | X5 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X0 != X7
              & X1 != X7
              & X2 != X7
              & X3 != X7
              & X4 != X7
              & X5 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X0 = X7
            | X1 = X7
            | X2 = X7
            | X3 = X7
            | X4 = X7
            | X5 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6) != X0
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X5 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6) = X0
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X5
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6) != X0
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X5 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6) = X0
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X5
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( X0 = X8
      | X1 = X8
      | X2 = X8
      | X3 = X8
      | X4 = X8
      | X5 = X8
      | ~ r2_hidden(X8,X6)
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP0(X5,X4,X3,X2,X1,X0,X6) ) ),
    inference(definition_folding,[],[f31,f40])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) )
      & ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f119,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f100,f84])).

fof(f129,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f119])).

cnf(c_35,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_41,negated_conjecture,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_335,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(prop_impl,[status(thm)],[c_41])).

cnf(c_643,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_335])).

cnf(c_644,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_43,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_42,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_646,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_43,c_42])).

cnf(c_2071,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(prop_impl,[status(thm)],[c_43,c_42,c_644])).

cnf(c_4517,plain,
    ( r1_tarski(sK4,sK5) = iProver_top
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2071])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4550,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13035,plain,
    ( r1_tarski(sK4,sK5) = iProver_top
    | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4517,c_4550])).

cnf(c_44,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_45,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_36,plain,
    ( r2_hidden(X0,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_57,plain,
    ( r2_hidden(X0,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_59,plain,
    ( r2_hidden(sK5,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_39,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_4904,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_4905,plain,
    ( r1_tarski(sK4,sK5) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4904])).

cnf(c_4993,plain,
    ( r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
    | r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4994,plain,
    ( r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) = iProver_top
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4993])).

cnf(c_3565,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_9042,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) = k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) ),
    inference(instantiation,[status(thm)],[c_3565])).

cnf(c_9045,plain,
    ( k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) = k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) ),
    inference(instantiation,[status(thm)],[c_9042])).

cnf(c_37,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_14865,plain,
    ( r2_hidden(X0,sK4)
    | r2_hidden(sK4,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_14866,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14865])).

cnf(c_14868,plain,
    ( sK4 = sK5
    | r2_hidden(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14866])).

cnf(c_17,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_4541,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4554,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12618,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4541,c_4554])).

cnf(c_34,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_40,negated_conjecture,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_333,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(prop_impl,[status(thm)],[c_40])).

cnf(c_629,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_333])).

cnf(c_630,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_632,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_43,c_42])).

cnf(c_2069,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(prop_impl,[status(thm)],[c_43,c_42,c_630])).

cnf(c_4518,plain,
    ( r1_tarski(sK4,sK5) != iProver_top
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2069])).

cnf(c_21689,plain,
    ( r1_tarski(sK4,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_12618,c_4518])).

cnf(c_38,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_615,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_333])).

cnf(c_616,plain,
    ( r2_hidden(sK5,sK4)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_618,plain,
    ( r2_hidden(sK5,sK4)
    | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_43,c_42])).

cnf(c_2144,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK5,sK4) ),
    inference(bin_hyper_res,[status(thm)],[c_618,c_2071])).

cnf(c_2153,plain,
    ( r1_tarski(sK4,sK5) = iProver_top
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2144])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4875,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4876,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4875])).

cnf(c_22233,plain,
    ( r2_hidden(sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21689,c_2153,c_4876])).

cnf(c_10017,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
    | r2_hidden(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_2071,c_7])).

cnf(c_6149,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r2_hidden(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_6154,plain,
    ( ~ r1_tarski(sK5,sK4)
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_6149])).

cnf(c_12,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8023,plain,
    ( r1_tarski(X0,sK4)
    | k4_xboole_0(X0,sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_8025,plain,
    ( r1_tarski(sK5,sK4)
    | k4_xboole_0(sK5,sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8023])).

cnf(c_596,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_38,c_35])).

cnf(c_8021,plain,
    ( r1_tarski(X0,sK4)
    | r2_hidden(sK4,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_8032,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8021])).

cnf(c_8034,plain,
    ( r1_tarski(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8032])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_12501,plain,
    ( ~ r1_tarski(X0,sK4)
    | k4_xboole_0(X0,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12502,plain,
    ( k4_xboole_0(X0,sK4) = k1_xboole_0
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12501])).

cnf(c_12504,plain,
    ( k4_xboole_0(sK5,sK4) = k1_xboole_0
    | r1_tarski(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12502])).

cnf(c_44551,plain,
    ( r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
    | r1_tarski(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10017,c_44,c_45,c_2153,c_4876,c_6154,c_8025,c_8034,c_12504,c_21689])).

cnf(c_44552,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) ),
    inference(renaming,[status(thm)],[c_44551])).

cnf(c_44553,plain,
    ( r1_tarski(sK4,sK5) = iProver_top
    | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44552])).

cnf(c_3567,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5036,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k5_xboole_0(X2,k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X2)))
    | X0 != X2
    | X1 != k5_xboole_0(X2,k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X2)) ),
    inference(instantiation,[status(thm)],[c_3567])).

cnf(c_9041,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)))
    | r2_hidden(X1,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)))
    | X1 != X0
    | k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) != k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) ),
    inference(instantiation,[status(thm)],[c_5036])).

cnf(c_92215,plain,
    ( ~ r2_hidden(sK5,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
    | k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) != k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_9041])).

cnf(c_92216,plain,
    ( k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) != k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
    | sK4 != sK5
    | r2_hidden(sK5,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) != iProver_top
    | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_92215])).

cnf(c_107954,plain,
    ( r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13035,c_44,c_45,c_59,c_2153,c_4876,c_4905,c_4994,c_9045,c_14868,c_21689,c_44553,c_92216])).

cnf(c_15,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4542,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4546,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5101,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4542,c_4546])).

cnf(c_5110,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5101,c_4541])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_5113,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5110,c_16])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4543,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6276,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5113,c_4543])).

cnf(c_12621,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6276,c_4554])).

cnf(c_107964,plain,
    ( r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_107954,c_12621])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13133,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
    | r2_hidden(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_2069,c_4])).

cnf(c_50774,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
    | ~ r1_tarski(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13133,c_44,c_45,c_2153,c_4876,c_6154,c_8025,c_8034,c_12504,c_21689])).

cnf(c_50775,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) ),
    inference(renaming,[status(thm)],[c_50774])).

cnf(c_50776,plain,
    ( r1_tarski(sK4,sK5) != iProver_top
    | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50775])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | ~ r2_hidden(X7,X6)
    | X7 = X5
    | X7 = X4
    | X7 = X3
    | X7 = X2
    | X7 = X1
    | X7 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_14860,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | ~ r2_hidden(sK4,X6)
    | sK4 = X0
    | sK4 = X1
    | sK4 = X2
    | sK4 = X5
    | sK4 = X4
    | sK4 = X3 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_29446,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0))
    | ~ r2_hidden(sK4,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0))
    | sK4 = X0
    | sK4 = X1
    | sK4 = X2
    | sK4 = X5
    | sK4 = X4
    | sK4 = X3 ),
    inference(instantiation,[status(thm)],[c_14860])).

cnf(c_29447,plain,
    ( sK4 = X0
    | sK4 = X1
    | sK4 = X2
    | sK4 = X3
    | sK4 = X4
    | sK4 = X5
    | sP0(X0,X1,X2,X5,X4,X3,k6_enumset1(X3,X3,X3,X4,X5,X2,X1,X0)) != iProver_top
    | r2_hidden(sK4,k6_enumset1(X3,X3,X3,X4,X5,X2,X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29446])).

cnf(c_29449,plain,
    ( sK4 = sK5
    | sP0(sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29447])).

cnf(c_3568,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5171,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK5)
    | sK5 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_3568])).

cnf(c_5172,plain,
    ( sK5 != X0
    | sK4 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5171])).

cnf(c_5174,plain,
    ( sK5 != sK5
    | sK4 != sK5
    | r1_tarski(sK5,sK5) != iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5172])).

cnf(c_136,plain,
    ( ~ r2_hidden(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_111,plain,
    ( ~ r1_tarski(sK5,sK5)
    | k4_xboole_0(sK5,sK5) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_107,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_109,plain,
    ( k4_xboole_0(sK5,sK5) != k1_xboole_0
    | r1_tarski(sK5,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_33,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_66,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_68,plain,
    ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_61,plain,
    ( ~ r1_ordinal1(sK5,sK5)
    | r1_tarski(sK5,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_55,plain,
    ( r2_hidden(sK5,sK5)
    | ~ v3_ordinal1(sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_52,plain,
    ( r1_ordinal1(sK5,sK5)
    | r2_hidden(sK5,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_107964,c_107954,c_50776,c_29449,c_5174,c_136,c_111,c_109,c_68,c_61,c_55,c_52,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:56:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.88/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.88/3.99  
% 27.88/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.88/3.99  
% 27.88/3.99  ------  iProver source info
% 27.88/3.99  
% 27.88/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.88/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.88/3.99  git: non_committed_changes: false
% 27.88/3.99  git: last_make_outside_of_git: false
% 27.88/3.99  
% 27.88/3.99  ------ 
% 27.88/3.99  ------ Parsing...
% 27.88/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.88/3.99  
% 27.88/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.88/3.99  
% 27.88/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.88/3.99  
% 27.88/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.88/3.99  ------ Proving...
% 27.88/3.99  ------ Problem Properties 
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  clauses                                 43
% 27.88/3.99  conjectures                             2
% 27.88/3.99  EPR                                     17
% 27.88/3.99  Horn                                    31
% 27.88/3.99  unary                                   7
% 27.88/3.99  binary                                  20
% 27.88/3.99  lits                                    108
% 27.88/3.99  lits eq                                 23
% 27.88/3.99  fd_pure                                 0
% 27.88/3.99  fd_pseudo                               0
% 27.88/3.99  fd_cond                                 0
% 27.88/3.99  fd_pseudo_cond                          3
% 27.88/3.99  AC symbols                              0
% 27.88/3.99  
% 27.88/3.99  ------ Input Options Time Limit: Unbounded
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  ------ 
% 27.88/3.99  Current options:
% 27.88/3.99  ------ 
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  ------ Proving...
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  % SZS status Theorem for theBenchmark.p
% 27.88/3.99  
% 27.88/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.88/3.99  
% 27.88/3.99  fof(f18,axiom,(
% 27.88/3.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f32,plain,(
% 27.88/3.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 27.88/3.99    inference(ennf_transformation,[],[f18])).
% 27.88/3.99  
% 27.88/3.99  fof(f33,plain,(
% 27.88/3.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 27.88/3.99    inference(flattening,[],[f32])).
% 27.88/3.99  
% 27.88/3.99  fof(f56,plain,(
% 27.88/3.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 27.88/3.99    inference(nnf_transformation,[],[f33])).
% 27.88/3.99  
% 27.88/3.99  fof(f103,plain,(
% 27.88/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f56])).
% 27.88/3.99  
% 27.88/3.99  fof(f23,conjecture,(
% 27.88/3.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f24,negated_conjecture,(
% 27.88/3.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 27.88/3.99    inference(negated_conjecture,[],[f23])).
% 27.88/3.99  
% 27.88/3.99  fof(f39,plain,(
% 27.88/3.99    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 27.88/3.99    inference(ennf_transformation,[],[f24])).
% 27.88/3.99  
% 27.88/3.99  fof(f57,plain,(
% 27.88/3.99    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 27.88/3.99    inference(nnf_transformation,[],[f39])).
% 27.88/3.99  
% 27.88/3.99  fof(f58,plain,(
% 27.88/3.99    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 27.88/3.99    inference(flattening,[],[f57])).
% 27.88/3.99  
% 27.88/3.99  fof(f60,plain,(
% 27.88/3.99    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK5) | ~r2_hidden(X0,k1_ordinal1(sK5))) & (r1_ordinal1(X0,sK5) | r2_hidden(X0,k1_ordinal1(sK5))) & v3_ordinal1(sK5))) )),
% 27.88/3.99    introduced(choice_axiom,[])).
% 27.88/3.99  
% 27.88/3.99  fof(f59,plain,(
% 27.88/3.99    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK4,X1) | ~r2_hidden(sK4,k1_ordinal1(X1))) & (r1_ordinal1(sK4,X1) | r2_hidden(sK4,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 27.88/3.99    introduced(choice_axiom,[])).
% 27.88/3.99  
% 27.88/3.99  fof(f61,plain,(
% 27.88/3.99    ((~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))) & (r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 27.88/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f58,f60,f59])).
% 27.88/3.99  
% 27.88/3.99  fof(f111,plain,(
% 27.88/3.99    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))),
% 27.88/3.99    inference(cnf_transformation,[],[f61])).
% 27.88/3.99  
% 27.88/3.99  fof(f17,axiom,(
% 27.88/3.99    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f102,plain,(
% 27.88/3.99    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f17])).
% 27.88/3.99  
% 27.88/3.99  fof(f10,axiom,(
% 27.88/3.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f80,plain,(
% 27.88/3.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f10])).
% 27.88/3.99  
% 27.88/3.99  fof(f11,axiom,(
% 27.88/3.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f81,plain,(
% 27.88/3.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f11])).
% 27.88/3.99  
% 27.88/3.99  fof(f12,axiom,(
% 27.88/3.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f82,plain,(
% 27.88/3.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f12])).
% 27.88/3.99  
% 27.88/3.99  fof(f13,axiom,(
% 27.88/3.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f83,plain,(
% 27.88/3.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f13])).
% 27.88/3.99  
% 27.88/3.99  fof(f15,axiom,(
% 27.88/3.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f85,plain,(
% 27.88/3.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f15])).
% 27.88/3.99  
% 27.88/3.99  fof(f113,plain,(
% 27.88/3.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 27.88/3.99    inference(definition_unfolding,[],[f83,f85])).
% 27.88/3.99  
% 27.88/3.99  fof(f114,plain,(
% 27.88/3.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 27.88/3.99    inference(definition_unfolding,[],[f82,f113])).
% 27.88/3.99  
% 27.88/3.99  fof(f115,plain,(
% 27.88/3.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 27.88/3.99    inference(definition_unfolding,[],[f81,f114])).
% 27.88/3.99  
% 27.88/3.99  fof(f116,plain,(
% 27.88/3.99    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) = k1_ordinal1(X0)) )),
% 27.88/3.99    inference(definition_unfolding,[],[f102,f80,f115])).
% 27.88/3.99  
% 27.88/3.99  fof(f122,plain,(
% 27.88/3.99    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))),
% 27.88/3.99    inference(definition_unfolding,[],[f111,f116])).
% 27.88/3.99  
% 27.88/3.99  fof(f109,plain,(
% 27.88/3.99    v3_ordinal1(sK4)),
% 27.88/3.99    inference(cnf_transformation,[],[f61])).
% 27.88/3.99  
% 27.88/3.99  fof(f110,plain,(
% 27.88/3.99    v3_ordinal1(sK5)),
% 27.88/3.99    inference(cnf_transformation,[],[f61])).
% 27.88/3.99  
% 27.88/3.99  fof(f3,axiom,(
% 27.88/3.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f28,plain,(
% 27.88/3.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 27.88/3.99    inference(ennf_transformation,[],[f3])).
% 27.88/3.99  
% 27.88/3.99  fof(f46,plain,(
% 27.88/3.99    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 27.88/3.99    inference(nnf_transformation,[],[f28])).
% 27.88/3.99  
% 27.88/3.99  fof(f66,plain,(
% 27.88/3.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 27.88/3.99    inference(cnf_transformation,[],[f46])).
% 27.88/3.99  
% 27.88/3.99  fof(f19,axiom,(
% 27.88/3.99    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f105,plain,(
% 27.88/3.99    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 27.88/3.99    inference(cnf_transformation,[],[f19])).
% 27.88/3.99  
% 27.88/3.99  fof(f120,plain,(
% 27.88/3.99    ( ! [X0] : (r2_hidden(X0,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)))) )),
% 27.88/3.99    inference(definition_unfolding,[],[f105,f116])).
% 27.88/3.99  
% 27.88/3.99  fof(f22,axiom,(
% 27.88/3.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f38,plain,(
% 27.88/3.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 27.88/3.99    inference(ennf_transformation,[],[f22])).
% 27.88/3.99  
% 27.88/3.99  fof(f108,plain,(
% 27.88/3.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f38])).
% 27.88/3.99  
% 27.88/3.99  fof(f20,axiom,(
% 27.88/3.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f34,plain,(
% 27.88/3.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 27.88/3.99    inference(ennf_transformation,[],[f20])).
% 27.88/3.99  
% 27.88/3.99  fof(f35,plain,(
% 27.88/3.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 27.88/3.99    inference(flattening,[],[f34])).
% 27.88/3.99  
% 27.88/3.99  fof(f106,plain,(
% 27.88/3.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f35])).
% 27.88/3.99  
% 27.88/3.99  fof(f9,axiom,(
% 27.88/3.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f79,plain,(
% 27.88/3.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.88/3.99    inference(cnf_transformation,[],[f9])).
% 27.88/3.99  
% 27.88/3.99  fof(f117,plain,(
% 27.88/3.99    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 27.88/3.99    inference(definition_unfolding,[],[f79,f80])).
% 27.88/3.99  
% 27.88/3.99  fof(f2,axiom,(
% 27.88/3.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f27,plain,(
% 27.88/3.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 27.88/3.99    inference(ennf_transformation,[],[f2])).
% 27.88/3.99  
% 27.88/3.99  fof(f42,plain,(
% 27.88/3.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 27.88/3.99    inference(nnf_transformation,[],[f27])).
% 27.88/3.99  
% 27.88/3.99  fof(f43,plain,(
% 27.88/3.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.88/3.99    inference(rectify,[],[f42])).
% 27.88/3.99  
% 27.88/3.99  fof(f44,plain,(
% 27.88/3.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 27.88/3.99    introduced(choice_axiom,[])).
% 27.88/3.99  
% 27.88/3.99  fof(f45,plain,(
% 27.88/3.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.88/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 27.88/3.99  
% 27.88/3.99  fof(f63,plain,(
% 27.88/3.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f45])).
% 27.88/3.99  
% 27.88/3.99  fof(f104,plain,(
% 27.88/3.99    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f56])).
% 27.88/3.99  
% 27.88/3.99  fof(f112,plain,(
% 27.88/3.99    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))),
% 27.88/3.99    inference(cnf_transformation,[],[f61])).
% 27.88/3.99  
% 27.88/3.99  fof(f121,plain,(
% 27.88/3.99    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))),
% 27.88/3.99    inference(definition_unfolding,[],[f112,f116])).
% 27.88/3.99  
% 27.88/3.99  fof(f21,axiom,(
% 27.88/3.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f36,plain,(
% 27.88/3.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 27.88/3.99    inference(ennf_transformation,[],[f21])).
% 27.88/3.99  
% 27.88/3.99  fof(f37,plain,(
% 27.88/3.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 27.88/3.99    inference(flattening,[],[f36])).
% 27.88/3.99  
% 27.88/3.99  fof(f107,plain,(
% 27.88/3.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f37])).
% 27.88/3.99  
% 27.88/3.99  fof(f1,axiom,(
% 27.88/3.99    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f26,plain,(
% 27.88/3.99    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 27.88/3.99    inference(ennf_transformation,[],[f1])).
% 27.88/3.99  
% 27.88/3.99  fof(f62,plain,(
% 27.88/3.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f26])).
% 27.88/3.99  
% 27.88/3.99  fof(f5,axiom,(
% 27.88/3.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f49,plain,(
% 27.88/3.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 27.88/3.99    inference(nnf_transformation,[],[f5])).
% 27.88/3.99  
% 27.88/3.99  fof(f73,plain,(
% 27.88/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.88/3.99    inference(cnf_transformation,[],[f49])).
% 27.88/3.99  
% 27.88/3.99  fof(f74,plain,(
% 27.88/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f49])).
% 27.88/3.99  
% 27.88/3.99  fof(f7,axiom,(
% 27.88/3.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f77,plain,(
% 27.88/3.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f7])).
% 27.88/3.99  
% 27.88/3.99  fof(f8,axiom,(
% 27.88/3.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f78,plain,(
% 27.88/3.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.88/3.99    inference(cnf_transformation,[],[f8])).
% 27.88/3.99  
% 27.88/3.99  fof(f6,axiom,(
% 27.88/3.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f30,plain,(
% 27.88/3.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 27.88/3.99    inference(ennf_transformation,[],[f6])).
% 27.88/3.99  
% 27.88/3.99  fof(f75,plain,(
% 27.88/3.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 27.88/3.99    inference(cnf_transformation,[],[f30])).
% 27.88/3.99  
% 27.88/3.99  fof(f69,plain,(
% 27.88/3.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f46])).
% 27.88/3.99  
% 27.88/3.99  fof(f40,plain,(
% 27.88/3.99    ! [X5,X4,X3,X2,X1,X0,X6] : (sP0(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 27.88/3.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 27.88/3.99  
% 27.88/3.99  fof(f50,plain,(
% 27.88/3.99    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 27.88/3.99    inference(nnf_transformation,[],[f40])).
% 27.88/3.99  
% 27.88/3.99  fof(f51,plain,(
% 27.88/3.99    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 27.88/3.99    inference(flattening,[],[f50])).
% 27.88/3.99  
% 27.88/3.99  fof(f52,plain,(
% 27.88/3.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 27.88/3.99    inference(rectify,[],[f51])).
% 27.88/3.99  
% 27.88/3.99  fof(f53,plain,(
% 27.88/3.99    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK3(X0,X1,X2,X3,X4,X5,X6) != X0 & sK3(X0,X1,X2,X3,X4,X5,X6) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK3(X0,X1,X2,X3,X4,X5,X6) = X0 | sK3(X0,X1,X2,X3,X4,X5,X6) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 27.88/3.99    introduced(choice_axiom,[])).
% 27.88/3.99  
% 27.88/3.99  fof(f54,plain,(
% 27.88/3.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (((sK3(X0,X1,X2,X3,X4,X5,X6) != X0 & sK3(X0,X1,X2,X3,X4,X5,X6) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK3(X0,X1,X2,X3,X4,X5,X6) = X0 | sK3(X0,X1,X2,X3,X4,X5,X6) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 27.88/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).
% 27.88/3.99  
% 27.88/3.99  fof(f86,plain,(
% 27.88/3.99    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6) | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f54])).
% 27.88/3.99  
% 27.88/3.99  fof(f16,axiom,(
% 27.88/3.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f31,plain,(
% 27.88/3.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 27.88/3.99    inference(ennf_transformation,[],[f16])).
% 27.88/3.99  
% 27.88/3.99  fof(f41,plain,(
% 27.88/3.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X4,X3,X2,X1,X0,X6))),
% 27.88/3.99    inference(definition_folding,[],[f31,f40])).
% 27.88/3.99  
% 27.88/3.99  fof(f55,plain,(
% 27.88/3.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X4,X3,X2,X1,X0,X6)) & (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 27.88/3.99    inference(nnf_transformation,[],[f41])).
% 27.88/3.99  
% 27.88/3.99  fof(f100,plain,(
% 27.88/3.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 27.88/3.99    inference(cnf_transformation,[],[f55])).
% 27.88/3.99  
% 27.88/3.99  fof(f14,axiom,(
% 27.88/3.99    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f84,plain,(
% 27.88/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f14])).
% 27.88/3.99  
% 27.88/3.99  fof(f119,plain,(
% 27.88/3.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 27.88/3.99    inference(definition_unfolding,[],[f100,f84])).
% 27.88/3.99  
% 27.88/3.99  fof(f129,plain,(
% 27.88/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) )),
% 27.88/3.99    inference(equality_resolution,[],[f119])).
% 27.88/3.99  
% 27.88/3.99  cnf(c_35,plain,
% 27.88/3.99      ( ~ r1_ordinal1(X0,X1)
% 27.88/3.99      | r1_tarski(X0,X1)
% 27.88/3.99      | ~ v3_ordinal1(X1)
% 27.88/3.99      | ~ v3_ordinal1(X0) ),
% 27.88/3.99      inference(cnf_transformation,[],[f103]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_41,negated_conjecture,
% 27.88/3.99      ( r1_ordinal1(sK4,sK5)
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
% 27.88/3.99      inference(cnf_transformation,[],[f122]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_335,plain,
% 27.88/3.99      ( r1_ordinal1(sK4,sK5)
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
% 27.88/3.99      inference(prop_impl,[status(thm)],[c_41]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_643,plain,
% 27.88/3.99      ( r1_tarski(X0,X1)
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
% 27.88/3.99      | ~ v3_ordinal1(X0)
% 27.88/3.99      | ~ v3_ordinal1(X1)
% 27.88/3.99      | sK5 != X1
% 27.88/3.99      | sK4 != X0 ),
% 27.88/3.99      inference(resolution_lifted,[status(thm)],[c_35,c_335]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_644,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5)
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
% 27.88/3.99      | ~ v3_ordinal1(sK5)
% 27.88/3.99      | ~ v3_ordinal1(sK4) ),
% 27.88/3.99      inference(unflattening,[status(thm)],[c_643]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_43,negated_conjecture,
% 27.88/3.99      ( v3_ordinal1(sK4) ),
% 27.88/3.99      inference(cnf_transformation,[],[f109]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_42,negated_conjecture,
% 27.88/3.99      ( v3_ordinal1(sK5) ),
% 27.88/3.99      inference(cnf_transformation,[],[f110]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_646,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5)
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
% 27.88/3.99      inference(global_propositional_subsumption,
% 27.88/3.99                [status(thm)],
% 27.88/3.99                [c_644,c_43,c_42]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_2071,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5)
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
% 27.88/3.99      inference(prop_impl,[status(thm)],[c_43,c_42,c_644]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4517,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5) = iProver_top
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_2071]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_7,plain,
% 27.88/3.99      ( r2_hidden(X0,X1)
% 27.88/3.99      | r2_hidden(X0,X2)
% 27.88/3.99      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 27.88/3.99      inference(cnf_transformation,[],[f66]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4550,plain,
% 27.88/3.99      ( r2_hidden(X0,X1) = iProver_top
% 27.88/3.99      | r2_hidden(X0,X2) = iProver_top
% 27.88/3.99      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_13035,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5) = iProver_top
% 27.88/3.99      | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) = iProver_top
% 27.88/3.99      | r2_hidden(sK4,sK5) = iProver_top ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_4517,c_4550]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_44,plain,
% 27.88/3.99      ( v3_ordinal1(sK4) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_45,plain,
% 27.88/3.99      ( v3_ordinal1(sK5) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_36,plain,
% 27.88/3.99      ( r2_hidden(X0,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0))) ),
% 27.88/3.99      inference(cnf_transformation,[],[f120]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_57,plain,
% 27.88/3.99      ( r2_hidden(X0,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0))) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_59,plain,
% 27.88/3.99      ( r2_hidden(sK5,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) = iProver_top ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_57]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_39,plain,
% 27.88/3.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 27.88/3.99      inference(cnf_transformation,[],[f108]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4904,plain,
% 27.88/3.99      ( ~ r1_tarski(sK4,sK5) | ~ r2_hidden(sK5,sK4) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_39]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4905,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5) != iProver_top
% 27.88/3.99      | r2_hidden(sK5,sK4) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_4904]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4993,plain,
% 27.88/3.99      ( r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
% 27.88/3.99      | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
% 27.88/3.99      | r2_hidden(sK4,sK5) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_7]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4994,plain,
% 27.88/3.99      ( r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) = iProver_top
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) != iProver_top
% 27.88/3.99      | r2_hidden(sK4,sK5) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_4993]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_3565,plain,( X0 = X0 ),theory(equality) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_9042,plain,
% 27.88/3.99      ( k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) = k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_3565]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_9045,plain,
% 27.88/3.99      ( k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) = k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_9042]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_37,plain,
% 27.88/3.99      ( r2_hidden(X0,X1)
% 27.88/3.99      | r2_hidden(X1,X0)
% 27.88/3.99      | ~ v3_ordinal1(X0)
% 27.88/3.99      | ~ v3_ordinal1(X1)
% 27.88/3.99      | X1 = X0 ),
% 27.88/3.99      inference(cnf_transformation,[],[f106]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_14865,plain,
% 27.88/3.99      ( r2_hidden(X0,sK4)
% 27.88/3.99      | r2_hidden(sK4,X0)
% 27.88/3.99      | ~ v3_ordinal1(X0)
% 27.88/3.99      | ~ v3_ordinal1(sK4)
% 27.88/3.99      | sK4 = X0 ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_37]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_14866,plain,
% 27.88/3.99      ( sK4 = X0
% 27.88/3.99      | r2_hidden(X0,sK4) = iProver_top
% 27.88/3.99      | r2_hidden(sK4,X0) = iProver_top
% 27.88/3.99      | v3_ordinal1(X0) != iProver_top
% 27.88/3.99      | v3_ordinal1(sK4) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_14865]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_14868,plain,
% 27.88/3.99      ( sK4 = sK5
% 27.88/3.99      | r2_hidden(sK5,sK4) = iProver_top
% 27.88/3.99      | r2_hidden(sK4,sK5) = iProver_top
% 27.88/3.99      | v3_ordinal1(sK5) != iProver_top
% 27.88/3.99      | v3_ordinal1(sK4) != iProver_top ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_14866]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_17,plain,
% 27.88/3.99      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 27.88/3.99      inference(cnf_transformation,[],[f117]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4541,plain,
% 27.88/3.99      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_3,plain,
% 27.88/3.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 27.88/3.99      inference(cnf_transformation,[],[f63]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4554,plain,
% 27.88/3.99      ( r1_tarski(X0,X1) != iProver_top
% 27.88/3.99      | r2_hidden(X2,X0) != iProver_top
% 27.88/3.99      | r2_hidden(X2,X1) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_12618,plain,
% 27.88/3.99      ( r2_hidden(X0,X1) != iProver_top
% 27.88/3.99      | r2_hidden(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = iProver_top ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_4541,c_4554]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_34,plain,
% 27.88/3.99      ( r1_ordinal1(X0,X1)
% 27.88/3.99      | ~ r1_tarski(X0,X1)
% 27.88/3.99      | ~ v3_ordinal1(X1)
% 27.88/3.99      | ~ v3_ordinal1(X0) ),
% 27.88/3.99      inference(cnf_transformation,[],[f104]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_40,negated_conjecture,
% 27.88/3.99      ( ~ r1_ordinal1(sK4,sK5)
% 27.88/3.99      | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
% 27.88/3.99      inference(cnf_transformation,[],[f121]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_333,plain,
% 27.88/3.99      ( ~ r1_ordinal1(sK4,sK5)
% 27.88/3.99      | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
% 27.88/3.99      inference(prop_impl,[status(thm)],[c_40]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_629,plain,
% 27.88/3.99      ( ~ r1_tarski(X0,X1)
% 27.88/3.99      | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
% 27.88/3.99      | ~ v3_ordinal1(X0)
% 27.88/3.99      | ~ v3_ordinal1(X1)
% 27.88/3.99      | sK5 != X1
% 27.88/3.99      | sK4 != X0 ),
% 27.88/3.99      inference(resolution_lifted,[status(thm)],[c_34,c_333]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_630,plain,
% 27.88/3.99      ( ~ r1_tarski(sK4,sK5)
% 27.88/3.99      | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
% 27.88/3.99      | ~ v3_ordinal1(sK5)
% 27.88/3.99      | ~ v3_ordinal1(sK4) ),
% 27.88/3.99      inference(unflattening,[status(thm)],[c_629]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_632,plain,
% 27.88/3.99      ( ~ r1_tarski(sK4,sK5)
% 27.88/3.99      | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
% 27.88/3.99      inference(global_propositional_subsumption,
% 27.88/3.99                [status(thm)],
% 27.88/3.99                [c_630,c_43,c_42]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_2069,plain,
% 27.88/3.99      ( ~ r1_tarski(sK4,sK5)
% 27.88/3.99      | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
% 27.88/3.99      inference(prop_impl,[status(thm)],[c_43,c_42,c_630]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4518,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5) != iProver_top
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_2069]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_21689,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5) != iProver_top
% 27.88/3.99      | r2_hidden(sK4,sK5) != iProver_top ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_12618,c_4518]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_38,plain,
% 27.88/3.99      ( r1_ordinal1(X0,X1)
% 27.88/3.99      | r2_hidden(X1,X0)
% 27.88/3.99      | ~ v3_ordinal1(X1)
% 27.88/3.99      | ~ v3_ordinal1(X0) ),
% 27.88/3.99      inference(cnf_transformation,[],[f107]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_615,plain,
% 27.88/3.99      ( r2_hidden(X0,X1)
% 27.88/3.99      | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
% 27.88/3.99      | ~ v3_ordinal1(X1)
% 27.88/3.99      | ~ v3_ordinal1(X0)
% 27.88/3.99      | sK5 != X0
% 27.88/3.99      | sK4 != X1 ),
% 27.88/3.99      inference(resolution_lifted,[status(thm)],[c_38,c_333]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_616,plain,
% 27.88/3.99      ( r2_hidden(sK5,sK4)
% 27.88/3.99      | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
% 27.88/3.99      | ~ v3_ordinal1(sK5)
% 27.88/3.99      | ~ v3_ordinal1(sK4) ),
% 27.88/3.99      inference(unflattening,[status(thm)],[c_615]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_618,plain,
% 27.88/3.99      ( r2_hidden(sK5,sK4)
% 27.88/3.99      | ~ r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) ),
% 27.88/3.99      inference(global_propositional_subsumption,
% 27.88/3.99                [status(thm)],
% 27.88/3.99                [c_616,c_43,c_42]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_2144,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5) | r2_hidden(sK5,sK4) ),
% 27.88/3.99      inference(bin_hyper_res,[status(thm)],[c_618,c_2071]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_2153,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5) = iProver_top
% 27.88/3.99      | r2_hidden(sK5,sK4) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_2144]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_0,plain,
% 27.88/3.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 27.88/3.99      inference(cnf_transformation,[],[f62]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4875,plain,
% 27.88/3.99      ( ~ r2_hidden(sK5,sK4) | ~ r2_hidden(sK4,sK5) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_0]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4876,plain,
% 27.88/3.99      ( r2_hidden(sK5,sK4) != iProver_top
% 27.88/3.99      | r2_hidden(sK4,sK5) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_4875]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_22233,plain,
% 27.88/3.99      ( r2_hidden(sK4,sK5) != iProver_top ),
% 27.88/3.99      inference(global_propositional_subsumption,
% 27.88/3.99                [status(thm)],
% 27.88/3.99                [c_21689,c_2153,c_4876]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_10017,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5)
% 27.88/3.99      | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
% 27.88/3.99      | r2_hidden(sK4,sK5) ),
% 27.88/3.99      inference(resolution,[status(thm)],[c_2071,c_7]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_6149,plain,
% 27.88/3.99      ( ~ r1_tarski(X0,sK4) | ~ r2_hidden(sK4,X0) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_39]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_6154,plain,
% 27.88/3.99      ( ~ r1_tarski(sK5,sK4) | ~ r2_hidden(sK4,sK5) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_6149]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_12,plain,
% 27.88/3.99      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 27.88/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_8023,plain,
% 27.88/3.99      ( r1_tarski(X0,sK4) | k4_xboole_0(X0,sK4) != k1_xboole_0 ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_12]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_8025,plain,
% 27.88/3.99      ( r1_tarski(sK5,sK4) | k4_xboole_0(sK5,sK4) != k1_xboole_0 ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_8023]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_596,plain,
% 27.88/3.99      ( r1_tarski(X0,X1)
% 27.88/3.99      | r2_hidden(X1,X0)
% 27.88/3.99      | ~ v3_ordinal1(X0)
% 27.88/3.99      | ~ v3_ordinal1(X1) ),
% 27.88/3.99      inference(resolution,[status(thm)],[c_38,c_35]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_8021,plain,
% 27.88/3.99      ( r1_tarski(X0,sK4)
% 27.88/3.99      | r2_hidden(sK4,X0)
% 27.88/3.99      | ~ v3_ordinal1(X0)
% 27.88/3.99      | ~ v3_ordinal1(sK4) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_596]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_8032,plain,
% 27.88/3.99      ( r1_tarski(X0,sK4) = iProver_top
% 27.88/3.99      | r2_hidden(sK4,X0) = iProver_top
% 27.88/3.99      | v3_ordinal1(X0) != iProver_top
% 27.88/3.99      | v3_ordinal1(sK4) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_8021]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_8034,plain,
% 27.88/3.99      ( r1_tarski(sK5,sK4) = iProver_top
% 27.88/3.99      | r2_hidden(sK4,sK5) = iProver_top
% 27.88/3.99      | v3_ordinal1(sK5) != iProver_top
% 27.88/3.99      | v3_ordinal1(sK4) != iProver_top ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_8032]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_11,plain,
% 27.88/3.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 27.88/3.99      inference(cnf_transformation,[],[f74]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_12501,plain,
% 27.88/3.99      ( ~ r1_tarski(X0,sK4) | k4_xboole_0(X0,sK4) = k1_xboole_0 ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_11]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_12502,plain,
% 27.88/3.99      ( k4_xboole_0(X0,sK4) = k1_xboole_0
% 27.88/3.99      | r1_tarski(X0,sK4) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_12501]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_12504,plain,
% 27.88/3.99      ( k4_xboole_0(sK5,sK4) = k1_xboole_0
% 27.88/3.99      | r1_tarski(sK5,sK4) != iProver_top ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_12502]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_44551,plain,
% 27.88/3.99      ( r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
% 27.88/3.99      | r1_tarski(sK4,sK5) ),
% 27.88/3.99      inference(global_propositional_subsumption,
% 27.88/3.99                [status(thm)],
% 27.88/3.99                [c_10017,c_44,c_45,c_2153,c_4876,c_6154,c_8025,c_8034,
% 27.88/3.99                 c_12504,c_21689]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_44552,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5)
% 27.88/3.99      | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) ),
% 27.88/3.99      inference(renaming,[status(thm)],[c_44551]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_44553,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5) = iProver_top
% 27.88/3.99      | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_44552]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_3567,plain,
% 27.88/3.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.88/3.99      theory(equality) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_5036,plain,
% 27.88/3.99      ( r2_hidden(X0,X1)
% 27.88/3.99      | ~ r2_hidden(X2,k5_xboole_0(X2,k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X2)))
% 27.88/3.99      | X0 != X2
% 27.88/3.99      | X1 != k5_xboole_0(X2,k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X2)) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_3567]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_9041,plain,
% 27.88/3.99      ( ~ r2_hidden(X0,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)))
% 27.88/3.99      | r2_hidden(X1,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)))
% 27.88/3.99      | X1 != X0
% 27.88/3.99      | k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) != k5_xboole_0(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_5036]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_92215,plain,
% 27.88/3.99      ( ~ r2_hidden(sK5,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)))
% 27.88/3.99      | k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) != k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
% 27.88/3.99      | sK4 != sK5 ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_9041]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_92216,plain,
% 27.88/3.99      ( k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) != k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
% 27.88/3.99      | sK4 != sK5
% 27.88/3.99      | r2_hidden(sK5,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) != iProver_top
% 27.88/3.99      | r2_hidden(sK4,k5_xboole_0(sK5,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_92215]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_107954,plain,
% 27.88/3.99      ( r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) = iProver_top ),
% 27.88/3.99      inference(global_propositional_subsumption,
% 27.88/3.99                [status(thm)],
% 27.88/3.99                [c_13035,c_44,c_45,c_59,c_2153,c_4876,c_4905,c_4994,
% 27.88/3.99                 c_9045,c_14868,c_21689,c_44553,c_92216]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_15,plain,
% 27.88/3.99      ( r1_tarski(k1_xboole_0,X0) ),
% 27.88/3.99      inference(cnf_transformation,[],[f77]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4542,plain,
% 27.88/3.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4546,plain,
% 27.88/3.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 27.88/3.99      | r1_tarski(X0,X1) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_5101,plain,
% 27.88/3.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_4542,c_4546]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_5110,plain,
% 27.88/3.99      ( r1_tarski(X0,k5_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_5101,c_4541]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_16,plain,
% 27.88/3.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.88/3.99      inference(cnf_transformation,[],[f78]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_5113,plain,
% 27.88/3.99      ( r1_tarski(X0,X0) = iProver_top ),
% 27.88/3.99      inference(light_normalisation,[status(thm)],[c_5110,c_16]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_14,plain,
% 27.88/3.99      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
% 27.88/3.99      inference(cnf_transformation,[],[f75]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4543,plain,
% 27.88/3.99      ( r1_tarski(X0,X1) = iProver_top
% 27.88/3.99      | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_6276,plain,
% 27.88/3.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_5113,c_4543]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_12621,plain,
% 27.88/3.99      ( r2_hidden(X0,X1) = iProver_top
% 27.88/3.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_6276,c_4554]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_107964,plain,
% 27.88/3.99      ( r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_107954,c_12621]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4,plain,
% 27.88/3.99      ( ~ r2_hidden(X0,X1)
% 27.88/3.99      | r2_hidden(X0,X2)
% 27.88/3.99      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 27.88/3.99      inference(cnf_transformation,[],[f69]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_13133,plain,
% 27.88/3.99      ( ~ r1_tarski(sK4,sK5)
% 27.88/3.99      | ~ r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
% 27.88/3.99      | r2_hidden(sK4,sK5) ),
% 27.88/3.99      inference(resolution,[status(thm)],[c_2069,c_4]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_50774,plain,
% 27.88/3.99      ( ~ r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5))
% 27.88/3.99      | ~ r1_tarski(sK4,sK5) ),
% 27.88/3.99      inference(global_propositional_subsumption,
% 27.88/3.99                [status(thm)],
% 27.88/3.99                [c_13133,c_44,c_45,c_2153,c_4876,c_6154,c_8025,c_8034,
% 27.88/3.99                 c_12504,c_21689]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_50775,plain,
% 27.88/3.99      ( ~ r1_tarski(sK4,sK5)
% 27.88/3.99      | ~ r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) ),
% 27.88/3.99      inference(renaming,[status(thm)],[c_50774]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_50776,plain,
% 27.88/3.99      ( r1_tarski(sK4,sK5) != iProver_top
% 27.88/3.99      | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK5)) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_50775]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_31,plain,
% 27.88/3.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
% 27.88/3.99      | ~ r2_hidden(X7,X6)
% 27.88/3.99      | X7 = X5
% 27.88/3.99      | X7 = X4
% 27.88/3.99      | X7 = X3
% 27.88/3.99      | X7 = X2
% 27.88/3.99      | X7 = X1
% 27.88/3.99      | X7 = X0 ),
% 27.88/3.99      inference(cnf_transformation,[],[f86]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_14860,plain,
% 27.88/3.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
% 27.88/3.99      | ~ r2_hidden(sK4,X6)
% 27.88/3.99      | sK4 = X0
% 27.88/3.99      | sK4 = X1
% 27.88/3.99      | sK4 = X2
% 27.88/3.99      | sK4 = X5
% 27.88/3.99      | sK4 = X4
% 27.88/3.99      | sK4 = X3 ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_31]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_29446,plain,
% 27.88/3.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0))
% 27.88/3.99      | ~ r2_hidden(sK4,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0))
% 27.88/3.99      | sK4 = X0
% 27.88/3.99      | sK4 = X1
% 27.88/3.99      | sK4 = X2
% 27.88/3.99      | sK4 = X5
% 27.88/3.99      | sK4 = X4
% 27.88/3.99      | sK4 = X3 ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_14860]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_29447,plain,
% 27.88/3.99      ( sK4 = X0
% 27.88/3.99      | sK4 = X1
% 27.88/3.99      | sK4 = X2
% 27.88/3.99      | sK4 = X3
% 27.88/3.99      | sK4 = X4
% 27.88/3.99      | sK4 = X5
% 27.88/3.99      | sP0(X0,X1,X2,X5,X4,X3,k6_enumset1(X3,X3,X3,X4,X5,X2,X1,X0)) != iProver_top
% 27.88/3.99      | r2_hidden(sK4,k6_enumset1(X3,X3,X3,X4,X5,X2,X1,X0)) != iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_29446]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_29449,plain,
% 27.88/3.99      ( sK4 = sK5
% 27.88/3.99      | sP0(sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 27.88/3.99      | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_29447]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_3568,plain,
% 27.88/3.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.88/3.99      theory(equality) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_5171,plain,
% 27.88/3.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,sK5) | sK5 != X1 | sK4 != X0 ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_3568]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_5172,plain,
% 27.88/3.99      ( sK5 != X0
% 27.88/3.99      | sK4 != X1
% 27.88/3.99      | r1_tarski(X1,X0) != iProver_top
% 27.88/3.99      | r1_tarski(sK4,sK5) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_5171]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_5174,plain,
% 27.88/3.99      ( sK5 != sK5
% 27.88/3.99      | sK4 != sK5
% 27.88/3.99      | r1_tarski(sK5,sK5) != iProver_top
% 27.88/3.99      | r1_tarski(sK4,sK5) = iProver_top ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_5172]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_136,plain,
% 27.88/3.99      ( ~ r2_hidden(sK5,sK5) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_0]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_111,plain,
% 27.88/3.99      ( ~ r1_tarski(sK5,sK5) | k4_xboole_0(sK5,sK5) = k1_xboole_0 ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_11]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_107,plain,
% 27.88/3.99      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 27.88/3.99      | r1_tarski(X0,X1) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_109,plain,
% 27.88/3.99      ( k4_xboole_0(sK5,sK5) != k1_xboole_0
% 27.88/3.99      | r1_tarski(sK5,sK5) = iProver_top ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_107]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_33,plain,
% 27.88/3.99      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
% 27.88/3.99      inference(cnf_transformation,[],[f129]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_66,plain,
% 27.88/3.99      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) = iProver_top ),
% 27.88/3.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_68,plain,
% 27.88/3.99      ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_66]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_61,plain,
% 27.88/3.99      ( ~ r1_ordinal1(sK5,sK5)
% 27.88/3.99      | r1_tarski(sK5,sK5)
% 27.88/3.99      | ~ v3_ordinal1(sK5) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_35]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_55,plain,
% 27.88/3.99      ( r2_hidden(sK5,sK5) | ~ v3_ordinal1(sK5) | sK5 = sK5 ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_37]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_52,plain,
% 27.88/3.99      ( r1_ordinal1(sK5,sK5) | r2_hidden(sK5,sK5) | ~ v3_ordinal1(sK5) ),
% 27.88/3.99      inference(instantiation,[status(thm)],[c_38]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(contradiction,plain,
% 27.88/3.99      ( $false ),
% 27.88/3.99      inference(minisat,
% 27.88/3.99                [status(thm)],
% 27.88/3.99                [c_107964,c_107954,c_50776,c_29449,c_5174,c_136,c_111,
% 27.88/3.99                 c_109,c_68,c_61,c_55,c_52,c_42]) ).
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.88/3.99  
% 27.88/3.99  ------                               Statistics
% 27.88/3.99  
% 27.88/3.99  ------ Selected
% 27.88/3.99  
% 27.88/3.99  total_time:                             3.266
% 27.88/3.99  
%------------------------------------------------------------------------------
