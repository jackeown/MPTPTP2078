%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:53 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  174 (1178 expanded)
%              Number of clauses        :   74 ( 187 expanded)
%              Number of leaves         :   25 ( 313 expanded)
%              Depth                    :   18
%              Number of atoms          :  676 (4331 expanded)
%              Number of equality atoms :  303 (1618 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f84,f85])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f83,f113])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f82,f114])).

fof(f116,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f81,f115])).

fof(f117,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f80,f116])).

fof(f118,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f86,f117])).

fof(f125,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f118])).

fof(f138,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f125])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

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
     => ( ( ~ r1_ordinal1(X0,sK6)
          | ~ r2_hidden(X0,k1_ordinal1(sK6)) )
        & ( r1_ordinal1(X0,sK6)
          | r2_hidden(X0,k1_ordinal1(sK6)) )
        & v3_ordinal1(sK6) ) ) ),
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
          ( ( ~ r1_ordinal1(sK5,X1)
            | ~ r2_hidden(sK5,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK5,X1)
            | r2_hidden(sK5,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ r1_ordinal1(sK5,sK6)
      | ~ r2_hidden(sK5,k1_ordinal1(sK6)) )
    & ( r1_ordinal1(sK5,sK6)
      | r2_hidden(sK5,k1_ordinal1(sK6)) )
    & v3_ordinal1(sK6)
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f58,f60,f59])).

fof(f112,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f119,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f79,f117])).

fof(f120,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f103,f118,f119])).

fof(f135,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f112,f120])).

fof(f109,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f110,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f111,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f61])).

fof(f136,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f111,f120])).

fof(f33,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f52,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f52])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f53])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f156,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f92])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f141,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f102,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f126,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f118])).

fof(f139,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f126])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f134,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f71,f116])).

fof(f148,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f134])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f124,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f118])).

fof(f137,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f124])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f133,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f72,f116])).

fof(f146,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f133])).

fof(f147,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f146])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_2883,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_34,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_38,negated_conjecture,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_304,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(prop_impl,[status(thm)],[c_38])).

cnf(c_567,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_304])).

cnf(c_568,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_41,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_40,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_570,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_41,c_40])).

cnf(c_1272,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(prop_impl,[status(thm)],[c_41,c_40,c_568])).

cnf(c_2851,plain,
    ( r1_tarski(sK5,sK6) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_572,plain,
    ( r1_tarski(sK5,sK6) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_35,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_39,negated_conjecture,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_306,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(prop_impl,[status(thm)],[c_39])).

cnf(c_581,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_306])).

cnf(c_582,plain,
    ( r1_tarski(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_584,plain,
    ( r1_tarski(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_41,c_40])).

cnf(c_1274,plain,
    ( r1_tarski(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(prop_impl,[status(thm)],[c_41,c_40,c_582])).

cnf(c_2850,plain,
    ( r1_tarski(sK5,sK6) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1274])).

cnf(c_43,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X1 = X0
    | X5 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X4 = X0
    | X3 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_71,plain,
    ( ~ sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_28,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_74,plain,
    ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_109,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_111,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_586,plain,
    ( r1_tarski(sK5,sK6) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_32,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_33,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_519,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_33])).

cnf(c_520,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_3159,plain,
    ( r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK5,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_3160,plain,
    ( r1_tarski(sK5,sK6) = iProver_top
    | r2_hidden(sK5,sK6) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3159])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_3241,plain,
    ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | r2_hidden(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3242,plain,
    ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3241])).

cnf(c_2008,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3288,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,sK6)
    | sK6 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_3289,plain,
    ( sK6 != X0
    | sK5 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3288])).

cnf(c_3291,plain,
    ( sK6 != sK6
    | sK5 != sK6
    | r1_tarski(sK6,sK6) != iProver_top
    | r1_tarski(sK5,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3289])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f148])).

cnf(c_3479,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
    | sK5 = X0
    | sK5 = X1
    | sK5 = X2 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3480,plain,
    ( sK5 = X0
    | sK5 = X1
    | sK5 = X2
    | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3479])).

cnf(c_3482,plain,
    ( sK5 = sK6
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3480])).

cnf(c_3927,plain,
    ( r1_tarski(sK5,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2850,c_43,c_71,c_74,c_111,c_586,c_3160,c_3242,c_3291,c_3482])).

cnf(c_5190,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2851,c_43,c_71,c_74,c_111,c_572,c_586,c_3160,c_3242,c_3291,c_3482])).

cnf(c_5196,plain,
    ( r2_hidden(sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2883,c_5190])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_3696,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | r2_hidden(X0,k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4511,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(instantiation,[status(thm)],[c_3696])).

cnf(c_2007,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3177,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_3402,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | r2_hidden(X3,k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6))
    | X3 != X0
    | k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_3177])).

cnf(c_4330,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | r2_hidden(sK5,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5))
    | k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_3402])).

cnf(c_4332,plain,
    ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4330])).

cnf(c_36,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_536,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_36,c_35])).

cnf(c_4288,plain,
    ( r1_tarski(X0,sK5)
    | r2_hidden(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_4292,plain,
    ( r1_tarski(X0,sK5) = iProver_top
    | r2_hidden(sK5,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4288])).

cnf(c_4294,plain,
    ( r1_tarski(sK6,sK5) = iProver_top
    | r2_hidden(sK5,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4292])).

cnf(c_3929,plain,
    ( r1_tarski(sK5,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3927])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3478,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3484,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3478])).

cnf(c_3486,plain,
    ( sK5 = sK6
    | r1_tarski(sK6,sK5) != iProver_top
    | r1_tarski(sK5,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3484])).

cnf(c_2005,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_2012,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_15,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_97,plain,
    ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_42,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5196,c_4511,c_4332,c_4294,c_3929,c_3927,c_3486,c_2012,c_570,c_97,c_74,c_71,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:25:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.23/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/0.99  
% 3.23/0.99  ------  iProver source info
% 3.23/0.99  
% 3.23/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.23/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/0.99  git: non_committed_changes: false
% 3.23/0.99  git: last_make_outside_of_git: false
% 3.23/0.99  
% 3.23/0.99  ------ 
% 3.23/0.99  
% 3.23/0.99  ------ Input Options
% 3.23/0.99  
% 3.23/0.99  --out_options                           all
% 3.23/0.99  --tptp_safe_out                         true
% 3.23/0.99  --problem_path                          ""
% 3.23/0.99  --include_path                          ""
% 3.23/0.99  --clausifier                            res/vclausify_rel
% 3.23/0.99  --clausifier_options                    --mode clausify
% 3.23/0.99  --stdin                                 false
% 3.23/0.99  --stats_out                             all
% 3.23/0.99  
% 3.23/0.99  ------ General Options
% 3.23/0.99  
% 3.23/0.99  --fof                                   false
% 3.23/0.99  --time_out_real                         305.
% 3.23/0.99  --time_out_virtual                      -1.
% 3.23/0.99  --symbol_type_check                     false
% 3.23/0.99  --clausify_out                          false
% 3.23/0.99  --sig_cnt_out                           false
% 3.23/0.99  --trig_cnt_out                          false
% 3.23/0.99  --trig_cnt_out_tolerance                1.
% 3.23/0.99  --trig_cnt_out_sk_spl                   false
% 3.23/0.99  --abstr_cl_out                          false
% 3.23/0.99  
% 3.23/0.99  ------ Global Options
% 3.23/0.99  
% 3.23/0.99  --schedule                              default
% 3.23/0.99  --add_important_lit                     false
% 3.23/0.99  --prop_solver_per_cl                    1000
% 3.23/0.99  --min_unsat_core                        false
% 3.23/0.99  --soft_assumptions                      false
% 3.23/0.99  --soft_lemma_size                       3
% 3.23/0.99  --prop_impl_unit_size                   0
% 3.23/0.99  --prop_impl_unit                        []
% 3.23/0.99  --share_sel_clauses                     true
% 3.23/0.99  --reset_solvers                         false
% 3.23/0.99  --bc_imp_inh                            [conj_cone]
% 3.23/0.99  --conj_cone_tolerance                   3.
% 3.23/0.99  --extra_neg_conj                        none
% 3.23/0.99  --large_theory_mode                     true
% 3.23/0.99  --prolific_symb_bound                   200
% 3.23/0.99  --lt_threshold                          2000
% 3.23/0.99  --clause_weak_htbl                      true
% 3.23/0.99  --gc_record_bc_elim                     false
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing Options
% 3.23/0.99  
% 3.23/0.99  --preprocessing_flag                    true
% 3.23/0.99  --time_out_prep_mult                    0.1
% 3.23/0.99  --splitting_mode                        input
% 3.23/0.99  --splitting_grd                         true
% 3.23/0.99  --splitting_cvd                         false
% 3.23/0.99  --splitting_cvd_svl                     false
% 3.23/0.99  --splitting_nvd                         32
% 3.23/0.99  --sub_typing                            true
% 3.23/0.99  --prep_gs_sim                           true
% 3.23/0.99  --prep_unflatten                        true
% 3.23/0.99  --prep_res_sim                          true
% 3.23/0.99  --prep_upred                            true
% 3.23/0.99  --prep_sem_filter                       exhaustive
% 3.23/0.99  --prep_sem_filter_out                   false
% 3.23/0.99  --pred_elim                             true
% 3.23/0.99  --res_sim_input                         true
% 3.23/0.99  --eq_ax_congr_red                       true
% 3.23/0.99  --pure_diseq_elim                       true
% 3.23/0.99  --brand_transform                       false
% 3.23/0.99  --non_eq_to_eq                          false
% 3.23/0.99  --prep_def_merge                        true
% 3.23/0.99  --prep_def_merge_prop_impl              false
% 3.23/0.99  --prep_def_merge_mbd                    true
% 3.23/0.99  --prep_def_merge_tr_red                 false
% 3.23/0.99  --prep_def_merge_tr_cl                  false
% 3.23/0.99  --smt_preprocessing                     true
% 3.23/0.99  --smt_ac_axioms                         fast
% 3.23/0.99  --preprocessed_out                      false
% 3.23/0.99  --preprocessed_stats                    false
% 3.23/0.99  
% 3.23/0.99  ------ Abstraction refinement Options
% 3.23/0.99  
% 3.23/0.99  --abstr_ref                             []
% 3.23/0.99  --abstr_ref_prep                        false
% 3.23/0.99  --abstr_ref_until_sat                   false
% 3.23/0.99  --abstr_ref_sig_restrict                funpre
% 3.23/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.99  --abstr_ref_under                       []
% 3.23/0.99  
% 3.23/0.99  ------ SAT Options
% 3.23/0.99  
% 3.23/0.99  --sat_mode                              false
% 3.23/0.99  --sat_fm_restart_options                ""
% 3.23/0.99  --sat_gr_def                            false
% 3.23/0.99  --sat_epr_types                         true
% 3.23/0.99  --sat_non_cyclic_types                  false
% 3.23/0.99  --sat_finite_models                     false
% 3.23/0.99  --sat_fm_lemmas                         false
% 3.23/0.99  --sat_fm_prep                           false
% 3.23/0.99  --sat_fm_uc_incr                        true
% 3.23/0.99  --sat_out_model                         small
% 3.23/0.99  --sat_out_clauses                       false
% 3.23/0.99  
% 3.23/0.99  ------ QBF Options
% 3.23/0.99  
% 3.23/0.99  --qbf_mode                              false
% 3.23/0.99  --qbf_elim_univ                         false
% 3.23/0.99  --qbf_dom_inst                          none
% 3.23/0.99  --qbf_dom_pre_inst                      false
% 3.23/0.99  --qbf_sk_in                             false
% 3.23/0.99  --qbf_pred_elim                         true
% 3.23/0.99  --qbf_split                             512
% 3.23/0.99  
% 3.23/0.99  ------ BMC1 Options
% 3.23/0.99  
% 3.23/0.99  --bmc1_incremental                      false
% 3.23/0.99  --bmc1_axioms                           reachable_all
% 3.23/0.99  --bmc1_min_bound                        0
% 3.23/0.99  --bmc1_max_bound                        -1
% 3.23/0.99  --bmc1_max_bound_default                -1
% 3.23/0.99  --bmc1_symbol_reachability              true
% 3.23/0.99  --bmc1_property_lemmas                  false
% 3.23/0.99  --bmc1_k_induction                      false
% 3.23/0.99  --bmc1_non_equiv_states                 false
% 3.23/0.99  --bmc1_deadlock                         false
% 3.23/0.99  --bmc1_ucm                              false
% 3.23/0.99  --bmc1_add_unsat_core                   none
% 3.23/0.99  --bmc1_unsat_core_children              false
% 3.23/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/0.99  --bmc1_out_stat                         full
% 3.23/0.99  --bmc1_ground_init                      false
% 3.23/0.99  --bmc1_pre_inst_next_state              false
% 3.23/0.99  --bmc1_pre_inst_state                   false
% 3.23/0.99  --bmc1_pre_inst_reach_state             false
% 3.23/0.99  --bmc1_out_unsat_core                   false
% 3.23/0.99  --bmc1_aig_witness_out                  false
% 3.23/0.99  --bmc1_verbose                          false
% 3.23/0.99  --bmc1_dump_clauses_tptp                false
% 3.23/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.23/0.99  --bmc1_dump_file                        -
% 3.23/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.23/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.23/0.99  --bmc1_ucm_extend_mode                  1
% 3.23/0.99  --bmc1_ucm_init_mode                    2
% 3.23/0.99  --bmc1_ucm_cone_mode                    none
% 3.23/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.23/0.99  --bmc1_ucm_relax_model                  4
% 3.23/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.23/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/0.99  --bmc1_ucm_layered_model                none
% 3.23/0.99  --bmc1_ucm_max_lemma_size               10
% 3.23/0.99  
% 3.23/0.99  ------ AIG Options
% 3.23/0.99  
% 3.23/0.99  --aig_mode                              false
% 3.23/0.99  
% 3.23/0.99  ------ Instantiation Options
% 3.23/0.99  
% 3.23/0.99  --instantiation_flag                    true
% 3.23/0.99  --inst_sos_flag                         false
% 3.23/0.99  --inst_sos_phase                        true
% 3.23/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel_side                     num_symb
% 3.23/0.99  --inst_solver_per_active                1400
% 3.23/0.99  --inst_solver_calls_frac                1.
% 3.23/0.99  --inst_passive_queue_type               priority_queues
% 3.23/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/0.99  --inst_passive_queues_freq              [25;2]
% 3.23/0.99  --inst_dismatching                      true
% 3.23/0.99  --inst_eager_unprocessed_to_passive     true
% 3.23/0.99  --inst_prop_sim_given                   true
% 3.23/0.99  --inst_prop_sim_new                     false
% 3.23/0.99  --inst_subs_new                         false
% 3.23/0.99  --inst_eq_res_simp                      false
% 3.23/0.99  --inst_subs_given                       false
% 3.23/0.99  --inst_orphan_elimination               true
% 3.23/0.99  --inst_learning_loop_flag               true
% 3.23/0.99  --inst_learning_start                   3000
% 3.23/0.99  --inst_learning_factor                  2
% 3.23/0.99  --inst_start_prop_sim_after_learn       3
% 3.23/0.99  --inst_sel_renew                        solver
% 3.23/0.99  --inst_lit_activity_flag                true
% 3.23/0.99  --inst_restr_to_given                   false
% 3.23/0.99  --inst_activity_threshold               500
% 3.23/0.99  --inst_out_proof                        true
% 3.23/0.99  
% 3.23/0.99  ------ Resolution Options
% 3.23/0.99  
% 3.23/0.99  --resolution_flag                       true
% 3.23/0.99  --res_lit_sel                           adaptive
% 3.23/0.99  --res_lit_sel_side                      none
% 3.23/0.99  --res_ordering                          kbo
% 3.23/0.99  --res_to_prop_solver                    active
% 3.23/0.99  --res_prop_simpl_new                    false
% 3.23/0.99  --res_prop_simpl_given                  true
% 3.23/0.99  --res_passive_queue_type                priority_queues
% 3.23/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/0.99  --res_passive_queues_freq               [15;5]
% 3.23/0.99  --res_forward_subs                      full
% 3.23/0.99  --res_backward_subs                     full
% 3.23/0.99  --res_forward_subs_resolution           true
% 3.23/0.99  --res_backward_subs_resolution          true
% 3.23/0.99  --res_orphan_elimination                true
% 3.23/0.99  --res_time_limit                        2.
% 3.23/0.99  --res_out_proof                         true
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Options
% 3.23/0.99  
% 3.23/0.99  --superposition_flag                    true
% 3.23/0.99  --sup_passive_queue_type                priority_queues
% 3.23/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.23/0.99  --demod_completeness_check              fast
% 3.23/0.99  --demod_use_ground                      true
% 3.23/0.99  --sup_to_prop_solver                    passive
% 3.23/0.99  --sup_prop_simpl_new                    true
% 3.23/0.99  --sup_prop_simpl_given                  true
% 3.23/0.99  --sup_fun_splitting                     false
% 3.23/0.99  --sup_smt_interval                      50000
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Simplification Setup
% 3.23/0.99  
% 3.23/0.99  --sup_indices_passive                   []
% 3.23/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_full_bw                           [BwDemod]
% 3.23/0.99  --sup_immed_triv                        [TrivRules]
% 3.23/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_immed_bw_main                     []
% 3.23/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  
% 3.23/0.99  ------ Combination Options
% 3.23/0.99  
% 3.23/0.99  --comb_res_mult                         3
% 3.23/0.99  --comb_sup_mult                         2
% 3.23/0.99  --comb_inst_mult                        10
% 3.23/0.99  
% 3.23/0.99  ------ Debug Options
% 3.23/0.99  
% 3.23/0.99  --dbg_backtrace                         false
% 3.23/0.99  --dbg_dump_prop_clauses                 false
% 3.23/0.99  --dbg_dump_prop_clauses_file            -
% 3.23/0.99  --dbg_out_stat                          false
% 3.23/0.99  ------ Parsing...
% 3.23/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/0.99  ------ Proving...
% 3.23/0.99  ------ Problem Properties 
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  clauses                                 39
% 3.23/0.99  conjectures                             2
% 3.23/0.99  EPR                                     19
% 3.23/0.99  Horn                                    30
% 3.23/0.99  unary                                   15
% 3.23/0.99  binary                                  7
% 3.23/0.99  lits                                    91
% 3.23/0.99  lits eq                                 26
% 3.23/0.99  fd_pure                                 0
% 3.23/0.99  fd_pseudo                               0
% 3.23/0.99  fd_cond                                 0
% 3.23/0.99  fd_pseudo_cond                          10
% 3.23/0.99  AC symbols                              0
% 3.23/0.99  
% 3.23/0.99  ------ Schedule dynamic 5 is on 
% 3.23/0.99  
% 3.23/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  ------ 
% 3.23/0.99  Current options:
% 3.23/0.99  ------ 
% 3.23/0.99  
% 3.23/0.99  ------ Input Options
% 3.23/0.99  
% 3.23/0.99  --out_options                           all
% 3.23/0.99  --tptp_safe_out                         true
% 3.23/0.99  --problem_path                          ""
% 3.23/0.99  --include_path                          ""
% 3.23/0.99  --clausifier                            res/vclausify_rel
% 3.23/0.99  --clausifier_options                    --mode clausify
% 3.23/0.99  --stdin                                 false
% 3.23/0.99  --stats_out                             all
% 3.23/0.99  
% 3.23/0.99  ------ General Options
% 3.23/0.99  
% 3.23/0.99  --fof                                   false
% 3.23/0.99  --time_out_real                         305.
% 3.23/0.99  --time_out_virtual                      -1.
% 3.23/0.99  --symbol_type_check                     false
% 3.23/0.99  --clausify_out                          false
% 3.23/0.99  --sig_cnt_out                           false
% 3.23/0.99  --trig_cnt_out                          false
% 3.23/0.99  --trig_cnt_out_tolerance                1.
% 3.23/0.99  --trig_cnt_out_sk_spl                   false
% 3.23/0.99  --abstr_cl_out                          false
% 3.23/0.99  
% 3.23/0.99  ------ Global Options
% 3.23/0.99  
% 3.23/0.99  --schedule                              default
% 3.23/0.99  --add_important_lit                     false
% 3.23/0.99  --prop_solver_per_cl                    1000
% 3.23/0.99  --min_unsat_core                        false
% 3.23/0.99  --soft_assumptions                      false
% 3.23/0.99  --soft_lemma_size                       3
% 3.23/0.99  --prop_impl_unit_size                   0
% 3.23/0.99  --prop_impl_unit                        []
% 3.23/0.99  --share_sel_clauses                     true
% 3.23/0.99  --reset_solvers                         false
% 3.23/0.99  --bc_imp_inh                            [conj_cone]
% 3.23/0.99  --conj_cone_tolerance                   3.
% 3.23/0.99  --extra_neg_conj                        none
% 3.23/0.99  --large_theory_mode                     true
% 3.23/0.99  --prolific_symb_bound                   200
% 3.23/0.99  --lt_threshold                          2000
% 3.23/0.99  --clause_weak_htbl                      true
% 3.23/0.99  --gc_record_bc_elim                     false
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing Options
% 3.23/0.99  
% 3.23/0.99  --preprocessing_flag                    true
% 3.23/0.99  --time_out_prep_mult                    0.1
% 3.23/0.99  --splitting_mode                        input
% 3.23/0.99  --splitting_grd                         true
% 3.23/0.99  --splitting_cvd                         false
% 3.23/0.99  --splitting_cvd_svl                     false
% 3.23/0.99  --splitting_nvd                         32
% 3.23/0.99  --sub_typing                            true
% 3.23/0.99  --prep_gs_sim                           true
% 3.23/0.99  --prep_unflatten                        true
% 3.23/0.99  --prep_res_sim                          true
% 3.23/0.99  --prep_upred                            true
% 3.23/0.99  --prep_sem_filter                       exhaustive
% 3.23/0.99  --prep_sem_filter_out                   false
% 3.23/0.99  --pred_elim                             true
% 3.23/0.99  --res_sim_input                         true
% 3.23/0.99  --eq_ax_congr_red                       true
% 3.23/0.99  --pure_diseq_elim                       true
% 3.23/0.99  --brand_transform                       false
% 3.23/0.99  --non_eq_to_eq                          false
% 3.23/0.99  --prep_def_merge                        true
% 3.23/0.99  --prep_def_merge_prop_impl              false
% 3.23/0.99  --prep_def_merge_mbd                    true
% 3.23/0.99  --prep_def_merge_tr_red                 false
% 3.23/0.99  --prep_def_merge_tr_cl                  false
% 3.23/0.99  --smt_preprocessing                     true
% 3.23/0.99  --smt_ac_axioms                         fast
% 3.23/0.99  --preprocessed_out                      false
% 3.23/0.99  --preprocessed_stats                    false
% 3.23/0.99  
% 3.23/0.99  ------ Abstraction refinement Options
% 3.23/0.99  
% 3.23/0.99  --abstr_ref                             []
% 3.23/0.99  --abstr_ref_prep                        false
% 3.23/0.99  --abstr_ref_until_sat                   false
% 3.23/0.99  --abstr_ref_sig_restrict                funpre
% 3.23/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.99  --abstr_ref_under                       []
% 3.23/0.99  
% 3.23/0.99  ------ SAT Options
% 3.23/0.99  
% 3.23/0.99  --sat_mode                              false
% 3.23/0.99  --sat_fm_restart_options                ""
% 3.23/0.99  --sat_gr_def                            false
% 3.23/0.99  --sat_epr_types                         true
% 3.23/0.99  --sat_non_cyclic_types                  false
% 3.23/0.99  --sat_finite_models                     false
% 3.23/0.99  --sat_fm_lemmas                         false
% 3.23/0.99  --sat_fm_prep                           false
% 3.23/0.99  --sat_fm_uc_incr                        true
% 3.23/0.99  --sat_out_model                         small
% 3.23/0.99  --sat_out_clauses                       false
% 3.23/0.99  
% 3.23/0.99  ------ QBF Options
% 3.23/0.99  
% 3.23/0.99  --qbf_mode                              false
% 3.23/0.99  --qbf_elim_univ                         false
% 3.23/0.99  --qbf_dom_inst                          none
% 3.23/0.99  --qbf_dom_pre_inst                      false
% 3.23/0.99  --qbf_sk_in                             false
% 3.23/0.99  --qbf_pred_elim                         true
% 3.23/0.99  --qbf_split                             512
% 3.23/0.99  
% 3.23/0.99  ------ BMC1 Options
% 3.23/0.99  
% 3.23/0.99  --bmc1_incremental                      false
% 3.23/0.99  --bmc1_axioms                           reachable_all
% 3.23/0.99  --bmc1_min_bound                        0
% 3.23/0.99  --bmc1_max_bound                        -1
% 3.23/0.99  --bmc1_max_bound_default                -1
% 3.23/0.99  --bmc1_symbol_reachability              true
% 3.23/0.99  --bmc1_property_lemmas                  false
% 3.23/0.99  --bmc1_k_induction                      false
% 3.23/0.99  --bmc1_non_equiv_states                 false
% 3.23/0.99  --bmc1_deadlock                         false
% 3.23/0.99  --bmc1_ucm                              false
% 3.23/0.99  --bmc1_add_unsat_core                   none
% 3.23/0.99  --bmc1_unsat_core_children              false
% 3.23/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/0.99  --bmc1_out_stat                         full
% 3.23/0.99  --bmc1_ground_init                      false
% 3.23/0.99  --bmc1_pre_inst_next_state              false
% 3.23/0.99  --bmc1_pre_inst_state                   false
% 3.23/0.99  --bmc1_pre_inst_reach_state             false
% 3.23/0.99  --bmc1_out_unsat_core                   false
% 3.23/0.99  --bmc1_aig_witness_out                  false
% 3.23/0.99  --bmc1_verbose                          false
% 3.23/0.99  --bmc1_dump_clauses_tptp                false
% 3.23/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.23/0.99  --bmc1_dump_file                        -
% 3.23/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.23/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.23/0.99  --bmc1_ucm_extend_mode                  1
% 3.23/0.99  --bmc1_ucm_init_mode                    2
% 3.23/0.99  --bmc1_ucm_cone_mode                    none
% 3.23/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.23/0.99  --bmc1_ucm_relax_model                  4
% 3.23/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.23/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/0.99  --bmc1_ucm_layered_model                none
% 3.23/0.99  --bmc1_ucm_max_lemma_size               10
% 3.23/0.99  
% 3.23/0.99  ------ AIG Options
% 3.23/0.99  
% 3.23/0.99  --aig_mode                              false
% 3.23/0.99  
% 3.23/0.99  ------ Instantiation Options
% 3.23/0.99  
% 3.23/0.99  --instantiation_flag                    true
% 3.23/0.99  --inst_sos_flag                         false
% 3.23/0.99  --inst_sos_phase                        true
% 3.23/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel_side                     none
% 3.23/0.99  --inst_solver_per_active                1400
% 3.23/0.99  --inst_solver_calls_frac                1.
% 3.23/0.99  --inst_passive_queue_type               priority_queues
% 3.23/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/0.99  --inst_passive_queues_freq              [25;2]
% 3.23/0.99  --inst_dismatching                      true
% 3.23/0.99  --inst_eager_unprocessed_to_passive     true
% 3.23/0.99  --inst_prop_sim_given                   true
% 3.23/0.99  --inst_prop_sim_new                     false
% 3.23/0.99  --inst_subs_new                         false
% 3.23/0.99  --inst_eq_res_simp                      false
% 3.23/0.99  --inst_subs_given                       false
% 3.23/0.99  --inst_orphan_elimination               true
% 3.23/0.99  --inst_learning_loop_flag               true
% 3.23/0.99  --inst_learning_start                   3000
% 3.23/0.99  --inst_learning_factor                  2
% 3.23/0.99  --inst_start_prop_sim_after_learn       3
% 3.23/0.99  --inst_sel_renew                        solver
% 3.23/0.99  --inst_lit_activity_flag                true
% 3.23/0.99  --inst_restr_to_given                   false
% 3.23/0.99  --inst_activity_threshold               500
% 3.23/0.99  --inst_out_proof                        true
% 3.23/0.99  
% 3.23/0.99  ------ Resolution Options
% 3.23/0.99  
% 3.23/0.99  --resolution_flag                       false
% 3.23/0.99  --res_lit_sel                           adaptive
% 3.23/0.99  --res_lit_sel_side                      none
% 3.23/0.99  --res_ordering                          kbo
% 3.23/0.99  --res_to_prop_solver                    active
% 3.23/0.99  --res_prop_simpl_new                    false
% 3.23/0.99  --res_prop_simpl_given                  true
% 3.23/0.99  --res_passive_queue_type                priority_queues
% 3.23/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/0.99  --res_passive_queues_freq               [15;5]
% 3.23/0.99  --res_forward_subs                      full
% 3.23/0.99  --res_backward_subs                     full
% 3.23/0.99  --res_forward_subs_resolution           true
% 3.23/0.99  --res_backward_subs_resolution          true
% 3.23/0.99  --res_orphan_elimination                true
% 3.23/0.99  --res_time_limit                        2.
% 3.23/0.99  --res_out_proof                         true
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Options
% 3.23/0.99  
% 3.23/0.99  --superposition_flag                    true
% 3.23/0.99  --sup_passive_queue_type                priority_queues
% 3.23/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.23/0.99  --demod_completeness_check              fast
% 3.23/0.99  --demod_use_ground                      true
% 3.23/0.99  --sup_to_prop_solver                    passive
% 3.23/0.99  --sup_prop_simpl_new                    true
% 3.23/0.99  --sup_prop_simpl_given                  true
% 3.23/0.99  --sup_fun_splitting                     false
% 3.23/0.99  --sup_smt_interval                      50000
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Simplification Setup
% 3.23/0.99  
% 3.23/0.99  --sup_indices_passive                   []
% 3.23/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_full_bw                           [BwDemod]
% 3.23/0.99  --sup_immed_triv                        [TrivRules]
% 3.23/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_immed_bw_main                     []
% 3.23/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  
% 3.23/0.99  ------ Combination Options
% 3.23/0.99  
% 3.23/0.99  --comb_res_mult                         3
% 3.23/0.99  --comb_sup_mult                         2
% 3.23/0.99  --comb_inst_mult                        10
% 3.23/0.99  
% 3.23/0.99  ------ Debug Options
% 3.23/0.99  
% 3.23/0.99  --dbg_backtrace                         false
% 3.23/0.99  --dbg_dump_prop_clauses                 false
% 3.23/0.99  --dbg_dump_prop_clauses_file            -
% 3.23/0.99  --dbg_out_stat                          false
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  ------ Proving...
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  % SZS status Theorem for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  fof(f1,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f36,plain,(
% 3.23/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.23/0.99    inference(nnf_transformation,[],[f1])).
% 3.23/0.99  
% 3.23/0.99  fof(f37,plain,(
% 3.23/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.23/0.99    inference(flattening,[],[f36])).
% 3.23/0.99  
% 3.23/0.99  fof(f38,plain,(
% 3.23/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.23/0.99    inference(rectify,[],[f37])).
% 3.23/0.99  
% 3.23/0.99  fof(f39,plain,(
% 3.23/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.23/0.99    introduced(choice_axiom,[])).
% 3.23/0.99  
% 3.23/0.99  fof(f40,plain,(
% 3.23/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.23/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 3.23/0.99  
% 3.23/0.99  fof(f63,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.23/0.99    inference(cnf_transformation,[],[f40])).
% 3.23/0.99  
% 3.23/0.99  fof(f11,axiom,(
% 3.23/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f86,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f11])).
% 3.23/0.99  
% 3.23/0.99  fof(f5,axiom,(
% 3.23/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f80,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f5])).
% 3.23/0.99  
% 3.23/0.99  fof(f6,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f81,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f6])).
% 3.23/0.99  
% 3.23/0.99  fof(f7,axiom,(
% 3.23/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f82,plain,(
% 3.23/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f7])).
% 3.23/0.99  
% 3.23/0.99  fof(f8,axiom,(
% 3.23/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f83,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f8])).
% 3.23/0.99  
% 3.23/0.99  fof(f9,axiom,(
% 3.23/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f84,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f9])).
% 3.23/0.99  
% 3.23/0.99  fof(f10,axiom,(
% 3.23/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f85,plain,(
% 3.23/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f10])).
% 3.23/0.99  
% 3.23/0.99  fof(f113,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f84,f85])).
% 3.23/0.99  
% 3.23/0.99  fof(f114,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f83,f113])).
% 3.23/0.99  
% 3.23/0.99  fof(f115,plain,(
% 3.23/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f82,f114])).
% 3.23/0.99  
% 3.23/0.99  fof(f116,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f81,f115])).
% 3.23/0.99  
% 3.23/0.99  fof(f117,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f80,f116])).
% 3.23/0.99  
% 3.23/0.99  fof(f118,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.23/0.99    inference(definition_unfolding,[],[f86,f117])).
% 3.23/0.99  
% 3.23/0.99  fof(f125,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.23/0.99    inference(definition_unfolding,[],[f63,f118])).
% 3.23/0.99  
% 3.23/0.99  fof(f138,plain,(
% 3.23/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 3.23/0.99    inference(equality_resolution,[],[f125])).
% 3.23/0.99  
% 3.23/0.99  fof(f16,axiom,(
% 3.23/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f27,plain,(
% 3.23/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.23/0.99    inference(ennf_transformation,[],[f16])).
% 3.23/0.99  
% 3.23/0.99  fof(f28,plain,(
% 3.23/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.23/0.99    inference(flattening,[],[f27])).
% 3.23/0.99  
% 3.23/0.99  fof(f56,plain,(
% 3.23/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.23/0.99    inference(nnf_transformation,[],[f28])).
% 3.23/0.99  
% 3.23/0.99  fof(f106,plain,(
% 3.23/0.99    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f56])).
% 3.23/0.99  
% 3.23/0.99  fof(f19,conjecture,(
% 3.23/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f20,negated_conjecture,(
% 3.23/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.23/0.99    inference(negated_conjecture,[],[f19])).
% 3.23/0.99  
% 3.23/0.99  fof(f32,plain,(
% 3.23/0.99    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f20])).
% 3.23/0.99  
% 3.23/0.99  fof(f57,plain,(
% 3.23/0.99    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.23/0.99    inference(nnf_transformation,[],[f32])).
% 3.23/0.99  
% 3.23/0.99  fof(f58,plain,(
% 3.23/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.23/0.99    inference(flattening,[],[f57])).
% 3.23/0.99  
% 3.23/0.99  fof(f60,plain,(
% 3.23/0.99    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK6) | ~r2_hidden(X0,k1_ordinal1(sK6))) & (r1_ordinal1(X0,sK6) | r2_hidden(X0,k1_ordinal1(sK6))) & v3_ordinal1(sK6))) )),
% 3.23/0.99    introduced(choice_axiom,[])).
% 3.23/0.99  
% 3.23/0.99  fof(f59,plain,(
% 3.23/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK5,X1) | ~r2_hidden(sK5,k1_ordinal1(X1))) & (r1_ordinal1(sK5,X1) | r2_hidden(sK5,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK5))),
% 3.23/0.99    introduced(choice_axiom,[])).
% 3.23/0.99  
% 3.23/0.99  fof(f61,plain,(
% 3.23/0.99    ((~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))) & (r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))) & v3_ordinal1(sK6)) & v3_ordinal1(sK5)),
% 3.23/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f58,f60,f59])).
% 3.23/0.99  
% 3.23/0.99  fof(f112,plain,(
% 3.23/0.99    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))),
% 3.23/0.99    inference(cnf_transformation,[],[f61])).
% 3.23/0.99  
% 3.23/0.99  fof(f14,axiom,(
% 3.23/0.99    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f103,plain,(
% 3.23/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f14])).
% 3.23/0.99  
% 3.23/0.99  fof(f4,axiom,(
% 3.23/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f79,plain,(
% 3.23/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f4])).
% 3.23/0.99  
% 3.23/0.99  fof(f119,plain,(
% 3.23/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f79,f117])).
% 3.23/0.99  
% 3.23/0.99  fof(f120,plain,(
% 3.23/0.99    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f103,f118,f119])).
% 3.23/0.99  
% 3.23/0.99  fof(f135,plain,(
% 3.23/0.99    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 3.23/0.99    inference(definition_unfolding,[],[f112,f120])).
% 3.23/0.99  
% 3.23/0.99  fof(f109,plain,(
% 3.23/0.99    v3_ordinal1(sK5)),
% 3.23/0.99    inference(cnf_transformation,[],[f61])).
% 3.23/0.99  
% 3.23/0.99  fof(f110,plain,(
% 3.23/0.99    v3_ordinal1(sK6)),
% 3.23/0.99    inference(cnf_transformation,[],[f61])).
% 3.23/0.99  
% 3.23/0.99  fof(f105,plain,(
% 3.23/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f56])).
% 3.23/0.99  
% 3.23/0.99  fof(f111,plain,(
% 3.23/0.99    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))),
% 3.23/0.99    inference(cnf_transformation,[],[f61])).
% 3.23/0.99  
% 3.23/0.99  fof(f136,plain,(
% 3.23/0.99    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 3.23/0.99    inference(definition_unfolding,[],[f111,f120])).
% 3.23/0.99  
% 3.23/0.99  fof(f33,plain,(
% 3.23/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 3.23/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.23/0.99  
% 3.23/0.99  fof(f52,plain,(
% 3.23/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.23/0.99    inference(nnf_transformation,[],[f33])).
% 3.23/0.99  
% 3.23/0.99  fof(f53,plain,(
% 3.23/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.23/0.99    inference(flattening,[],[f52])).
% 3.23/0.99  
% 3.23/0.99  fof(f54,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.23/0.99    inference(rectify,[],[f53])).
% 3.23/0.99  
% 3.23/0.99  fof(f91,plain,(
% 3.23/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f54])).
% 3.23/0.99  
% 3.23/0.99  fof(f92,plain,(
% 3.23/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 3.23/0.99    inference(cnf_transformation,[],[f54])).
% 3.23/0.99  
% 3.23/0.99  fof(f156,plain,(
% 3.23/0.99    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.23/0.99    inference(equality_resolution,[],[f92])).
% 3.23/0.99  
% 3.23/0.99  fof(f2,axiom,(
% 3.23/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f41,plain,(
% 3.23/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/0.99    inference(nnf_transformation,[],[f2])).
% 3.23/0.99  
% 3.23/0.99  fof(f42,plain,(
% 3.23/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/0.99    inference(flattening,[],[f41])).
% 3.23/0.99  
% 3.23/0.99  fof(f68,plain,(
% 3.23/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.23/0.99    inference(cnf_transformation,[],[f42])).
% 3.23/0.99  
% 3.23/0.99  fof(f141,plain,(
% 3.23/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.23/0.99    inference(equality_resolution,[],[f68])).
% 3.23/0.99  
% 3.23/0.99  fof(f13,axiom,(
% 3.23/0.99    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f22,plain,(
% 3.23/0.99    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 3.23/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.23/0.99  
% 3.23/0.99  fof(f25,plain,(
% 3.23/0.99    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f22])).
% 3.23/0.99  
% 3.23/0.99  fof(f102,plain,(
% 3.23/0.99    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f25])).
% 3.23/0.99  
% 3.23/0.99  fof(f15,axiom,(
% 3.23/0.99    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f21,plain,(
% 3.23/0.99    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.23/0.99    inference(unused_predicate_definition_removal,[],[f15])).
% 3.23/0.99  
% 3.23/0.99  fof(f26,plain,(
% 3.23/0.99    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f21])).
% 3.23/0.99  
% 3.23/0.99  fof(f104,plain,(
% 3.23/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f26])).
% 3.23/0.99  
% 3.23/0.99  fof(f62,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.23/0.99    inference(cnf_transformation,[],[f40])).
% 3.23/0.99  
% 3.23/0.99  fof(f126,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.23/0.99    inference(definition_unfolding,[],[f62,f118])).
% 3.23/0.99  
% 3.23/0.99  fof(f139,plain,(
% 3.23/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.23/0.99    inference(equality_resolution,[],[f126])).
% 3.23/0.99  
% 3.23/0.99  fof(f3,axiom,(
% 3.23/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f23,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.23/0.99    inference(ennf_transformation,[],[f3])).
% 3.23/0.99  
% 3.23/0.99  fof(f43,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.23/0.99    inference(nnf_transformation,[],[f23])).
% 3.23/0.99  
% 3.23/0.99  fof(f44,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.23/0.99    inference(flattening,[],[f43])).
% 3.23/0.99  
% 3.23/0.99  fof(f45,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.23/0.99    inference(rectify,[],[f44])).
% 3.23/0.99  
% 3.23/0.99  fof(f46,plain,(
% 3.23/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 3.23/0.99    introduced(choice_axiom,[])).
% 3.23/0.99  
% 3.23/0.99  fof(f47,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.23/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 3.23/0.99  
% 3.23/0.99  fof(f71,plain,(
% 3.23/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.23/0.99    inference(cnf_transformation,[],[f47])).
% 3.23/0.99  
% 3.23/0.99  fof(f134,plain,(
% 3.23/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.23/0.99    inference(definition_unfolding,[],[f71,f116])).
% 3.23/0.99  
% 3.23/0.99  fof(f148,plain,(
% 3.23/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 3.23/0.99    inference(equality_resolution,[],[f134])).
% 3.23/0.99  
% 3.23/0.99  fof(f64,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.23/0.99    inference(cnf_transformation,[],[f40])).
% 3.23/0.99  
% 3.23/0.99  fof(f124,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.23/0.99    inference(definition_unfolding,[],[f64,f118])).
% 3.23/0.99  
% 3.23/0.99  fof(f137,plain,(
% 3.23/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.23/0.99    inference(equality_resolution,[],[f124])).
% 3.23/0.99  
% 3.23/0.99  fof(f17,axiom,(
% 3.23/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f29,plain,(
% 3.23/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f17])).
% 3.23/0.99  
% 3.23/0.99  fof(f30,plain,(
% 3.23/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.23/0.99    inference(flattening,[],[f29])).
% 3.23/0.99  
% 3.23/0.99  fof(f107,plain,(
% 3.23/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f30])).
% 3.23/0.99  
% 3.23/0.99  fof(f70,plain,(
% 3.23/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f42])).
% 3.23/0.99  
% 3.23/0.99  fof(f72,plain,(
% 3.23/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.23/0.99    inference(cnf_transformation,[],[f47])).
% 3.23/0.99  
% 3.23/0.99  fof(f133,plain,(
% 3.23/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.23/0.99    inference(definition_unfolding,[],[f72,f116])).
% 3.23/0.99  
% 3.23/0.99  fof(f146,plain,(
% 3.23/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 3.23/0.99    inference(equality_resolution,[],[f133])).
% 3.23/0.99  
% 3.23/0.99  fof(f147,plain,(
% 3.23/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 3.23/0.99    inference(equality_resolution,[],[f146])).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,X1)
% 3.23/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f138]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2883,plain,
% 3.23/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.23/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_34,plain,
% 3.23/0.99      ( r1_ordinal1(X0,X1)
% 3.23/0.99      | ~ r1_tarski(X0,X1)
% 3.23/0.99      | ~ v3_ordinal1(X0)
% 3.23/0.99      | ~ v3_ordinal1(X1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_38,negated_conjecture,
% 3.23/0.99      ( ~ r1_ordinal1(sK5,sK6)
% 3.23/0.99      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f135]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_304,plain,
% 3.23/0.99      ( ~ r1_ordinal1(sK5,sK6)
% 3.23/0.99      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.23/0.99      inference(prop_impl,[status(thm)],[c_38]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_567,plain,
% 3.23/0.99      ( ~ r1_tarski(X0,X1)
% 3.23/0.99      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.23/0.99      | ~ v3_ordinal1(X0)
% 3.23/0.99      | ~ v3_ordinal1(X1)
% 3.23/0.99      | sK6 != X1
% 3.23/0.99      | sK5 != X0 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_34,c_304]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_568,plain,
% 3.23/0.99      ( ~ r1_tarski(sK5,sK6)
% 3.23/0.99      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.23/0.99      | ~ v3_ordinal1(sK6)
% 3.23/0.99      | ~ v3_ordinal1(sK5) ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_567]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_41,negated_conjecture,
% 3.23/0.99      ( v3_ordinal1(sK5) ),
% 3.23/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_40,negated_conjecture,
% 3.23/0.99      ( v3_ordinal1(sK6) ),
% 3.23/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_570,plain,
% 3.23/0.99      ( ~ r1_tarski(sK5,sK6)
% 3.23/0.99      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_568,c_41,c_40]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1272,plain,
% 3.23/0.99      ( ~ r1_tarski(sK5,sK6)
% 3.23/0.99      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.23/0.99      inference(prop_impl,[status(thm)],[c_41,c_40,c_568]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2851,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6) != iProver_top
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_572,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6) != iProver_top
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_570]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_35,plain,
% 3.23/0.99      ( ~ r1_ordinal1(X0,X1)
% 3.23/0.99      | r1_tarski(X0,X1)
% 3.23/0.99      | ~ v3_ordinal1(X0)
% 3.23/0.99      | ~ v3_ordinal1(X1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_39,negated_conjecture,
% 3.23/0.99      ( r1_ordinal1(sK5,sK6)
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f136]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_306,plain,
% 3.23/0.99      ( r1_ordinal1(sK5,sK6)
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.23/0.99      inference(prop_impl,[status(thm)],[c_39]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_581,plain,
% 3.23/0.99      ( r1_tarski(X0,X1)
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.23/0.99      | ~ v3_ordinal1(X0)
% 3.23/0.99      | ~ v3_ordinal1(X1)
% 3.23/0.99      | sK6 != X1
% 3.23/0.99      | sK5 != X0 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_306]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_582,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6)
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.23/0.99      | ~ v3_ordinal1(sK6)
% 3.23/0.99      | ~ v3_ordinal1(sK5) ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_581]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_584,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6)
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_582,c_41,c_40]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1274,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6)
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.23/0.99      inference(prop_impl,[status(thm)],[c_41,c_40,c_582]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2850,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6) = iProver_top
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_1274]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_43,plain,
% 3.23/0.99      ( v3_ordinal1(sK6) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_29,plain,
% 3.23/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.23/0.99      | X1 = X0
% 3.23/0.99      | X5 = X0
% 3.23/0.99      | X8 = X0
% 3.23/0.99      | X7 = X0
% 3.23/0.99      | X6 = X0
% 3.23/0.99      | X4 = X0
% 3.23/0.99      | X3 = X0
% 3.23/0.99      | X2 = X0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_71,plain,
% 3.23/0.99      ( ~ sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) | sK6 = sK6 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_28,plain,
% 3.23/0.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f156]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_74,plain,
% 3.23/0.99      ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_8,plain,
% 3.23/0.99      ( r1_tarski(X0,X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f141]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_109,plain,
% 3.23/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_111,plain,
% 3.23/0.99      ( r1_tarski(sK6,sK6) = iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_109]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_586,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6) = iProver_top
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_32,plain,
% 3.23/0.99      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_33,plain,
% 3.23/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_519,plain,
% 3.23/0.99      ( r1_tarski(X0,X1)
% 3.23/0.99      | ~ r2_hidden(X0,X1)
% 3.23/0.99      | ~ v3_ordinal1(X2)
% 3.23/0.99      | X1 != X2 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_33]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_520,plain,
% 3.23/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_519]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3159,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6) | ~ r2_hidden(sK5,sK6) | ~ v3_ordinal1(sK6) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_520]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3160,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6) = iProver_top
% 3.23/0.99      | r2_hidden(sK5,sK6) != iProver_top
% 3.23/0.99      | v3_ordinal1(sK6) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_3159]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5,plain,
% 3.23/0.99      ( r2_hidden(X0,X1)
% 3.23/0.99      | r2_hidden(X0,X2)
% 3.23/0.99      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f139]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3241,plain,
% 3.23/0.99      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.23/0.99      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.23/0.99      | r2_hidden(sK5,sK6) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3242,plain,
% 3.23/0.99      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top
% 3.23/0.99      | r2_hidden(sK5,sK6) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_3241]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2008,plain,
% 3.23/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.23/0.99      theory(equality) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3288,plain,
% 3.23/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK5,sK6) | sK6 != X1 | sK5 != X0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_2008]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3289,plain,
% 3.23/0.99      ( sK6 != X0
% 3.23/0.99      | sK5 != X1
% 3.23/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.23/0.99      | r1_tarski(sK5,sK6) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_3288]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3291,plain,
% 3.23/0.99      ( sK6 != sK6
% 3.23/0.99      | sK5 != sK6
% 3.23/0.99      | r1_tarski(sK6,sK6) != iProver_top
% 3.23/0.99      | r1_tarski(sK5,sK6) = iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_3289]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_16,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 3.23/0.99      | X0 = X1
% 3.23/0.99      | X0 = X2
% 3.23/0.99      | X0 = X3 ),
% 3.23/0.99      inference(cnf_transformation,[],[f148]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3479,plain,
% 3.23/0.99      ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
% 3.23/0.99      | sK5 = X0
% 3.23/0.99      | sK5 = X1
% 3.23/0.99      | sK5 = X2 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3480,plain,
% 3.23/0.99      ( sK5 = X0
% 3.23/0.99      | sK5 = X1
% 3.23/0.99      | sK5 = X2
% 3.23/0.99      | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_3479]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3482,plain,
% 3.23/0.99      ( sK5 = sK6
% 3.23/0.99      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_3480]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3927,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6) = iProver_top ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_2850,c_43,c_71,c_74,c_111,c_586,c_3160,c_3242,c_3291,
% 3.23/0.99                 c_3482]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5190,plain,
% 3.23/0.99      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_2851,c_43,c_71,c_74,c_111,c_572,c_586,c_3160,c_3242,
% 3.23/0.99                 c_3291,c_3482]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5196,plain,
% 3.23/0.99      ( r2_hidden(sK5,sK6) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_2883,c_5190]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,X1)
% 3.23/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f137]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3696,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 3.23/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4511,plain,
% 3.23/0.99      ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.23/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_3696]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2007,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.23/0.99      theory(equality) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3177,plain,
% 3.23/0.99      ( r2_hidden(X0,X1)
% 3.23/0.99      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
% 3.23/0.99      | X0 != X2
% 3.23/0.99      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_2007]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3402,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
% 3.23/0.99      | r2_hidden(X3,k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6))
% 3.23/0.99      | X3 != X0
% 3.23/0.99      | k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X6) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_3177]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4330,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
% 3.23/0.99      | r2_hidden(sK5,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5))
% 3.23/0.99      | k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)
% 3.23/0.99      | sK5 != X0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_3402]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4332,plain,
% 3.23/0.99      ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.23/0.99      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.23/0.99      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 3.23/0.99      | sK5 != sK6 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_4330]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_36,plain,
% 3.23/0.99      ( r1_ordinal1(X0,X1)
% 3.23/0.99      | r2_hidden(X1,X0)
% 3.23/0.99      | ~ v3_ordinal1(X0)
% 3.23/0.99      | ~ v3_ordinal1(X1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_536,plain,
% 3.23/0.99      ( r1_tarski(X0,X1)
% 3.23/0.99      | r2_hidden(X1,X0)
% 3.23/0.99      | ~ v3_ordinal1(X0)
% 3.23/0.99      | ~ v3_ordinal1(X1) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_36,c_35]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4288,plain,
% 3.23/0.99      ( r1_tarski(X0,sK5)
% 3.23/0.99      | r2_hidden(sK5,X0)
% 3.23/0.99      | ~ v3_ordinal1(X0)
% 3.23/0.99      | ~ v3_ordinal1(sK5) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4292,plain,
% 3.23/0.99      ( r1_tarski(X0,sK5) = iProver_top
% 3.23/0.99      | r2_hidden(sK5,X0) = iProver_top
% 3.23/0.99      | v3_ordinal1(X0) != iProver_top
% 3.23/0.99      | v3_ordinal1(sK5) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_4288]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4294,plain,
% 3.23/0.99      ( r1_tarski(sK6,sK5) = iProver_top
% 3.23/0.99      | r2_hidden(sK5,sK6) = iProver_top
% 3.23/0.99      | v3_ordinal1(sK6) != iProver_top
% 3.23/0.99      | v3_ordinal1(sK5) != iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_4292]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3929,plain,
% 3.23/0.99      ( r1_tarski(sK5,sK6) ),
% 3.23/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3927]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6,plain,
% 3.23/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.23/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3478,plain,
% 3.23/0.99      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3484,plain,
% 3.23/0.99      ( sK5 = X0
% 3.23/0.99      | r1_tarski(X0,sK5) != iProver_top
% 3.23/0.99      | r1_tarski(sK5,X0) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_3478]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3486,plain,
% 3.23/0.99      ( sK5 = sK6
% 3.23/0.99      | r1_tarski(sK6,sK5) != iProver_top
% 3.23/0.99      | r1_tarski(sK5,sK6) != iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_3484]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2005,plain,
% 3.23/0.99      ( X0 != X1
% 3.23/0.99      | X2 != X3
% 3.23/0.99      | X4 != X5
% 3.23/0.99      | X6 != X7
% 3.23/0.99      | X8 != X9
% 3.23/0.99      | X10 != X11
% 3.23/0.99      | X12 != X13
% 3.23/0.99      | X14 != X15
% 3.23/0.99      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 3.23/0.99      theory(equality) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2012,plain,
% 3.23/0.99      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 3.23/0.99      | sK6 != sK6 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_2005]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_15,plain,
% 3.23/0.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 3.23/0.99      inference(cnf_transformation,[],[f147]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_97,plain,
% 3.23/0.99      ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_42,plain,
% 3.23/0.99      ( v3_ordinal1(sK5) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(contradiction,plain,
% 3.23/0.99      ( $false ),
% 3.23/0.99      inference(minisat,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_5196,c_4511,c_4332,c_4294,c_3929,c_3927,c_3486,c_2012,
% 3.23/0.99                 c_570,c_97,c_74,c_71,c_43,c_42]) ).
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  ------                               Statistics
% 3.23/0.99  
% 3.23/0.99  ------ General
% 3.23/0.99  
% 3.23/0.99  abstr_ref_over_cycles:                  0
% 3.23/0.99  abstr_ref_under_cycles:                 0
% 3.23/0.99  gc_basic_clause_elim:                   0
% 3.23/0.99  forced_gc_time:                         0
% 3.23/0.99  parsing_time:                           0.012
% 3.23/0.99  unif_index_cands_time:                  0.
% 3.23/0.99  unif_index_add_time:                    0.
% 3.23/0.99  orderings_time:                         0.
% 3.23/0.99  out_proof_time:                         0.013
% 3.23/0.99  total_time:                             0.217
% 3.23/0.99  num_of_symbols:                         42
% 3.23/0.99  num_of_terms:                           5009
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing
% 3.23/0.99  
% 3.23/0.99  num_of_splits:                          0
% 3.23/0.99  num_of_split_atoms:                     0
% 3.23/0.99  num_of_reused_defs:                     0
% 3.23/0.99  num_eq_ax_congr_red:                    99
% 3.23/0.99  num_of_sem_filtered_clauses:            1
% 3.23/0.99  num_of_subtypes:                        0
% 3.23/0.99  monotx_restored_types:                  0
% 3.23/0.99  sat_num_of_epr_types:                   0
% 3.23/0.99  sat_num_of_non_cyclic_types:            0
% 3.23/0.99  sat_guarded_non_collapsed_types:        0
% 3.23/0.99  num_pure_diseq_elim:                    0
% 3.23/0.99  simp_replaced_by:                       0
% 3.23/0.99  res_preprocessed:                       177
% 3.23/0.99  prep_upred:                             0
% 3.23/0.99  prep_unflattend:                        603
% 3.23/0.99  smt_new_axioms:                         0
% 3.23/0.99  pred_elim_cands:                        5
% 3.23/0.99  pred_elim:                              2
% 3.23/0.99  pred_elim_cl:                           2
% 3.23/0.99  pred_elim_cycles:                       6
% 3.23/0.99  merged_defs:                            8
% 3.23/0.99  merged_defs_ncl:                        0
% 3.23/0.99  bin_hyper_res:                          9
% 3.23/0.99  prep_cycles:                            4
% 3.23/0.99  pred_elim_time:                         0.023
% 3.23/0.99  splitting_time:                         0.
% 3.23/0.99  sem_filter_time:                        0.
% 3.23/0.99  monotx_time:                            0.001
% 3.23/0.99  subtype_inf_time:                       0.
% 3.23/0.99  
% 3.23/0.99  ------ Problem properties
% 3.23/0.99  
% 3.23/0.99  clauses:                                39
% 3.23/0.99  conjectures:                            2
% 3.23/0.99  epr:                                    19
% 3.23/0.99  horn:                                   30
% 3.23/0.99  ground:                                 5
% 3.23/0.99  unary:                                  15
% 3.23/0.99  binary:                                 7
% 3.23/0.99  lits:                                   91
% 3.23/0.99  lits_eq:                                26
% 3.23/0.99  fd_pure:                                0
% 3.23/0.99  fd_pseudo:                              0
% 3.23/0.99  fd_cond:                                0
% 3.23/0.99  fd_pseudo_cond:                         10
% 3.23/0.99  ac_symbols:                             0
% 3.23/0.99  
% 3.23/0.99  ------ Propositional Solver
% 3.23/0.99  
% 3.23/0.99  prop_solver_calls:                      25
% 3.23/0.99  prop_fast_solver_calls:                 1151
% 3.23/0.99  smt_solver_calls:                       0
% 3.23/0.99  smt_fast_solver_calls:                  0
% 3.23/0.99  prop_num_of_clauses:                    1228
% 3.23/0.99  prop_preprocess_simplified:             7505
% 3.23/0.99  prop_fo_subsumed:                       9
% 3.23/0.99  prop_solver_time:                       0.
% 3.23/0.99  smt_solver_time:                        0.
% 3.23/0.99  smt_fast_solver_time:                   0.
% 3.23/0.99  prop_fast_solver_time:                  0.
% 3.23/0.99  prop_unsat_core_time:                   0.
% 3.23/0.99  
% 3.23/0.99  ------ QBF
% 3.23/0.99  
% 3.23/0.99  qbf_q_res:                              0
% 3.23/0.99  qbf_num_tautologies:                    0
% 3.23/0.99  qbf_prep_cycles:                        0
% 3.23/0.99  
% 3.23/0.99  ------ BMC1
% 3.23/0.99  
% 3.23/0.99  bmc1_current_bound:                     -1
% 3.23/0.99  bmc1_last_solved_bound:                 -1
% 3.23/0.99  bmc1_unsat_core_size:                   -1
% 3.23/0.99  bmc1_unsat_core_parents_size:           -1
% 3.23/0.99  bmc1_merge_next_fun:                    0
% 3.23/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.23/0.99  
% 3.23/0.99  ------ Instantiation
% 3.23/0.99  
% 3.23/0.99  inst_num_of_clauses:                    369
% 3.23/0.99  inst_num_in_passive:                    66
% 3.23/0.99  inst_num_in_active:                     156
% 3.23/0.99  inst_num_in_unprocessed:                147
% 3.23/0.99  inst_num_of_loops:                      170
% 3.23/0.99  inst_num_of_learning_restarts:          0
% 3.23/0.99  inst_num_moves_active_passive:          13
% 3.23/0.99  inst_lit_activity:                      0
% 3.23/0.99  inst_lit_activity_moves:                0
% 3.23/0.99  inst_num_tautologies:                   0
% 3.23/0.99  inst_num_prop_implied:                  0
% 3.23/0.99  inst_num_existing_simplified:           0
% 3.23/0.99  inst_num_eq_res_simplified:             0
% 3.23/0.99  inst_num_child_elim:                    0
% 3.23/0.99  inst_num_of_dismatching_blockings:      99
% 3.23/0.99  inst_num_of_non_proper_insts:           313
% 3.23/0.99  inst_num_of_duplicates:                 0
% 3.23/0.99  inst_inst_num_from_inst_to_res:         0
% 3.23/0.99  inst_dismatching_checking_time:         0.
% 3.23/0.99  
% 3.23/0.99  ------ Resolution
% 3.23/0.99  
% 3.23/0.99  res_num_of_clauses:                     0
% 3.23/0.99  res_num_in_passive:                     0
% 3.23/0.99  res_num_in_active:                      0
% 3.23/0.99  res_num_of_loops:                       181
% 3.23/0.99  res_forward_subset_subsumed:            32
% 3.23/0.99  res_backward_subset_subsumed:           0
% 3.23/0.99  res_forward_subsumed:                   0
% 3.23/0.99  res_backward_subsumed:                  0
% 3.23/0.99  res_forward_subsumption_resolution:     0
% 3.23/0.99  res_backward_subsumption_resolution:    0
% 3.23/0.99  res_clause_to_clause_subsumption:       952
% 3.23/0.99  res_orphan_elimination:                 0
% 3.23/0.99  res_tautology_del:                      50
% 3.23/0.99  res_num_eq_res_simplified:              0
% 3.23/0.99  res_num_sel_changes:                    0
% 3.23/0.99  res_moves_from_active_to_pass:          0
% 3.23/0.99  
% 3.23/0.99  ------ Superposition
% 3.23/0.99  
% 3.23/0.99  sup_time_total:                         0.
% 3.23/0.99  sup_time_generating:                    0.
% 3.23/0.99  sup_time_sim_full:                      0.
% 3.23/0.99  sup_time_sim_immed:                     0.
% 3.23/0.99  
% 3.23/0.99  sup_num_of_clauses:                     63
% 3.23/0.99  sup_num_in_active:                      33
% 3.23/0.99  sup_num_in_passive:                     30
% 3.23/0.99  sup_num_of_loops:                       33
% 3.23/0.99  sup_fw_superposition:                   23
% 3.23/0.99  sup_bw_superposition:                   8
% 3.23/0.99  sup_immediate_simplified:               0
% 3.23/0.99  sup_given_eliminated:                   0
% 3.23/0.99  comparisons_done:                       0
% 3.23/0.99  comparisons_avoided:                    0
% 3.23/0.99  
% 3.23/0.99  ------ Simplifications
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  sim_fw_subset_subsumed:                 0
% 3.23/0.99  sim_bw_subset_subsumed:                 2
% 3.23/0.99  sim_fw_subsumed:                        0
% 3.23/0.99  sim_bw_subsumed:                        0
% 3.23/0.99  sim_fw_subsumption_res:                 0
% 3.23/0.99  sim_bw_subsumption_res:                 0
% 3.23/0.99  sim_tautology_del:                      1
% 3.23/0.99  sim_eq_tautology_del:                   2
% 3.23/0.99  sim_eq_res_simp:                        0
% 3.23/0.99  sim_fw_demodulated:                     0
% 3.23/0.99  sim_bw_demodulated:                     0
% 3.23/0.99  sim_light_normalised:                   0
% 3.23/0.99  sim_joinable_taut:                      0
% 3.23/0.99  sim_joinable_simp:                      0
% 3.23/0.99  sim_ac_normalised:                      0
% 3.23/0.99  sim_smt_subsumption:                    0
% 3.23/0.99  
%------------------------------------------------------------------------------
