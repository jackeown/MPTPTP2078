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
% DateTime   : Thu Dec  3 11:53:52 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  182 (3279 expanded)
%              Number of clauses        :   82 ( 455 expanded)
%              Number of leaves         :   26 ( 909 expanded)
%              Depth                    :   23
%              Number of atoms          :  652 (10567 expanded)
%              Number of equality atoms :  309 (4662 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f108])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f77,f109])).

fof(f111,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f110])).

fof(f112,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f75,f111])).

fof(f113,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f81,f112])).

fof(f120,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f113])).

fof(f129,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f120])).

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

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f59,plain,(
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

fof(f58,plain,
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

fof(f60,plain,
    ( ( ~ r1_ordinal1(sK5,sK6)
      | ~ r2_hidden(sK5,k1_ordinal1(sK6)) )
    & ( r1_ordinal1(sK5,sK6)
      | r2_hidden(sK5,k1_ordinal1(sK6)) )
    & v3_ordinal1(sK6)
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f57,f59,f58])).

fof(f107,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f114,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f112])).

fof(f115,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f99,f113,f114])).

fof(f126,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f107,f115])).

fof(f104,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f105,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f60])).

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

fof(f24,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f97,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
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
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f106,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f60])).

fof(f127,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f106,f115])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f121,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f113])).

fof(f130,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f121])).

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

fof(f51,plain,(
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
    inference(flattening,[],[f51])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f143,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f87])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f125,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f70,f114])).

fof(f135,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f125])).

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

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f71,f114])).

fof(f133,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f124])).

fof(f134,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f133])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f113])).

fof(f128,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f119])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2655,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_32,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2653,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4824,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2655,c_2653])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2678,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_34,negated_conjecture,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2651,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4028,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top
    | r2_hidden(sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2678,c_2651])).

cnf(c_8383,plain,
    ( r1_tarski(sK6,sK5) = iProver_top
    | r2_hidden(sK5,sK6) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4824,c_4028])).

cnf(c_37,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_38,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_39,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_28,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_30,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_475,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_476,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_3950,plain,
    ( r1_tarski(X0,sK5)
    | ~ r2_hidden(X0,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_3951,plain,
    ( r1_tarski(X0,sK5) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3950])).

cnf(c_3953,plain,
    ( r1_tarski(sK6,sK5) = iProver_top
    | r2_hidden(sK6,sK5) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3951])).

cnf(c_33,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2652,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4383,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK5,sK6) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2652,c_4028])).

cnf(c_4607,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK5,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4383,c_38,c_39])).

cnf(c_4823,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2652,c_2653])).

cnf(c_35,negated_conjecture,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2650,plain,
    ( r1_ordinal1(sK5,sK6) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2677,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5346,plain,
    ( r1_ordinal1(sK5,sK6) = iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2650,c_2677])).

cnf(c_40,plain,
    ( r1_ordinal1(sK5,sK6) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_54,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_56,plain,
    ( r1_ordinal1(sK6,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_25,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X1 = X0
    | X3 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_67,plain,
    ( ~ sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_24,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_70,plain,
    ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3226,plain,
    ( r2_hidden(sK5,X0)
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3232,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3226])).

cnf(c_3234,plain,
    ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3232])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f135])).

cnf(c_3279,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3280,plain,
    ( sK5 = X0
    | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3279])).

cnf(c_3282,plain,
    ( sK5 = sK6
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3280])).

cnf(c_1867,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5615,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(sK5,sK6)
    | sK6 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1867])).

cnf(c_5616,plain,
    ( sK6 != X0
    | sK5 != X1
    | r1_ordinal1(X1,X0) != iProver_top
    | r1_ordinal1(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5615])).

cnf(c_5618,plain,
    ( sK6 != sK6
    | sK5 != sK6
    | r1_ordinal1(sK6,sK6) != iProver_top
    | r1_ordinal1(sK5,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5616])).

cnf(c_5668,plain,
    ( r1_ordinal1(sK5,sK6) = iProver_top
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5346,c_39,c_40,c_56,c_67,c_70,c_3234,c_3282,c_5618])).

cnf(c_5674,plain,
    ( r1_tarski(sK5,sK6) = iProver_top
    | r2_hidden(sK5,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5668,c_2653])).

cnf(c_5744,plain,
    ( r1_tarski(sK5,sK6) = iProver_top
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5674,c_38,c_39])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2676,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5751,plain,
    ( sK6 = sK5
    | r1_tarski(sK6,sK5) != iProver_top
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5744,c_2676])).

cnf(c_11,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_92,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_94,plain,
    ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_1861,plain,
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

cnf(c_1868,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1861])).

cnf(c_1863,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2938,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | X0 != X2
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_3227,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2938])).

cnf(c_3228,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | sK5 != X0
    | r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3227])).

cnf(c_3230,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK5 != sK6
    | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3228])).

cnf(c_3278,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3284,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3278])).

cnf(c_3286,plain,
    ( sK5 = sK6
    | r1_tarski(sK6,sK5) != iProver_top
    | r1_tarski(sK5,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3284])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_2679,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4150,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2679,c_2651])).

cnf(c_5760,plain,
    ( r1_tarski(sK6,sK5) != iProver_top
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5751,c_38,c_39,c_67,c_70,c_94,c_1868,c_3230,c_3286,c_4150,c_5668,c_5674])).

cnf(c_8144,plain,
    ( r2_hidden(sK5,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4823,c_5760])).

cnf(c_8768,plain,
    ( r1_tarski(sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8383,c_38,c_39,c_3953,c_4607,c_8144])).

cnf(c_8776,plain,
    ( r2_hidden(sK5,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_8768,c_5760])).

cnf(c_2647,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_9067,plain,
    ( r1_tarski(sK5,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8776,c_2647])).

cnf(c_31,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_5607,plain,
    ( r1_ordinal1(sK5,sK6)
    | ~ r1_tarski(sK5,sK6)
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_5611,plain,
    ( r1_ordinal1(sK5,sK6) = iProver_top
    | r1_tarski(sK5,sK6) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5607])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9067,c_8144,c_5611,c_4028,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.98/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/1.00  
% 2.98/1.00  ------  iProver source info
% 2.98/1.00  
% 2.98/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.98/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/1.00  git: non_committed_changes: false
% 2.98/1.00  git: last_make_outside_of_git: false
% 2.98/1.00  
% 2.98/1.00  ------ 
% 2.98/1.00  
% 2.98/1.00  ------ Input Options
% 2.98/1.00  
% 2.98/1.00  --out_options                           all
% 2.98/1.00  --tptp_safe_out                         true
% 2.98/1.00  --problem_path                          ""
% 2.98/1.00  --include_path                          ""
% 2.98/1.00  --clausifier                            res/vclausify_rel
% 2.98/1.00  --clausifier_options                    --mode clausify
% 2.98/1.00  --stdin                                 false
% 2.98/1.00  --stats_out                             all
% 2.98/1.00  
% 2.98/1.00  ------ General Options
% 2.98/1.00  
% 2.98/1.00  --fof                                   false
% 2.98/1.00  --time_out_real                         305.
% 2.98/1.00  --time_out_virtual                      -1.
% 2.98/1.00  --symbol_type_check                     false
% 2.98/1.00  --clausify_out                          false
% 2.98/1.00  --sig_cnt_out                           false
% 2.98/1.00  --trig_cnt_out                          false
% 2.98/1.00  --trig_cnt_out_tolerance                1.
% 2.98/1.00  --trig_cnt_out_sk_spl                   false
% 2.98/1.00  --abstr_cl_out                          false
% 2.98/1.00  
% 2.98/1.00  ------ Global Options
% 2.98/1.00  
% 2.98/1.00  --schedule                              default
% 2.98/1.00  --add_important_lit                     false
% 2.98/1.00  --prop_solver_per_cl                    1000
% 2.98/1.00  --min_unsat_core                        false
% 2.98/1.00  --soft_assumptions                      false
% 2.98/1.00  --soft_lemma_size                       3
% 2.98/1.00  --prop_impl_unit_size                   0
% 2.98/1.00  --prop_impl_unit                        []
% 2.98/1.00  --share_sel_clauses                     true
% 2.98/1.00  --reset_solvers                         false
% 2.98/1.00  --bc_imp_inh                            [conj_cone]
% 2.98/1.00  --conj_cone_tolerance                   3.
% 2.98/1.00  --extra_neg_conj                        none
% 2.98/1.00  --large_theory_mode                     true
% 2.98/1.00  --prolific_symb_bound                   200
% 2.98/1.00  --lt_threshold                          2000
% 2.98/1.00  --clause_weak_htbl                      true
% 2.98/1.00  --gc_record_bc_elim                     false
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing Options
% 2.98/1.00  
% 2.98/1.00  --preprocessing_flag                    true
% 2.98/1.00  --time_out_prep_mult                    0.1
% 2.98/1.00  --splitting_mode                        input
% 2.98/1.00  --splitting_grd                         true
% 2.98/1.00  --splitting_cvd                         false
% 2.98/1.00  --splitting_cvd_svl                     false
% 2.98/1.00  --splitting_nvd                         32
% 2.98/1.00  --sub_typing                            true
% 2.98/1.00  --prep_gs_sim                           true
% 2.98/1.00  --prep_unflatten                        true
% 2.98/1.00  --prep_res_sim                          true
% 2.98/1.00  --prep_upred                            true
% 2.98/1.00  --prep_sem_filter                       exhaustive
% 2.98/1.00  --prep_sem_filter_out                   false
% 2.98/1.00  --pred_elim                             true
% 2.98/1.00  --res_sim_input                         true
% 2.98/1.00  --eq_ax_congr_red                       true
% 2.98/1.00  --pure_diseq_elim                       true
% 2.98/1.00  --brand_transform                       false
% 2.98/1.00  --non_eq_to_eq                          false
% 2.98/1.00  --prep_def_merge                        true
% 2.98/1.00  --prep_def_merge_prop_impl              false
% 2.98/1.00  --prep_def_merge_mbd                    true
% 2.98/1.00  --prep_def_merge_tr_red                 false
% 2.98/1.00  --prep_def_merge_tr_cl                  false
% 2.98/1.00  --smt_preprocessing                     true
% 2.98/1.00  --smt_ac_axioms                         fast
% 2.98/1.00  --preprocessed_out                      false
% 2.98/1.00  --preprocessed_stats                    false
% 2.98/1.00  
% 2.98/1.00  ------ Abstraction refinement Options
% 2.98/1.00  
% 2.98/1.00  --abstr_ref                             []
% 2.98/1.00  --abstr_ref_prep                        false
% 2.98/1.00  --abstr_ref_until_sat                   false
% 2.98/1.00  --abstr_ref_sig_restrict                funpre
% 2.98/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/1.00  --abstr_ref_under                       []
% 2.98/1.00  
% 2.98/1.00  ------ SAT Options
% 2.98/1.00  
% 2.98/1.00  --sat_mode                              false
% 2.98/1.00  --sat_fm_restart_options                ""
% 2.98/1.00  --sat_gr_def                            false
% 2.98/1.00  --sat_epr_types                         true
% 2.98/1.00  --sat_non_cyclic_types                  false
% 2.98/1.00  --sat_finite_models                     false
% 2.98/1.00  --sat_fm_lemmas                         false
% 2.98/1.00  --sat_fm_prep                           false
% 2.98/1.00  --sat_fm_uc_incr                        true
% 2.98/1.00  --sat_out_model                         small
% 2.98/1.00  --sat_out_clauses                       false
% 2.98/1.00  
% 2.98/1.00  ------ QBF Options
% 2.98/1.00  
% 2.98/1.00  --qbf_mode                              false
% 2.98/1.00  --qbf_elim_univ                         false
% 2.98/1.00  --qbf_dom_inst                          none
% 2.98/1.00  --qbf_dom_pre_inst                      false
% 2.98/1.00  --qbf_sk_in                             false
% 2.98/1.00  --qbf_pred_elim                         true
% 2.98/1.00  --qbf_split                             512
% 2.98/1.00  
% 2.98/1.00  ------ BMC1 Options
% 2.98/1.00  
% 2.98/1.00  --bmc1_incremental                      false
% 2.98/1.00  --bmc1_axioms                           reachable_all
% 2.98/1.00  --bmc1_min_bound                        0
% 2.98/1.00  --bmc1_max_bound                        -1
% 2.98/1.00  --bmc1_max_bound_default                -1
% 2.98/1.00  --bmc1_symbol_reachability              true
% 2.98/1.00  --bmc1_property_lemmas                  false
% 2.98/1.00  --bmc1_k_induction                      false
% 2.98/1.00  --bmc1_non_equiv_states                 false
% 2.98/1.00  --bmc1_deadlock                         false
% 2.98/1.00  --bmc1_ucm                              false
% 2.98/1.00  --bmc1_add_unsat_core                   none
% 2.98/1.00  --bmc1_unsat_core_children              false
% 2.98/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/1.00  --bmc1_out_stat                         full
% 2.98/1.00  --bmc1_ground_init                      false
% 2.98/1.00  --bmc1_pre_inst_next_state              false
% 2.98/1.00  --bmc1_pre_inst_state                   false
% 2.98/1.00  --bmc1_pre_inst_reach_state             false
% 2.98/1.00  --bmc1_out_unsat_core                   false
% 2.98/1.00  --bmc1_aig_witness_out                  false
% 2.98/1.00  --bmc1_verbose                          false
% 2.98/1.00  --bmc1_dump_clauses_tptp                false
% 2.98/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.98/1.00  --bmc1_dump_file                        -
% 2.98/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.98/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.98/1.00  --bmc1_ucm_extend_mode                  1
% 2.98/1.00  --bmc1_ucm_init_mode                    2
% 2.98/1.00  --bmc1_ucm_cone_mode                    none
% 2.98/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.98/1.00  --bmc1_ucm_relax_model                  4
% 2.98/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.98/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/1.00  --bmc1_ucm_layered_model                none
% 2.98/1.00  --bmc1_ucm_max_lemma_size               10
% 2.98/1.00  
% 2.98/1.00  ------ AIG Options
% 2.98/1.00  
% 2.98/1.00  --aig_mode                              false
% 2.98/1.00  
% 2.98/1.00  ------ Instantiation Options
% 2.98/1.00  
% 2.98/1.00  --instantiation_flag                    true
% 2.98/1.00  --inst_sos_flag                         false
% 2.98/1.00  --inst_sos_phase                        true
% 2.98/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/1.00  --inst_lit_sel_side                     num_symb
% 2.98/1.00  --inst_solver_per_active                1400
% 2.98/1.00  --inst_solver_calls_frac                1.
% 2.98/1.00  --inst_passive_queue_type               priority_queues
% 2.98/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/1.00  --inst_passive_queues_freq              [25;2]
% 2.98/1.00  --inst_dismatching                      true
% 2.98/1.00  --inst_eager_unprocessed_to_passive     true
% 2.98/1.00  --inst_prop_sim_given                   true
% 2.98/1.00  --inst_prop_sim_new                     false
% 2.98/1.00  --inst_subs_new                         false
% 2.98/1.00  --inst_eq_res_simp                      false
% 2.98/1.00  --inst_subs_given                       false
% 2.98/1.00  --inst_orphan_elimination               true
% 2.98/1.00  --inst_learning_loop_flag               true
% 2.98/1.00  --inst_learning_start                   3000
% 2.98/1.00  --inst_learning_factor                  2
% 2.98/1.00  --inst_start_prop_sim_after_learn       3
% 2.98/1.00  --inst_sel_renew                        solver
% 2.98/1.00  --inst_lit_activity_flag                true
% 2.98/1.00  --inst_restr_to_given                   false
% 2.98/1.00  --inst_activity_threshold               500
% 2.98/1.00  --inst_out_proof                        true
% 2.98/1.00  
% 2.98/1.00  ------ Resolution Options
% 2.98/1.00  
% 2.98/1.00  --resolution_flag                       true
% 2.98/1.00  --res_lit_sel                           adaptive
% 2.98/1.00  --res_lit_sel_side                      none
% 2.98/1.00  --res_ordering                          kbo
% 2.98/1.00  --res_to_prop_solver                    active
% 2.98/1.00  --res_prop_simpl_new                    false
% 2.98/1.00  --res_prop_simpl_given                  true
% 2.98/1.00  --res_passive_queue_type                priority_queues
% 2.98/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/1.00  --res_passive_queues_freq               [15;5]
% 2.98/1.00  --res_forward_subs                      full
% 2.98/1.00  --res_backward_subs                     full
% 2.98/1.00  --res_forward_subs_resolution           true
% 2.98/1.00  --res_backward_subs_resolution          true
% 2.98/1.00  --res_orphan_elimination                true
% 2.98/1.00  --res_time_limit                        2.
% 2.98/1.00  --res_out_proof                         true
% 2.98/1.00  
% 2.98/1.00  ------ Superposition Options
% 2.98/1.00  
% 2.98/1.00  --superposition_flag                    true
% 2.98/1.00  --sup_passive_queue_type                priority_queues
% 2.98/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.98/1.00  --demod_completeness_check              fast
% 2.98/1.00  --demod_use_ground                      true
% 2.98/1.00  --sup_to_prop_solver                    passive
% 2.98/1.00  --sup_prop_simpl_new                    true
% 2.98/1.00  --sup_prop_simpl_given                  true
% 2.98/1.00  --sup_fun_splitting                     false
% 2.98/1.00  --sup_smt_interval                      50000
% 2.98/1.00  
% 2.98/1.00  ------ Superposition Simplification Setup
% 2.98/1.00  
% 2.98/1.00  --sup_indices_passive                   []
% 2.98/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.00  --sup_full_bw                           [BwDemod]
% 2.98/1.00  --sup_immed_triv                        [TrivRules]
% 2.98/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.00  --sup_immed_bw_main                     []
% 2.98/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.00  
% 2.98/1.00  ------ Combination Options
% 2.98/1.00  
% 2.98/1.00  --comb_res_mult                         3
% 2.98/1.00  --comb_sup_mult                         2
% 2.98/1.00  --comb_inst_mult                        10
% 2.98/1.00  
% 2.98/1.00  ------ Debug Options
% 2.98/1.00  
% 2.98/1.00  --dbg_backtrace                         false
% 2.98/1.00  --dbg_dump_prop_clauses                 false
% 2.98/1.00  --dbg_dump_prop_clauses_file            -
% 2.98/1.00  --dbg_out_stat                          false
% 2.98/1.00  ------ Parsing...
% 2.98/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/1.00  ------ Proving...
% 2.98/1.00  ------ Problem Properties 
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  clauses                                 36
% 2.98/1.00  conjectures                             4
% 2.98/1.00  EPR                                     20
% 2.98/1.00  Horn                                    28
% 2.98/1.00  unary                                   13
% 2.98/1.00  binary                                  6
% 2.98/1.00  lits                                    87
% 2.98/1.00  lits eq                                 18
% 2.98/1.00  fd_pure                                 0
% 2.98/1.00  fd_pseudo                               0
% 2.98/1.00  fd_cond                                 0
% 2.98/1.00  fd_pseudo_cond                          8
% 2.98/1.00  AC symbols                              0
% 2.98/1.00  
% 2.98/1.00  ------ Schedule dynamic 5 is on 
% 2.98/1.00  
% 2.98/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  ------ 
% 2.98/1.00  Current options:
% 2.98/1.00  ------ 
% 2.98/1.00  
% 2.98/1.00  ------ Input Options
% 2.98/1.00  
% 2.98/1.00  --out_options                           all
% 2.98/1.00  --tptp_safe_out                         true
% 2.98/1.00  --problem_path                          ""
% 2.98/1.00  --include_path                          ""
% 2.98/1.00  --clausifier                            res/vclausify_rel
% 2.98/1.00  --clausifier_options                    --mode clausify
% 2.98/1.00  --stdin                                 false
% 2.98/1.00  --stats_out                             all
% 2.98/1.00  
% 2.98/1.00  ------ General Options
% 2.98/1.00  
% 2.98/1.00  --fof                                   false
% 2.98/1.00  --time_out_real                         305.
% 2.98/1.00  --time_out_virtual                      -1.
% 2.98/1.00  --symbol_type_check                     false
% 2.98/1.00  --clausify_out                          false
% 2.98/1.00  --sig_cnt_out                           false
% 2.98/1.00  --trig_cnt_out                          false
% 2.98/1.00  --trig_cnt_out_tolerance                1.
% 2.98/1.00  --trig_cnt_out_sk_spl                   false
% 2.98/1.00  --abstr_cl_out                          false
% 2.98/1.00  
% 2.98/1.00  ------ Global Options
% 2.98/1.00  
% 2.98/1.00  --schedule                              default
% 2.98/1.00  --add_important_lit                     false
% 2.98/1.00  --prop_solver_per_cl                    1000
% 2.98/1.00  --min_unsat_core                        false
% 2.98/1.00  --soft_assumptions                      false
% 2.98/1.00  --soft_lemma_size                       3
% 2.98/1.00  --prop_impl_unit_size                   0
% 2.98/1.00  --prop_impl_unit                        []
% 2.98/1.00  --share_sel_clauses                     true
% 2.98/1.00  --reset_solvers                         false
% 2.98/1.00  --bc_imp_inh                            [conj_cone]
% 2.98/1.00  --conj_cone_tolerance                   3.
% 2.98/1.00  --extra_neg_conj                        none
% 2.98/1.00  --large_theory_mode                     true
% 2.98/1.00  --prolific_symb_bound                   200
% 2.98/1.00  --lt_threshold                          2000
% 2.98/1.00  --clause_weak_htbl                      true
% 2.98/1.00  --gc_record_bc_elim                     false
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing Options
% 2.98/1.00  
% 2.98/1.00  --preprocessing_flag                    true
% 2.98/1.00  --time_out_prep_mult                    0.1
% 2.98/1.00  --splitting_mode                        input
% 2.98/1.00  --splitting_grd                         true
% 2.98/1.00  --splitting_cvd                         false
% 2.98/1.00  --splitting_cvd_svl                     false
% 2.98/1.00  --splitting_nvd                         32
% 2.98/1.00  --sub_typing                            true
% 2.98/1.00  --prep_gs_sim                           true
% 2.98/1.00  --prep_unflatten                        true
% 2.98/1.00  --prep_res_sim                          true
% 2.98/1.00  --prep_upred                            true
% 2.98/1.00  --prep_sem_filter                       exhaustive
% 2.98/1.00  --prep_sem_filter_out                   false
% 2.98/1.00  --pred_elim                             true
% 2.98/1.00  --res_sim_input                         true
% 2.98/1.00  --eq_ax_congr_red                       true
% 2.98/1.00  --pure_diseq_elim                       true
% 2.98/1.00  --brand_transform                       false
% 2.98/1.00  --non_eq_to_eq                          false
% 2.98/1.00  --prep_def_merge                        true
% 2.98/1.00  --prep_def_merge_prop_impl              false
% 2.98/1.00  --prep_def_merge_mbd                    true
% 2.98/1.00  --prep_def_merge_tr_red                 false
% 2.98/1.00  --prep_def_merge_tr_cl                  false
% 2.98/1.00  --smt_preprocessing                     true
% 2.98/1.00  --smt_ac_axioms                         fast
% 2.98/1.00  --preprocessed_out                      false
% 2.98/1.00  --preprocessed_stats                    false
% 2.98/1.00  
% 2.98/1.00  ------ Abstraction refinement Options
% 2.98/1.00  
% 2.98/1.00  --abstr_ref                             []
% 2.98/1.00  --abstr_ref_prep                        false
% 2.98/1.00  --abstr_ref_until_sat                   false
% 2.98/1.00  --abstr_ref_sig_restrict                funpre
% 2.98/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/1.00  --abstr_ref_under                       []
% 2.98/1.00  
% 2.98/1.00  ------ SAT Options
% 2.98/1.00  
% 2.98/1.00  --sat_mode                              false
% 2.98/1.00  --sat_fm_restart_options                ""
% 2.98/1.00  --sat_gr_def                            false
% 2.98/1.00  --sat_epr_types                         true
% 2.98/1.00  --sat_non_cyclic_types                  false
% 2.98/1.00  --sat_finite_models                     false
% 2.98/1.00  --sat_fm_lemmas                         false
% 2.98/1.00  --sat_fm_prep                           false
% 2.98/1.00  --sat_fm_uc_incr                        true
% 2.98/1.00  --sat_out_model                         small
% 2.98/1.00  --sat_out_clauses                       false
% 2.98/1.00  
% 2.98/1.00  ------ QBF Options
% 2.98/1.00  
% 2.98/1.00  --qbf_mode                              false
% 2.98/1.00  --qbf_elim_univ                         false
% 2.98/1.00  --qbf_dom_inst                          none
% 2.98/1.00  --qbf_dom_pre_inst                      false
% 2.98/1.00  --qbf_sk_in                             false
% 2.98/1.00  --qbf_pred_elim                         true
% 2.98/1.00  --qbf_split                             512
% 2.98/1.00  
% 2.98/1.00  ------ BMC1 Options
% 2.98/1.00  
% 2.98/1.00  --bmc1_incremental                      false
% 2.98/1.00  --bmc1_axioms                           reachable_all
% 2.98/1.00  --bmc1_min_bound                        0
% 2.98/1.00  --bmc1_max_bound                        -1
% 2.98/1.00  --bmc1_max_bound_default                -1
% 2.98/1.00  --bmc1_symbol_reachability              true
% 2.98/1.00  --bmc1_property_lemmas                  false
% 2.98/1.00  --bmc1_k_induction                      false
% 2.98/1.00  --bmc1_non_equiv_states                 false
% 2.98/1.00  --bmc1_deadlock                         false
% 2.98/1.00  --bmc1_ucm                              false
% 2.98/1.00  --bmc1_add_unsat_core                   none
% 2.98/1.00  --bmc1_unsat_core_children              false
% 2.98/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/1.00  --bmc1_out_stat                         full
% 2.98/1.00  --bmc1_ground_init                      false
% 2.98/1.00  --bmc1_pre_inst_next_state              false
% 2.98/1.00  --bmc1_pre_inst_state                   false
% 2.98/1.00  --bmc1_pre_inst_reach_state             false
% 2.98/1.00  --bmc1_out_unsat_core                   false
% 2.98/1.00  --bmc1_aig_witness_out                  false
% 2.98/1.00  --bmc1_verbose                          false
% 2.98/1.00  --bmc1_dump_clauses_tptp                false
% 2.98/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.98/1.00  --bmc1_dump_file                        -
% 2.98/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.98/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.98/1.00  --bmc1_ucm_extend_mode                  1
% 2.98/1.00  --bmc1_ucm_init_mode                    2
% 2.98/1.00  --bmc1_ucm_cone_mode                    none
% 2.98/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.98/1.00  --bmc1_ucm_relax_model                  4
% 2.98/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.98/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/1.00  --bmc1_ucm_layered_model                none
% 2.98/1.00  --bmc1_ucm_max_lemma_size               10
% 2.98/1.00  
% 2.98/1.00  ------ AIG Options
% 2.98/1.00  
% 2.98/1.00  --aig_mode                              false
% 2.98/1.00  
% 2.98/1.00  ------ Instantiation Options
% 2.98/1.00  
% 2.98/1.00  --instantiation_flag                    true
% 2.98/1.00  --inst_sos_flag                         false
% 2.98/1.00  --inst_sos_phase                        true
% 2.98/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/1.00  --inst_lit_sel_side                     none
% 2.98/1.00  --inst_solver_per_active                1400
% 2.98/1.00  --inst_solver_calls_frac                1.
% 2.98/1.00  --inst_passive_queue_type               priority_queues
% 2.98/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/1.00  --inst_passive_queues_freq              [25;2]
% 2.98/1.00  --inst_dismatching                      true
% 2.98/1.00  --inst_eager_unprocessed_to_passive     true
% 2.98/1.00  --inst_prop_sim_given                   true
% 2.98/1.00  --inst_prop_sim_new                     false
% 2.98/1.00  --inst_subs_new                         false
% 2.98/1.00  --inst_eq_res_simp                      false
% 2.98/1.00  --inst_subs_given                       false
% 2.98/1.00  --inst_orphan_elimination               true
% 2.98/1.00  --inst_learning_loop_flag               true
% 2.98/1.00  --inst_learning_start                   3000
% 2.98/1.00  --inst_learning_factor                  2
% 2.98/1.00  --inst_start_prop_sim_after_learn       3
% 2.98/1.00  --inst_sel_renew                        solver
% 2.98/1.00  --inst_lit_activity_flag                true
% 2.98/1.00  --inst_restr_to_given                   false
% 2.98/1.00  --inst_activity_threshold               500
% 2.98/1.00  --inst_out_proof                        true
% 2.98/1.00  
% 2.98/1.00  ------ Resolution Options
% 2.98/1.00  
% 2.98/1.00  --resolution_flag                       false
% 2.98/1.00  --res_lit_sel                           adaptive
% 2.98/1.00  --res_lit_sel_side                      none
% 2.98/1.00  --res_ordering                          kbo
% 2.98/1.00  --res_to_prop_solver                    active
% 2.98/1.00  --res_prop_simpl_new                    false
% 2.98/1.00  --res_prop_simpl_given                  true
% 2.98/1.00  --res_passive_queue_type                priority_queues
% 2.98/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/1.00  --res_passive_queues_freq               [15;5]
% 2.98/1.00  --res_forward_subs                      full
% 2.98/1.00  --res_backward_subs                     full
% 2.98/1.00  --res_forward_subs_resolution           true
% 2.98/1.00  --res_backward_subs_resolution          true
% 2.98/1.00  --res_orphan_elimination                true
% 2.98/1.00  --res_time_limit                        2.
% 2.98/1.00  --res_out_proof                         true
% 2.98/1.00  
% 2.98/1.00  ------ Superposition Options
% 2.98/1.00  
% 2.98/1.00  --superposition_flag                    true
% 2.98/1.00  --sup_passive_queue_type                priority_queues
% 2.98/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.98/1.00  --demod_completeness_check              fast
% 2.98/1.00  --demod_use_ground                      true
% 2.98/1.00  --sup_to_prop_solver                    passive
% 2.98/1.00  --sup_prop_simpl_new                    true
% 2.98/1.00  --sup_prop_simpl_given                  true
% 2.98/1.00  --sup_fun_splitting                     false
% 2.98/1.00  --sup_smt_interval                      50000
% 2.98/1.00  
% 2.98/1.00  ------ Superposition Simplification Setup
% 2.98/1.00  
% 2.98/1.00  --sup_indices_passive                   []
% 2.98/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.00  --sup_full_bw                           [BwDemod]
% 2.98/1.00  --sup_immed_triv                        [TrivRules]
% 2.98/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.00  --sup_immed_bw_main                     []
% 2.98/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.00  
% 2.98/1.00  ------ Combination Options
% 2.98/1.00  
% 2.98/1.00  --comb_res_mult                         3
% 2.98/1.00  --comb_sup_mult                         2
% 2.98/1.00  --comb_inst_mult                        10
% 2.98/1.00  
% 2.98/1.00  ------ Debug Options
% 2.98/1.00  
% 2.98/1.00  --dbg_backtrace                         false
% 2.98/1.00  --dbg_dump_prop_clauses                 false
% 2.98/1.00  --dbg_dump_prop_clauses_file            -
% 2.98/1.00  --dbg_out_stat                          false
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  ------ Proving...
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  % SZS status Theorem for theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  fof(f14,axiom,(
% 2.98/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f25,plain,(
% 2.98/1.00    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.98/1.00    inference(ennf_transformation,[],[f14])).
% 2.98/1.00  
% 2.98/1.00  fof(f26,plain,(
% 2.98/1.00    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.98/1.00    inference(flattening,[],[f25])).
% 2.98/1.00  
% 2.98/1.00  fof(f98,plain,(
% 2.98/1.00    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f26])).
% 2.98/1.00  
% 2.98/1.00  fof(f17,axiom,(
% 2.98/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f28,plain,(
% 2.98/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.98/1.00    inference(ennf_transformation,[],[f17])).
% 2.98/1.00  
% 2.98/1.00  fof(f29,plain,(
% 2.98/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.98/1.01    inference(flattening,[],[f28])).
% 2.98/1.01  
% 2.98/1.01  fof(f55,plain,(
% 2.98/1.01    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.98/1.01    inference(nnf_transformation,[],[f29])).
% 2.98/1.01  
% 2.98/1.01  fof(f101,plain,(
% 2.98/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f55])).
% 2.98/1.01  
% 2.98/1.01  fof(f1,axiom,(
% 2.98/1.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f36,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(nnf_transformation,[],[f1])).
% 2.98/1.01  
% 2.98/1.01  fof(f37,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(flattening,[],[f36])).
% 2.98/1.01  
% 2.98/1.01  fof(f38,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(rectify,[],[f37])).
% 2.98/1.01  
% 2.98/1.01  fof(f39,plain,(
% 2.98/1.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f40,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 2.98/1.01  
% 2.98/1.01  fof(f62,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.98/1.01    inference(cnf_transformation,[],[f40])).
% 2.98/1.01  
% 2.98/1.01  fof(f11,axiom,(
% 2.98/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f81,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.98/1.01    inference(cnf_transformation,[],[f11])).
% 2.98/1.01  
% 2.98/1.01  fof(f5,axiom,(
% 2.98/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f75,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f5])).
% 2.98/1.01  
% 2.98/1.01  fof(f6,axiom,(
% 2.98/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f76,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f6])).
% 2.98/1.01  
% 2.98/1.01  fof(f7,axiom,(
% 2.98/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f77,plain,(
% 2.98/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f7])).
% 2.98/1.01  
% 2.98/1.01  fof(f8,axiom,(
% 2.98/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f78,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f8])).
% 2.98/1.01  
% 2.98/1.01  fof(f9,axiom,(
% 2.98/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f79,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f9])).
% 2.98/1.01  
% 2.98/1.01  fof(f10,axiom,(
% 2.98/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f80,plain,(
% 2.98/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f10])).
% 2.98/1.01  
% 2.98/1.01  fof(f108,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f79,f80])).
% 2.98/1.01  
% 2.98/1.01  fof(f109,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f78,f108])).
% 2.98/1.01  
% 2.98/1.01  fof(f110,plain,(
% 2.98/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f77,f109])).
% 2.98/1.01  
% 2.98/1.01  fof(f111,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f76,f110])).
% 2.98/1.01  
% 2.98/1.01  fof(f112,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f75,f111])).
% 2.98/1.01  
% 2.98/1.01  fof(f113,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.98/1.01    inference(definition_unfolding,[],[f81,f112])).
% 2.98/1.01  
% 2.98/1.01  fof(f120,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.98/1.01    inference(definition_unfolding,[],[f62,f113])).
% 2.98/1.01  
% 2.98/1.01  fof(f129,plain,(
% 2.98/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.98/1.01    inference(equality_resolution,[],[f120])).
% 2.98/1.01  
% 2.98/1.01  fof(f19,conjecture,(
% 2.98/1.01    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f20,negated_conjecture,(
% 2.98/1.01    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.98/1.01    inference(negated_conjecture,[],[f19])).
% 2.98/1.01  
% 2.98/1.01  fof(f32,plain,(
% 2.98/1.01    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f20])).
% 2.98/1.01  
% 2.98/1.01  fof(f56,plain,(
% 2.98/1.01    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.98/1.01    inference(nnf_transformation,[],[f32])).
% 2.98/1.01  
% 2.98/1.01  fof(f57,plain,(
% 2.98/1.01    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.98/1.01    inference(flattening,[],[f56])).
% 2.98/1.01  
% 2.98/1.01  fof(f59,plain,(
% 2.98/1.01    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK6) | ~r2_hidden(X0,k1_ordinal1(sK6))) & (r1_ordinal1(X0,sK6) | r2_hidden(X0,k1_ordinal1(sK6))) & v3_ordinal1(sK6))) )),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f58,plain,(
% 2.98/1.01    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK5,X1) | ~r2_hidden(sK5,k1_ordinal1(X1))) & (r1_ordinal1(sK5,X1) | r2_hidden(sK5,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK5))),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f60,plain,(
% 2.98/1.01    ((~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))) & (r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))) & v3_ordinal1(sK6)) & v3_ordinal1(sK5)),
% 2.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f57,f59,f58])).
% 2.98/1.01  
% 2.98/1.01  fof(f107,plain,(
% 2.98/1.01    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))),
% 2.98/1.01    inference(cnf_transformation,[],[f60])).
% 2.98/1.01  
% 2.98/1.01  fof(f15,axiom,(
% 2.98/1.01    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f99,plain,(
% 2.98/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f15])).
% 2.98/1.01  
% 2.98/1.01  fof(f4,axiom,(
% 2.98/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f74,plain,(
% 2.98/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f4])).
% 2.98/1.01  
% 2.98/1.01  fof(f114,plain,(
% 2.98/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f74,f112])).
% 2.98/1.01  
% 2.98/1.01  fof(f115,plain,(
% 2.98/1.01    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f99,f113,f114])).
% 2.98/1.01  
% 2.98/1.01  fof(f126,plain,(
% 2.98/1.01    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 2.98/1.01    inference(definition_unfolding,[],[f107,f115])).
% 2.98/1.01  
% 2.98/1.01  fof(f104,plain,(
% 2.98/1.01    v3_ordinal1(sK5)),
% 2.98/1.01    inference(cnf_transformation,[],[f60])).
% 2.98/1.01  
% 2.98/1.01  fof(f105,plain,(
% 2.98/1.01    v3_ordinal1(sK6)),
% 2.98/1.01    inference(cnf_transformation,[],[f60])).
% 2.98/1.01  
% 2.98/1.01  fof(f13,axiom,(
% 2.98/1.01    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f22,plain,(
% 2.98/1.01    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 2.98/1.01    inference(pure_predicate_removal,[],[f13])).
% 2.98/1.01  
% 2.98/1.01  fof(f24,plain,(
% 2.98/1.01    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f22])).
% 2.98/1.01  
% 2.98/1.01  fof(f97,plain,(
% 2.98/1.01    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f24])).
% 2.98/1.01  
% 2.98/1.01  fof(f16,axiom,(
% 2.98/1.01    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f21,plain,(
% 2.98/1.01    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 2.98/1.01    inference(unused_predicate_definition_removal,[],[f16])).
% 2.98/1.01  
% 2.98/1.01  fof(f27,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f21])).
% 2.98/1.01  
% 2.98/1.01  fof(f100,plain,(
% 2.98/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f27])).
% 2.98/1.01  
% 2.98/1.01  fof(f18,axiom,(
% 2.98/1.01    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f30,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f18])).
% 2.98/1.01  
% 2.98/1.01  fof(f31,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.98/1.01    inference(flattening,[],[f30])).
% 2.98/1.01  
% 2.98/1.01  fof(f103,plain,(
% 2.98/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f31])).
% 2.98/1.01  
% 2.98/1.01  fof(f106,plain,(
% 2.98/1.01    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))),
% 2.98/1.01    inference(cnf_transformation,[],[f60])).
% 2.98/1.01  
% 2.98/1.01  fof(f127,plain,(
% 2.98/1.01    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 2.98/1.01    inference(definition_unfolding,[],[f106,f115])).
% 2.98/1.01  
% 2.98/1.01  fof(f61,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.98/1.01    inference(cnf_transformation,[],[f40])).
% 2.98/1.01  
% 2.98/1.01  fof(f121,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.98/1.01    inference(definition_unfolding,[],[f61,f113])).
% 2.98/1.01  
% 2.98/1.01  fof(f130,plain,(
% 2.98/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.98/1.01    inference(equality_resolution,[],[f121])).
% 2.98/1.01  
% 2.98/1.01  fof(f33,plain,(
% 2.98/1.01    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 2.98/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.98/1.01  
% 2.98/1.01  fof(f51,plain,(
% 2.98/1.01    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.98/1.01    inference(nnf_transformation,[],[f33])).
% 2.98/1.01  
% 2.98/1.01  fof(f52,plain,(
% 2.98/1.01    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.98/1.01    inference(flattening,[],[f51])).
% 2.98/1.01  
% 2.98/1.01  fof(f53,plain,(
% 2.98/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.98/1.01    inference(rectify,[],[f52])).
% 2.98/1.01  
% 2.98/1.01  fof(f86,plain,(
% 2.98/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f53])).
% 2.98/1.01  
% 2.98/1.01  fof(f87,plain,(
% 2.98/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 2.98/1.01    inference(cnf_transformation,[],[f53])).
% 2.98/1.01  
% 2.98/1.01  fof(f143,plain,(
% 2.98/1.01    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.98/1.01    inference(equality_resolution,[],[f87])).
% 2.98/1.01  
% 2.98/1.01  fof(f3,axiom,(
% 2.98/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f43,plain,(
% 2.98/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.98/1.01    inference(nnf_transformation,[],[f3])).
% 2.98/1.01  
% 2.98/1.01  fof(f44,plain,(
% 2.98/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.98/1.01    inference(rectify,[],[f43])).
% 2.98/1.01  
% 2.98/1.01  fof(f45,plain,(
% 2.98/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f46,plain,(
% 2.98/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 2.98/1.01  
% 2.98/1.01  fof(f70,plain,(
% 2.98/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.98/1.01    inference(cnf_transformation,[],[f46])).
% 2.98/1.01  
% 2.98/1.01  fof(f125,plain,(
% 2.98/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.98/1.01    inference(definition_unfolding,[],[f70,f114])).
% 2.98/1.01  
% 2.98/1.01  fof(f135,plain,(
% 2.98/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 2.98/1.01    inference(equality_resolution,[],[f125])).
% 2.98/1.01  
% 2.98/1.01  fof(f2,axiom,(
% 2.98/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f41,plain,(
% 2.98/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.98/1.01    inference(nnf_transformation,[],[f2])).
% 2.98/1.01  
% 2.98/1.01  fof(f42,plain,(
% 2.98/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.98/1.01    inference(flattening,[],[f41])).
% 2.98/1.01  
% 2.98/1.01  fof(f69,plain,(
% 2.98/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f42])).
% 2.98/1.01  
% 2.98/1.01  fof(f71,plain,(
% 2.98/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.98/1.01    inference(cnf_transformation,[],[f46])).
% 2.98/1.01  
% 2.98/1.01  fof(f124,plain,(
% 2.98/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.98/1.01    inference(definition_unfolding,[],[f71,f114])).
% 2.98/1.01  
% 2.98/1.01  fof(f133,plain,(
% 2.98/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 2.98/1.01    inference(equality_resolution,[],[f124])).
% 2.98/1.01  
% 2.98/1.01  fof(f134,plain,(
% 2.98/1.01    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 2.98/1.01    inference(equality_resolution,[],[f133])).
% 2.98/1.01  
% 2.98/1.01  fof(f63,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.98/1.01    inference(cnf_transformation,[],[f40])).
% 2.98/1.01  
% 2.98/1.01  fof(f119,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.98/1.01    inference(definition_unfolding,[],[f63,f113])).
% 2.98/1.01  
% 2.98/1.01  fof(f128,plain,(
% 2.98/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.98/1.01    inference(equality_resolution,[],[f119])).
% 2.98/1.01  
% 2.98/1.01  fof(f102,plain,(
% 2.98/1.01    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f55])).
% 2.98/1.01  
% 2.98/1.01  cnf(c_29,plain,
% 2.98/1.01      ( r1_ordinal1(X0,X1)
% 2.98/1.01      | r1_ordinal1(X1,X0)
% 2.98/1.01      | ~ v3_ordinal1(X0)
% 2.98/1.01      | ~ v3_ordinal1(X1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f98]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2655,plain,
% 2.98/1.01      ( r1_ordinal1(X0,X1) = iProver_top
% 2.98/1.01      | r1_ordinal1(X1,X0) = iProver_top
% 2.98/1.01      | v3_ordinal1(X0) != iProver_top
% 2.98/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_32,plain,
% 2.98/1.01      ( ~ r1_ordinal1(X0,X1)
% 2.98/1.01      | r1_tarski(X0,X1)
% 2.98/1.01      | ~ v3_ordinal1(X0)
% 2.98/1.01      | ~ v3_ordinal1(X1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f101]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2653,plain,
% 2.98/1.01      ( r1_ordinal1(X0,X1) != iProver_top
% 2.98/1.01      | r1_tarski(X0,X1) = iProver_top
% 2.98/1.01      | v3_ordinal1(X0) != iProver_top
% 2.98/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_4824,plain,
% 2.98/1.01      ( r1_ordinal1(X0,X1) = iProver_top
% 2.98/1.01      | r1_tarski(X1,X0) = iProver_top
% 2.98/1.01      | v3_ordinal1(X0) != iProver_top
% 2.98/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_2655,c_2653]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_4,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,X1)
% 2.98/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 2.98/1.01      inference(cnf_transformation,[],[f129]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2678,plain,
% 2.98/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.98/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_34,negated_conjecture,
% 2.98/1.01      ( ~ r1_ordinal1(sK5,sK6)
% 2.98/1.01      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.98/1.01      inference(cnf_transformation,[],[f126]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2651,plain,
% 2.98/1.01      ( r1_ordinal1(sK5,sK6) != iProver_top
% 2.98/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_4028,plain,
% 2.98/1.01      ( r1_ordinal1(sK5,sK6) != iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_2678,c_2651]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_8383,plain,
% 2.98/1.01      ( r1_tarski(sK6,sK5) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) != iProver_top
% 2.98/1.01      | v3_ordinal1(sK6) != iProver_top
% 2.98/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_4824,c_4028]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_37,negated_conjecture,
% 2.98/1.01      ( v3_ordinal1(sK5) ),
% 2.98/1.01      inference(cnf_transformation,[],[f104]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_38,plain,
% 2.98/1.01      ( v3_ordinal1(sK5) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_36,negated_conjecture,
% 2.98/1.01      ( v3_ordinal1(sK6) ),
% 2.98/1.01      inference(cnf_transformation,[],[f105]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_39,plain,
% 2.98/1.01      ( v3_ordinal1(sK6) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_28,plain,
% 2.98/1.01      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f97]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_30,plain,
% 2.98/1.01      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f100]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_475,plain,
% 2.98/1.01      ( r1_tarski(X0,X1)
% 2.98/1.01      | ~ r2_hidden(X0,X1)
% 2.98/1.01      | ~ v3_ordinal1(X2)
% 2.98/1.01      | X1 != X2 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_476,plain,
% 2.98/1.01      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_475]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3950,plain,
% 2.98/1.01      ( r1_tarski(X0,sK5) | ~ r2_hidden(X0,sK5) | ~ v3_ordinal1(sK5) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_476]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3951,plain,
% 2.98/1.01      ( r1_tarski(X0,sK5) = iProver_top
% 2.98/1.01      | r2_hidden(X0,sK5) != iProver_top
% 2.98/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_3950]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3953,plain,
% 2.98/1.01      ( r1_tarski(sK6,sK5) = iProver_top
% 2.98/1.01      | r2_hidden(sK6,sK5) != iProver_top
% 2.98/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_3951]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_33,plain,
% 2.98/1.01      ( r1_ordinal1(X0,X1)
% 2.98/1.01      | r2_hidden(X1,X0)
% 2.98/1.01      | ~ v3_ordinal1(X0)
% 2.98/1.01      | ~ v3_ordinal1(X1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f103]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2652,plain,
% 2.98/1.01      ( r1_ordinal1(X0,X1) = iProver_top
% 2.98/1.01      | r2_hidden(X1,X0) = iProver_top
% 2.98/1.01      | v3_ordinal1(X0) != iProver_top
% 2.98/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_4383,plain,
% 2.98/1.01      ( r2_hidden(sK6,sK5) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) != iProver_top
% 2.98/1.01      | v3_ordinal1(sK6) != iProver_top
% 2.98/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_2652,c_4028]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_4607,plain,
% 2.98/1.01      ( r2_hidden(sK6,sK5) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) != iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_4383,c_38,c_39]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_4823,plain,
% 2.98/1.01      ( r1_tarski(X0,X1) = iProver_top
% 2.98/1.01      | r2_hidden(X1,X0) = iProver_top
% 2.98/1.01      | v3_ordinal1(X1) != iProver_top
% 2.98/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_2652,c_2653]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_35,negated_conjecture,
% 2.98/1.01      ( r1_ordinal1(sK5,sK6)
% 2.98/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.98/1.01      inference(cnf_transformation,[],[f127]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2650,plain,
% 2.98/1.01      ( r1_ordinal1(sK5,sK6) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5,plain,
% 2.98/1.01      ( r2_hidden(X0,X1)
% 2.98/1.01      | r2_hidden(X0,X2)
% 2.98/1.01      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.98/1.01      inference(cnf_transformation,[],[f130]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2677,plain,
% 2.98/1.01      ( r2_hidden(X0,X1) = iProver_top
% 2.98/1.01      | r2_hidden(X0,X2) = iProver_top
% 2.98/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5346,plain,
% 2.98/1.01      ( r1_ordinal1(sK5,sK6) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) = iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_2650,c_2677]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_40,plain,
% 2.98/1.01      ( r1_ordinal1(sK5,sK6) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_54,plain,
% 2.98/1.01      ( r1_ordinal1(X0,X1) = iProver_top
% 2.98/1.01      | r1_ordinal1(X1,X0) = iProver_top
% 2.98/1.01      | v3_ordinal1(X0) != iProver_top
% 2.98/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_56,plain,
% 2.98/1.01      ( r1_ordinal1(sK6,sK6) = iProver_top
% 2.98/1.01      | v3_ordinal1(sK6) != iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_54]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_25,plain,
% 2.98/1.01      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.98/1.01      | X1 = X0
% 2.98/1.01      | X3 = X0
% 2.98/1.01      | X8 = X0
% 2.98/1.01      | X7 = X0
% 2.98/1.01      | X6 = X0
% 2.98/1.01      | X5 = X0
% 2.98/1.01      | X4 = X0
% 2.98/1.01      | X2 = X0 ),
% 2.98/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_67,plain,
% 2.98/1.01      ( ~ sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) | sK6 = sK6 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_25]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_24,plain,
% 2.98/1.01      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f143]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_70,plain,
% 2.98/1.01      ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_24]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3226,plain,
% 2.98/1.01      ( r2_hidden(sK5,X0)
% 2.98/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.98/1.01      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3232,plain,
% 2.98/1.01      ( r2_hidden(sK5,X0) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_3226]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3234,plain,
% 2.98/1.01      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) = iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_3232]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_12,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 2.98/1.01      inference(cnf_transformation,[],[f135]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3279,plain,
% 2.98/1.01      ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 2.98/1.01      | sK5 = X0 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3280,plain,
% 2.98/1.01      ( sK5 = X0
% 2.98/1.01      | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_3279]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3282,plain,
% 2.98/1.01      ( sK5 = sK6
% 2.98/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_3280]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1867,plain,
% 2.98/1.01      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.98/1.01      theory(equality) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5615,plain,
% 2.98/1.01      ( ~ r1_ordinal1(X0,X1)
% 2.98/1.01      | r1_ordinal1(sK5,sK6)
% 2.98/1.01      | sK6 != X1
% 2.98/1.01      | sK5 != X0 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1867]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5616,plain,
% 2.98/1.01      ( sK6 != X0
% 2.98/1.01      | sK5 != X1
% 2.98/1.01      | r1_ordinal1(X1,X0) != iProver_top
% 2.98/1.01      | r1_ordinal1(sK5,sK6) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_5615]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5618,plain,
% 2.98/1.01      ( sK6 != sK6
% 2.98/1.01      | sK5 != sK6
% 2.98/1.01      | r1_ordinal1(sK6,sK6) != iProver_top
% 2.98/1.01      | r1_ordinal1(sK5,sK6) = iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_5616]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5668,plain,
% 2.98/1.01      ( r1_ordinal1(sK5,sK6) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) = iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_5346,c_39,c_40,c_56,c_67,c_70,c_3234,c_3282,c_5618]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5674,plain,
% 2.98/1.01      ( r1_tarski(sK5,sK6) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) = iProver_top
% 2.98/1.01      | v3_ordinal1(sK6) != iProver_top
% 2.98/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_5668,c_2653]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5744,plain,
% 2.98/1.01      ( r1_tarski(sK5,sK6) = iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) = iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_5674,c_38,c_39]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6,plain,
% 2.98/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.98/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2676,plain,
% 2.98/1.01      ( X0 = X1
% 2.98/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.98/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5751,plain,
% 2.98/1.01      ( sK6 = sK5
% 2.98/1.01      | r1_tarski(sK6,sK5) != iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) = iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_5744,c_2676]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_11,plain,
% 2.98/1.01      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f134]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_92,plain,
% 2.98/1.01      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_94,plain,
% 2.98/1.01      ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_92]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1861,plain,
% 2.98/1.01      ( X0 != X1
% 2.98/1.01      | X2 != X3
% 2.98/1.01      | X4 != X5
% 2.98/1.01      | X6 != X7
% 2.98/1.01      | X8 != X9
% 2.98/1.01      | X10 != X11
% 2.98/1.01      | X12 != X13
% 2.98/1.01      | X14 != X15
% 2.98/1.01      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 2.98/1.01      theory(equality) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1868,plain,
% 2.98/1.01      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.98/1.01      | sK6 != sK6 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1861]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1863,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.98/1.01      theory(equality) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2938,plain,
% 2.98/1.01      ( r2_hidden(X0,X1)
% 2.98/1.01      | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 2.98/1.01      | X0 != X2
% 2.98/1.01      | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1863]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3227,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 2.98/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.98/1.01      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 2.98/1.01      | sK5 != X0 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_2938]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3228,plain,
% 2.98/1.01      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 2.98/1.01      | sK5 != X0
% 2.98/1.01      | r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
% 2.98/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_3227]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3230,plain,
% 2.98/1.01      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.98/1.01      | sK5 != sK6
% 2.98/1.01      | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.98/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_3228]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3278,plain,
% 2.98/1.01      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3284,plain,
% 2.98/1.01      ( sK5 = X0
% 2.98/1.01      | r1_tarski(X0,sK5) != iProver_top
% 2.98/1.01      | r1_tarski(sK5,X0) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_3278]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3286,plain,
% 2.98/1.01      ( sK5 = sK6
% 2.98/1.01      | r1_tarski(sK6,sK5) != iProver_top
% 2.98/1.01      | r1_tarski(sK5,sK6) != iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_3284]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,X1)
% 2.98/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.98/1.01      inference(cnf_transformation,[],[f128]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2679,plain,
% 2.98/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.98/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_4150,plain,
% 2.98/1.01      ( r1_ordinal1(sK5,sK6) != iProver_top
% 2.98/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_2679,c_2651]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5760,plain,
% 2.98/1.01      ( r1_tarski(sK6,sK5) != iProver_top
% 2.98/1.01      | r2_hidden(sK5,sK6) = iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_5751,c_38,c_39,c_67,c_70,c_94,c_1868,c_3230,c_3286,
% 2.98/1.01                 c_4150,c_5668,c_5674]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_8144,plain,
% 2.98/1.01      ( r2_hidden(sK5,sK6) = iProver_top
% 2.98/1.01      | v3_ordinal1(sK6) != iProver_top
% 2.98/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_4823,c_5760]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_8768,plain,
% 2.98/1.01      ( r1_tarski(sK6,sK5) = iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_8383,c_38,c_39,c_3953,c_4607,c_8144]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_8776,plain,
% 2.98/1.01      ( r2_hidden(sK5,sK6) = iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_8768,c_5760]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2647,plain,
% 2.98/1.01      ( r1_tarski(X0,X1) = iProver_top
% 2.98/1.01      | r2_hidden(X0,X1) != iProver_top
% 2.98/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_9067,plain,
% 2.98/1.01      ( r1_tarski(sK5,sK6) = iProver_top
% 2.98/1.01      | v3_ordinal1(sK6) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_8776,c_2647]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_31,plain,
% 2.98/1.01      ( r1_ordinal1(X0,X1)
% 2.98/1.01      | ~ r1_tarski(X0,X1)
% 2.98/1.01      | ~ v3_ordinal1(X0)
% 2.98/1.01      | ~ v3_ordinal1(X1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f102]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5607,plain,
% 2.98/1.01      ( r1_ordinal1(sK5,sK6)
% 2.98/1.01      | ~ r1_tarski(sK5,sK6)
% 2.98/1.01      | ~ v3_ordinal1(sK6)
% 2.98/1.01      | ~ v3_ordinal1(sK5) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_31]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5611,plain,
% 2.98/1.01      ( r1_ordinal1(sK5,sK6) = iProver_top
% 2.98/1.01      | r1_tarski(sK5,sK6) != iProver_top
% 2.98/1.01      | v3_ordinal1(sK6) != iProver_top
% 2.98/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_5607]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(contradiction,plain,
% 2.98/1.01      ( $false ),
% 2.98/1.01      inference(minisat,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_9067,c_8144,c_5611,c_4028,c_39,c_38]) ).
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  ------                               Statistics
% 2.98/1.01  
% 2.98/1.01  ------ General
% 2.98/1.01  
% 2.98/1.01  abstr_ref_over_cycles:                  0
% 2.98/1.01  abstr_ref_under_cycles:                 0
% 2.98/1.01  gc_basic_clause_elim:                   0
% 2.98/1.01  forced_gc_time:                         0
% 2.98/1.01  parsing_time:                           0.012
% 2.98/1.01  unif_index_cands_time:                  0.
% 2.98/1.01  unif_index_add_time:                    0.
% 2.98/1.01  orderings_time:                         0.
% 2.98/1.01  out_proof_time:                         0.01
% 2.98/1.01  total_time:                             0.316
% 2.98/1.01  num_of_symbols:                         45
% 2.98/1.01  num_of_terms:                           9133
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing
% 2.98/1.01  
% 2.98/1.01  num_of_splits:                          0
% 2.98/1.01  num_of_split_atoms:                     0
% 2.98/1.01  num_of_reused_defs:                     0
% 2.98/1.01  num_eq_ax_congr_red:                    97
% 2.98/1.01  num_of_sem_filtered_clauses:            1
% 2.98/1.01  num_of_subtypes:                        0
% 2.98/1.01  monotx_restored_types:                  0
% 2.98/1.01  sat_num_of_epr_types:                   0
% 2.98/1.01  sat_num_of_non_cyclic_types:            0
% 2.98/1.01  sat_guarded_non_collapsed_types:        0
% 2.98/1.01  num_pure_diseq_elim:                    0
% 2.98/1.01  simp_replaced_by:                       0
% 2.98/1.01  res_preprocessed:                       164
% 2.98/1.01  prep_upred:                             0
% 2.98/1.01  prep_unflattend:                        597
% 2.98/1.01  smt_new_axioms:                         0
% 2.98/1.01  pred_elim_cands:                        6
% 2.98/1.01  pred_elim:                              1
% 2.98/1.01  pred_elim_cl:                           1
% 2.98/1.01  pred_elim_cycles:                       5
% 2.98/1.01  merged_defs:                            8
% 2.98/1.01  merged_defs_ncl:                        0
% 2.98/1.01  bin_hyper_res:                          8
% 2.98/1.01  prep_cycles:                            4
% 2.98/1.01  pred_elim_time:                         0.023
% 2.98/1.01  splitting_time:                         0.
% 2.98/1.01  sem_filter_time:                        0.
% 2.98/1.01  monotx_time:                            0.001
% 2.98/1.01  subtype_inf_time:                       0.
% 2.98/1.01  
% 2.98/1.01  ------ Problem properties
% 2.98/1.01  
% 2.98/1.01  clauses:                                36
% 2.98/1.01  conjectures:                            4
% 2.98/1.01  epr:                                    20
% 2.98/1.01  horn:                                   28
% 2.98/1.01  ground:                                 4
% 2.98/1.01  unary:                                  13
% 2.98/1.01  binary:                                 6
% 2.98/1.01  lits:                                   87
% 2.98/1.01  lits_eq:                                18
% 2.98/1.01  fd_pure:                                0
% 2.98/1.01  fd_pseudo:                              0
% 2.98/1.01  fd_cond:                                0
% 2.98/1.01  fd_pseudo_cond:                         8
% 2.98/1.01  ac_symbols:                             0
% 2.98/1.01  
% 2.98/1.01  ------ Propositional Solver
% 2.98/1.01  
% 2.98/1.01  prop_solver_calls:                      26
% 2.98/1.01  prop_fast_solver_calls:                 1230
% 2.98/1.01  smt_solver_calls:                       0
% 2.98/1.01  smt_fast_solver_calls:                  0
% 2.98/1.01  prop_num_of_clauses:                    2580
% 2.98/1.01  prop_preprocess_simplified:             9372
% 2.98/1.01  prop_fo_subsumed:                       12
% 2.98/1.01  prop_solver_time:                       0.
% 2.98/1.01  smt_solver_time:                        0.
% 2.98/1.01  smt_fast_solver_time:                   0.
% 2.98/1.01  prop_fast_solver_time:                  0.
% 2.98/1.01  prop_unsat_core_time:                   0.
% 2.98/1.01  
% 2.98/1.01  ------ QBF
% 2.98/1.01  
% 2.98/1.01  qbf_q_res:                              0
% 2.98/1.01  qbf_num_tautologies:                    0
% 2.98/1.01  qbf_prep_cycles:                        0
% 2.98/1.01  
% 2.98/1.01  ------ BMC1
% 2.98/1.01  
% 2.98/1.01  bmc1_current_bound:                     -1
% 2.98/1.01  bmc1_last_solved_bound:                 -1
% 2.98/1.01  bmc1_unsat_core_size:                   -1
% 2.98/1.01  bmc1_unsat_core_parents_size:           -1
% 2.98/1.01  bmc1_merge_next_fun:                    0
% 2.98/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.98/1.01  
% 2.98/1.01  ------ Instantiation
% 2.98/1.01  
% 2.98/1.01  inst_num_of_clauses:                    701
% 2.98/1.01  inst_num_in_passive:                    70
% 2.98/1.01  inst_num_in_active:                     304
% 2.98/1.01  inst_num_in_unprocessed:                327
% 2.98/1.01  inst_num_of_loops:                      390
% 2.98/1.01  inst_num_of_learning_restarts:          0
% 2.98/1.01  inst_num_moves_active_passive:          84
% 2.98/1.01  inst_lit_activity:                      0
% 2.98/1.01  inst_lit_activity_moves:                0
% 2.98/1.01  inst_num_tautologies:                   0
% 2.98/1.01  inst_num_prop_implied:                  0
% 2.98/1.01  inst_num_existing_simplified:           0
% 2.98/1.01  inst_num_eq_res_simplified:             0
% 2.98/1.01  inst_num_child_elim:                    0
% 2.98/1.01  inst_num_of_dismatching_blockings:      475
% 2.98/1.01  inst_num_of_non_proper_insts:           968
% 2.98/1.01  inst_num_of_duplicates:                 0
% 2.98/1.01  inst_inst_num_from_inst_to_res:         0
% 2.98/1.01  inst_dismatching_checking_time:         0.
% 2.98/1.01  
% 2.98/1.01  ------ Resolution
% 2.98/1.01  
% 2.98/1.01  res_num_of_clauses:                     0
% 2.98/1.01  res_num_in_passive:                     0
% 2.98/1.01  res_num_in_active:                      0
% 2.98/1.01  res_num_of_loops:                       168
% 2.98/1.01  res_forward_subset_subsumed:            44
% 2.98/1.01  res_backward_subset_subsumed:           2
% 2.98/1.01  res_forward_subsumed:                   0
% 2.98/1.01  res_backward_subsumed:                  0
% 2.98/1.01  res_forward_subsumption_resolution:     0
% 2.98/1.01  res_backward_subsumption_resolution:    0
% 2.98/1.01  res_clause_to_clause_subsumption:       1526
% 2.98/1.01  res_orphan_elimination:                 0
% 2.98/1.01  res_tautology_del:                      64
% 2.98/1.01  res_num_eq_res_simplified:              0
% 2.98/1.01  res_num_sel_changes:                    0
% 2.98/1.01  res_moves_from_active_to_pass:          0
% 2.98/1.01  
% 2.98/1.01  ------ Superposition
% 2.98/1.01  
% 2.98/1.01  sup_time_total:                         0.
% 2.98/1.01  sup_time_generating:                    0.
% 2.98/1.01  sup_time_sim_full:                      0.
% 2.98/1.01  sup_time_sim_immed:                     0.
% 2.98/1.01  
% 2.98/1.01  sup_num_of_clauses:                     133
% 2.98/1.01  sup_num_in_active:                      77
% 2.98/1.01  sup_num_in_passive:                     56
% 2.98/1.01  sup_num_of_loops:                       76
% 2.98/1.01  sup_fw_superposition:                   63
% 2.98/1.01  sup_bw_superposition:                   96
% 2.98/1.01  sup_immediate_simplified:               18
% 2.98/1.01  sup_given_eliminated:                   0
% 2.98/1.01  comparisons_done:                       0
% 2.98/1.01  comparisons_avoided:                    2
% 2.98/1.01  
% 2.98/1.01  ------ Simplifications
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  sim_fw_subset_subsumed:                 11
% 2.98/1.01  sim_bw_subset_subsumed:                 1
% 2.98/1.01  sim_fw_subsumed:                        10
% 2.98/1.01  sim_bw_subsumed:                        0
% 2.98/1.01  sim_fw_subsumption_res:                 0
% 2.98/1.01  sim_bw_subsumption_res:                 0
% 2.98/1.01  sim_tautology_del:                      11
% 2.98/1.01  sim_eq_tautology_del:                   6
% 2.98/1.01  sim_eq_res_simp:                        8
% 2.98/1.01  sim_fw_demodulated:                     0
% 2.98/1.01  sim_bw_demodulated:                     0
% 2.98/1.01  sim_light_normalised:                   0
% 2.98/1.01  sim_joinable_taut:                      0
% 2.98/1.01  sim_joinable_simp:                      0
% 2.98/1.01  sim_ac_normalised:                      0
% 2.98/1.01  sim_smt_subsumption:                    0
% 2.98/1.01  
%------------------------------------------------------------------------------
