%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:57 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 609 expanded)
%              Number of clauses        :   60 (  91 expanded)
%              Number of leaves         :   23 ( 169 expanded)
%              Depth                    :   14
%              Number of atoms          :  521 (1899 expanded)
%              Number of equality atoms :  205 ( 648 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f54,plain,
    ( ( ~ r1_ordinal1(sK5,sK6)
      | ~ r2_hidden(sK5,k1_ordinal1(sK6)) )
    & ( r1_ordinal1(sK5,sK6)
      | r2_hidden(sK5,k1_ordinal1(sK6)) )
    & v3_ordinal1(sK6)
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f51,f53,f52])).

fof(f99,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f105,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f74,f104])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f100])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f101])).

fof(f103,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f102])).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f103])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f104])).

fof(f107,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f91,f105,f106])).

fof(f120,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f99,f107])).

fof(f96,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f97,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f118,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f62,f104])).

fof(f127,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f118])).

fof(f128,plain,(
    ! [X4,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f127])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f57,f105])).

fof(f122,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f111])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f105])).

fof(f123,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f61,f104])).

fof(f129,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f119])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f105])).

fof(f124,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f113])).

fof(f98,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f54])).

fof(f121,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f98,f107])).

cnf(c_1840,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3156,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(sK5,sK6)
    | sK6 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_3158,plain,
    ( ~ r1_ordinal1(sK6,sK6)
    | r1_ordinal1(sK5,sK6)
    | sK6 != sK6
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_3156])).

cnf(c_32,negated_conjecture,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2562,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_36,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_37,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_39,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_41,plain,
    ( ~ r1_tarski(sK6,sK6)
    | ~ r2_hidden(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_30,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_44,plain,
    ( r2_hidden(sK6,sK6)
    | ~ v3_ordinal1(sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_47,plain,
    ( r1_tarski(sK6,sK6)
    | ~ r1_ordinal1(sK6,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_27,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_53,plain,
    ( r1_ordinal1(sK6,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_10,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_87,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_89,plain,
    ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_1835,plain,
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

cnf(c_1842,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1835])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2635,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2636,plain,
    ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2635])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2638,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ r2_hidden(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2639,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top
    | r2_hidden(sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2638])).

cnf(c_455,plain,
    ( ~ r1_ordinal1(X0,X1)
    | ~ r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_29,c_31])).

cnf(c_2651,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK6,sK5)
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_2652,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top
    | r2_hidden(sK6,sK5) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2651])).

cnf(c_2804,plain,
    ( r2_hidden(X0,sK5)
    | r2_hidden(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2805,plain,
    ( sK5 = X0
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(sK5,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2804])).

cnf(c_2807,plain,
    ( sK5 = sK6
    | r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK5,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2805])).

cnf(c_1837,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2684,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_2956,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2684])).

cnf(c_2957,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
    | sK5 != X1
    | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2956])).

cnf(c_2959,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK5 != sK6
    | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2957])).

cnf(c_2993,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2562,c_36,c_34,c_37,c_39,c_41,c_44,c_47,c_53,c_89,c_1842,c_2636,c_2639,c_2652,c_2807,c_2959])).

cnf(c_2958,plain,
    ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_2956])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2795,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | sK5 = X0
    | sK5 = X1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2796,plain,
    ( sK5 = X0
    | sK5 = X1
    | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2795])).

cnf(c_2798,plain,
    ( sK5 = sK6
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2796])).

cnf(c_2769,plain,
    ( r1_ordinal1(X0,sK5)
    | r1_ordinal1(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2770,plain,
    ( r1_ordinal1(X0,sK5) = iProver_top
    | r1_ordinal1(sK5,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2769])).

cnf(c_2772,plain,
    ( r1_ordinal1(sK6,sK5) = iProver_top
    | r1_ordinal1(sK5,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2770])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2674,plain,
    ( r2_hidden(sK5,X0)
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2675,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2674])).

cnf(c_2677,plain,
    ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2675])).

cnf(c_2666,plain,
    ( ~ r1_ordinal1(X0,sK5)
    | ~ r2_hidden(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_2667,plain,
    ( r1_ordinal1(X0,sK5) != iProver_top
    | r2_hidden(sK5,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2666])).

cnf(c_2669,plain,
    ( r1_ordinal1(sK6,sK5) != iProver_top
    | r2_hidden(sK5,sK6) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2667])).

cnf(c_88,plain,
    ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_33,negated_conjecture,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_38,plain,
    ( r1_ordinal1(sK5,sK6) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3158,c_2993,c_2958,c_2798,c_2772,c_2677,c_2669,c_2635,c_1842,c_88,c_53,c_47,c_44,c_41,c_32,c_38,c_37,c_34,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.72/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.01  
% 2.72/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.72/1.01  
% 2.72/1.01  ------  iProver source info
% 2.72/1.01  
% 2.72/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.72/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.72/1.01  git: non_committed_changes: false
% 2.72/1.01  git: last_make_outside_of_git: false
% 2.72/1.01  
% 2.72/1.01  ------ 
% 2.72/1.01  
% 2.72/1.01  ------ Input Options
% 2.72/1.01  
% 2.72/1.01  --out_options                           all
% 2.72/1.01  --tptp_safe_out                         true
% 2.72/1.01  --problem_path                          ""
% 2.72/1.01  --include_path                          ""
% 2.72/1.01  --clausifier                            res/vclausify_rel
% 2.72/1.01  --clausifier_options                    ""
% 2.72/1.01  --stdin                                 false
% 2.72/1.01  --stats_out                             all
% 2.72/1.01  
% 2.72/1.01  ------ General Options
% 2.72/1.01  
% 2.72/1.01  --fof                                   false
% 2.72/1.01  --time_out_real                         305.
% 2.72/1.01  --time_out_virtual                      -1.
% 2.72/1.01  --symbol_type_check                     false
% 2.72/1.01  --clausify_out                          false
% 2.72/1.01  --sig_cnt_out                           false
% 2.72/1.01  --trig_cnt_out                          false
% 2.72/1.01  --trig_cnt_out_tolerance                1.
% 2.72/1.01  --trig_cnt_out_sk_spl                   false
% 2.72/1.01  --abstr_cl_out                          false
% 2.72/1.01  
% 2.72/1.01  ------ Global Options
% 2.72/1.01  
% 2.72/1.01  --schedule                              default
% 2.72/1.01  --add_important_lit                     false
% 2.72/1.01  --prop_solver_per_cl                    1000
% 2.72/1.01  --min_unsat_core                        false
% 2.72/1.01  --soft_assumptions                      false
% 2.72/1.01  --soft_lemma_size                       3
% 2.72/1.01  --prop_impl_unit_size                   0
% 2.72/1.01  --prop_impl_unit                        []
% 2.72/1.01  --share_sel_clauses                     true
% 2.72/1.01  --reset_solvers                         false
% 2.72/1.01  --bc_imp_inh                            [conj_cone]
% 2.72/1.01  --conj_cone_tolerance                   3.
% 2.72/1.01  --extra_neg_conj                        none
% 2.72/1.01  --large_theory_mode                     true
% 2.72/1.01  --prolific_symb_bound                   200
% 2.72/1.01  --lt_threshold                          2000
% 2.72/1.01  --clause_weak_htbl                      true
% 2.72/1.01  --gc_record_bc_elim                     false
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing Options
% 2.72/1.01  
% 2.72/1.01  --preprocessing_flag                    true
% 2.72/1.01  --time_out_prep_mult                    0.1
% 2.72/1.01  --splitting_mode                        input
% 2.72/1.01  --splitting_grd                         true
% 2.72/1.01  --splitting_cvd                         false
% 2.72/1.01  --splitting_cvd_svl                     false
% 2.72/1.01  --splitting_nvd                         32
% 2.72/1.01  --sub_typing                            true
% 2.72/1.01  --prep_gs_sim                           true
% 2.72/1.01  --prep_unflatten                        true
% 2.72/1.01  --prep_res_sim                          true
% 2.72/1.01  --prep_upred                            true
% 2.72/1.01  --prep_sem_filter                       exhaustive
% 2.72/1.01  --prep_sem_filter_out                   false
% 2.72/1.01  --pred_elim                             true
% 2.72/1.01  --res_sim_input                         true
% 2.72/1.01  --eq_ax_congr_red                       true
% 2.72/1.01  --pure_diseq_elim                       true
% 2.72/1.01  --brand_transform                       false
% 2.72/1.01  --non_eq_to_eq                          false
% 2.72/1.01  --prep_def_merge                        true
% 2.72/1.01  --prep_def_merge_prop_impl              false
% 2.72/1.01  --prep_def_merge_mbd                    true
% 2.72/1.01  --prep_def_merge_tr_red                 false
% 2.72/1.01  --prep_def_merge_tr_cl                  false
% 2.72/1.01  --smt_preprocessing                     true
% 2.72/1.01  --smt_ac_axioms                         fast
% 2.72/1.01  --preprocessed_out                      false
% 2.72/1.01  --preprocessed_stats                    false
% 2.72/1.01  
% 2.72/1.01  ------ Abstraction refinement Options
% 2.72/1.01  
% 2.72/1.01  --abstr_ref                             []
% 2.72/1.01  --abstr_ref_prep                        false
% 2.72/1.01  --abstr_ref_until_sat                   false
% 2.72/1.01  --abstr_ref_sig_restrict                funpre
% 2.72/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/1.01  --abstr_ref_under                       []
% 2.72/1.01  
% 2.72/1.01  ------ SAT Options
% 2.72/1.01  
% 2.72/1.01  --sat_mode                              false
% 2.72/1.01  --sat_fm_restart_options                ""
% 2.72/1.01  --sat_gr_def                            false
% 2.72/1.01  --sat_epr_types                         true
% 2.72/1.01  --sat_non_cyclic_types                  false
% 2.72/1.01  --sat_finite_models                     false
% 2.72/1.01  --sat_fm_lemmas                         false
% 2.72/1.01  --sat_fm_prep                           false
% 2.72/1.01  --sat_fm_uc_incr                        true
% 2.72/1.01  --sat_out_model                         small
% 2.72/1.01  --sat_out_clauses                       false
% 2.72/1.01  
% 2.72/1.01  ------ QBF Options
% 2.72/1.01  
% 2.72/1.01  --qbf_mode                              false
% 2.72/1.01  --qbf_elim_univ                         false
% 2.72/1.01  --qbf_dom_inst                          none
% 2.72/1.01  --qbf_dom_pre_inst                      false
% 2.72/1.01  --qbf_sk_in                             false
% 2.72/1.01  --qbf_pred_elim                         true
% 2.72/1.01  --qbf_split                             512
% 2.72/1.01  
% 2.72/1.01  ------ BMC1 Options
% 2.72/1.01  
% 2.72/1.01  --bmc1_incremental                      false
% 2.72/1.01  --bmc1_axioms                           reachable_all
% 2.72/1.01  --bmc1_min_bound                        0
% 2.72/1.01  --bmc1_max_bound                        -1
% 2.72/1.01  --bmc1_max_bound_default                -1
% 2.72/1.01  --bmc1_symbol_reachability              true
% 2.72/1.01  --bmc1_property_lemmas                  false
% 2.72/1.01  --bmc1_k_induction                      false
% 2.72/1.01  --bmc1_non_equiv_states                 false
% 2.72/1.01  --bmc1_deadlock                         false
% 2.72/1.01  --bmc1_ucm                              false
% 2.72/1.01  --bmc1_add_unsat_core                   none
% 2.72/1.01  --bmc1_unsat_core_children              false
% 2.72/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/1.01  --bmc1_out_stat                         full
% 2.72/1.01  --bmc1_ground_init                      false
% 2.72/1.01  --bmc1_pre_inst_next_state              false
% 2.72/1.01  --bmc1_pre_inst_state                   false
% 2.72/1.01  --bmc1_pre_inst_reach_state             false
% 2.72/1.01  --bmc1_out_unsat_core                   false
% 2.72/1.01  --bmc1_aig_witness_out                  false
% 2.72/1.01  --bmc1_verbose                          false
% 2.72/1.01  --bmc1_dump_clauses_tptp                false
% 2.72/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.72/1.01  --bmc1_dump_file                        -
% 2.72/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.72/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.72/1.01  --bmc1_ucm_extend_mode                  1
% 2.72/1.01  --bmc1_ucm_init_mode                    2
% 2.72/1.01  --bmc1_ucm_cone_mode                    none
% 2.72/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.72/1.01  --bmc1_ucm_relax_model                  4
% 2.72/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.72/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/1.01  --bmc1_ucm_layered_model                none
% 2.72/1.01  --bmc1_ucm_max_lemma_size               10
% 2.72/1.01  
% 2.72/1.01  ------ AIG Options
% 2.72/1.01  
% 2.72/1.01  --aig_mode                              false
% 2.72/1.01  
% 2.72/1.01  ------ Instantiation Options
% 2.72/1.01  
% 2.72/1.01  --instantiation_flag                    true
% 2.72/1.01  --inst_sos_flag                         true
% 2.72/1.01  --inst_sos_phase                        true
% 2.72/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/1.01  --inst_lit_sel_side                     num_symb
% 2.72/1.01  --inst_solver_per_active                1400
% 2.72/1.01  --inst_solver_calls_frac                1.
% 2.72/1.01  --inst_passive_queue_type               priority_queues
% 2.72/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/1.01  --inst_passive_queues_freq              [25;2]
% 2.72/1.01  --inst_dismatching                      true
% 2.72/1.01  --inst_eager_unprocessed_to_passive     true
% 2.72/1.01  --inst_prop_sim_given                   true
% 2.72/1.01  --inst_prop_sim_new                     false
% 2.72/1.01  --inst_subs_new                         false
% 2.72/1.01  --inst_eq_res_simp                      false
% 2.72/1.01  --inst_subs_given                       false
% 2.72/1.01  --inst_orphan_elimination               true
% 2.72/1.01  --inst_learning_loop_flag               true
% 2.72/1.01  --inst_learning_start                   3000
% 2.72/1.01  --inst_learning_factor                  2
% 2.72/1.01  --inst_start_prop_sim_after_learn       3
% 2.72/1.01  --inst_sel_renew                        solver
% 2.72/1.01  --inst_lit_activity_flag                true
% 2.72/1.01  --inst_restr_to_given                   false
% 2.72/1.01  --inst_activity_threshold               500
% 2.72/1.01  --inst_out_proof                        true
% 2.72/1.01  
% 2.72/1.01  ------ Resolution Options
% 2.72/1.01  
% 2.72/1.01  --resolution_flag                       true
% 2.72/1.01  --res_lit_sel                           adaptive
% 2.72/1.01  --res_lit_sel_side                      none
% 2.72/1.01  --res_ordering                          kbo
% 2.72/1.01  --res_to_prop_solver                    active
% 2.72/1.01  --res_prop_simpl_new                    false
% 2.72/1.01  --res_prop_simpl_given                  true
% 2.72/1.01  --res_passive_queue_type                priority_queues
% 2.72/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/1.01  --res_passive_queues_freq               [15;5]
% 2.72/1.01  --res_forward_subs                      full
% 2.72/1.01  --res_backward_subs                     full
% 2.72/1.01  --res_forward_subs_resolution           true
% 2.72/1.01  --res_backward_subs_resolution          true
% 2.72/1.01  --res_orphan_elimination                true
% 2.72/1.01  --res_time_limit                        2.
% 2.72/1.01  --res_out_proof                         true
% 2.72/1.01  
% 2.72/1.01  ------ Superposition Options
% 2.72/1.01  
% 2.72/1.01  --superposition_flag                    true
% 2.72/1.01  --sup_passive_queue_type                priority_queues
% 2.72/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.72/1.01  --demod_completeness_check              fast
% 2.72/1.01  --demod_use_ground                      true
% 2.72/1.01  --sup_to_prop_solver                    passive
% 2.72/1.01  --sup_prop_simpl_new                    true
% 2.72/1.01  --sup_prop_simpl_given                  true
% 2.72/1.01  --sup_fun_splitting                     true
% 2.72/1.01  --sup_smt_interval                      50000
% 2.72/1.01  
% 2.72/1.01  ------ Superposition Simplification Setup
% 2.72/1.01  
% 2.72/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.72/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.72/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.72/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.72/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.72/1.01  --sup_immed_triv                        [TrivRules]
% 2.72/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/1.01  --sup_immed_bw_main                     []
% 2.72/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.72/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/1.01  --sup_input_bw                          []
% 2.72/1.01  
% 2.72/1.01  ------ Combination Options
% 2.72/1.01  
% 2.72/1.01  --comb_res_mult                         3
% 2.72/1.01  --comb_sup_mult                         2
% 2.72/1.01  --comb_inst_mult                        10
% 2.72/1.01  
% 2.72/1.01  ------ Debug Options
% 2.72/1.01  
% 2.72/1.01  --dbg_backtrace                         false
% 2.72/1.01  --dbg_dump_prop_clauses                 false
% 2.72/1.01  --dbg_dump_prop_clauses_file            -
% 2.72/1.01  --dbg_out_stat                          false
% 2.72/1.01  ------ Parsing...
% 2.72/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.72/1.01  ------ Proving...
% 2.72/1.01  ------ Problem Properties 
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  clauses                                 34
% 2.72/1.01  conjectures                             4
% 2.72/1.01  EPR                                     16
% 2.72/1.01  Horn                                    25
% 2.72/1.01  unary                                   13
% 2.72/1.01  binary                                  5
% 2.72/1.01  lits                                    83
% 2.72/1.01  lits eq                                 22
% 2.72/1.01  fd_pure                                 0
% 2.72/1.01  fd_pseudo                               0
% 2.72/1.01  fd_cond                                 0
% 2.72/1.01  fd_pseudo_cond                          9
% 2.72/1.01  AC symbols                              0
% 2.72/1.01  
% 2.72/1.01  ------ Schedule dynamic 5 is on 
% 2.72/1.01  
% 2.72/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  ------ 
% 2.72/1.01  Current options:
% 2.72/1.01  ------ 
% 2.72/1.01  
% 2.72/1.01  ------ Input Options
% 2.72/1.01  
% 2.72/1.01  --out_options                           all
% 2.72/1.01  --tptp_safe_out                         true
% 2.72/1.01  --problem_path                          ""
% 2.72/1.01  --include_path                          ""
% 2.72/1.01  --clausifier                            res/vclausify_rel
% 2.72/1.01  --clausifier_options                    ""
% 2.72/1.01  --stdin                                 false
% 2.72/1.01  --stats_out                             all
% 2.72/1.01  
% 2.72/1.01  ------ General Options
% 2.72/1.01  
% 2.72/1.01  --fof                                   false
% 2.72/1.01  --time_out_real                         305.
% 2.72/1.01  --time_out_virtual                      -1.
% 2.72/1.01  --symbol_type_check                     false
% 2.72/1.01  --clausify_out                          false
% 2.72/1.01  --sig_cnt_out                           false
% 2.72/1.01  --trig_cnt_out                          false
% 2.72/1.01  --trig_cnt_out_tolerance                1.
% 2.72/1.01  --trig_cnt_out_sk_spl                   false
% 2.72/1.01  --abstr_cl_out                          false
% 2.72/1.01  
% 2.72/1.01  ------ Global Options
% 2.72/1.01  
% 2.72/1.01  --schedule                              default
% 2.72/1.01  --add_important_lit                     false
% 2.72/1.01  --prop_solver_per_cl                    1000
% 2.72/1.01  --min_unsat_core                        false
% 2.72/1.01  --soft_assumptions                      false
% 2.72/1.01  --soft_lemma_size                       3
% 2.72/1.01  --prop_impl_unit_size                   0
% 2.72/1.01  --prop_impl_unit                        []
% 2.72/1.01  --share_sel_clauses                     true
% 2.72/1.01  --reset_solvers                         false
% 2.72/1.01  --bc_imp_inh                            [conj_cone]
% 2.72/1.01  --conj_cone_tolerance                   3.
% 2.72/1.01  --extra_neg_conj                        none
% 2.72/1.01  --large_theory_mode                     true
% 2.72/1.01  --prolific_symb_bound                   200
% 2.72/1.01  --lt_threshold                          2000
% 2.72/1.01  --clause_weak_htbl                      true
% 2.72/1.01  --gc_record_bc_elim                     false
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing Options
% 2.72/1.01  
% 2.72/1.01  --preprocessing_flag                    true
% 2.72/1.01  --time_out_prep_mult                    0.1
% 2.72/1.01  --splitting_mode                        input
% 2.72/1.01  --splitting_grd                         true
% 2.72/1.01  --splitting_cvd                         false
% 2.72/1.01  --splitting_cvd_svl                     false
% 2.72/1.01  --splitting_nvd                         32
% 2.72/1.01  --sub_typing                            true
% 2.72/1.01  --prep_gs_sim                           true
% 2.72/1.01  --prep_unflatten                        true
% 2.72/1.01  --prep_res_sim                          true
% 2.72/1.01  --prep_upred                            true
% 2.72/1.01  --prep_sem_filter                       exhaustive
% 2.72/1.01  --prep_sem_filter_out                   false
% 2.72/1.01  --pred_elim                             true
% 2.72/1.01  --res_sim_input                         true
% 2.72/1.01  --eq_ax_congr_red                       true
% 2.72/1.01  --pure_diseq_elim                       true
% 2.72/1.01  --brand_transform                       false
% 2.72/1.01  --non_eq_to_eq                          false
% 2.72/1.01  --prep_def_merge                        true
% 2.72/1.01  --prep_def_merge_prop_impl              false
% 2.72/1.01  --prep_def_merge_mbd                    true
% 2.72/1.01  --prep_def_merge_tr_red                 false
% 2.72/1.01  --prep_def_merge_tr_cl                  false
% 2.72/1.01  --smt_preprocessing                     true
% 2.72/1.01  --smt_ac_axioms                         fast
% 2.72/1.01  --preprocessed_out                      false
% 2.72/1.01  --preprocessed_stats                    false
% 2.72/1.01  
% 2.72/1.01  ------ Abstraction refinement Options
% 2.72/1.01  
% 2.72/1.01  --abstr_ref                             []
% 2.72/1.01  --abstr_ref_prep                        false
% 2.72/1.01  --abstr_ref_until_sat                   false
% 2.72/1.01  --abstr_ref_sig_restrict                funpre
% 2.72/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/1.01  --abstr_ref_under                       []
% 2.72/1.01  
% 2.72/1.01  ------ SAT Options
% 2.72/1.01  
% 2.72/1.01  --sat_mode                              false
% 2.72/1.01  --sat_fm_restart_options                ""
% 2.72/1.01  --sat_gr_def                            false
% 2.72/1.01  --sat_epr_types                         true
% 2.72/1.01  --sat_non_cyclic_types                  false
% 2.72/1.01  --sat_finite_models                     false
% 2.72/1.01  --sat_fm_lemmas                         false
% 2.72/1.01  --sat_fm_prep                           false
% 2.72/1.01  --sat_fm_uc_incr                        true
% 2.72/1.01  --sat_out_model                         small
% 2.72/1.01  --sat_out_clauses                       false
% 2.72/1.01  
% 2.72/1.01  ------ QBF Options
% 2.72/1.01  
% 2.72/1.01  --qbf_mode                              false
% 2.72/1.01  --qbf_elim_univ                         false
% 2.72/1.01  --qbf_dom_inst                          none
% 2.72/1.01  --qbf_dom_pre_inst                      false
% 2.72/1.01  --qbf_sk_in                             false
% 2.72/1.01  --qbf_pred_elim                         true
% 2.72/1.01  --qbf_split                             512
% 2.72/1.01  
% 2.72/1.01  ------ BMC1 Options
% 2.72/1.01  
% 2.72/1.01  --bmc1_incremental                      false
% 2.72/1.01  --bmc1_axioms                           reachable_all
% 2.72/1.01  --bmc1_min_bound                        0
% 2.72/1.01  --bmc1_max_bound                        -1
% 2.72/1.01  --bmc1_max_bound_default                -1
% 2.72/1.01  --bmc1_symbol_reachability              true
% 2.72/1.01  --bmc1_property_lemmas                  false
% 2.72/1.01  --bmc1_k_induction                      false
% 2.72/1.01  --bmc1_non_equiv_states                 false
% 2.72/1.01  --bmc1_deadlock                         false
% 2.72/1.01  --bmc1_ucm                              false
% 2.72/1.01  --bmc1_add_unsat_core                   none
% 2.72/1.01  --bmc1_unsat_core_children              false
% 2.72/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/1.01  --bmc1_out_stat                         full
% 2.72/1.01  --bmc1_ground_init                      false
% 2.72/1.01  --bmc1_pre_inst_next_state              false
% 2.72/1.01  --bmc1_pre_inst_state                   false
% 2.72/1.01  --bmc1_pre_inst_reach_state             false
% 2.72/1.01  --bmc1_out_unsat_core                   false
% 2.72/1.01  --bmc1_aig_witness_out                  false
% 2.72/1.01  --bmc1_verbose                          false
% 2.72/1.01  --bmc1_dump_clauses_tptp                false
% 2.72/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.72/1.01  --bmc1_dump_file                        -
% 2.72/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.72/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.72/1.01  --bmc1_ucm_extend_mode                  1
% 2.72/1.01  --bmc1_ucm_init_mode                    2
% 2.72/1.01  --bmc1_ucm_cone_mode                    none
% 2.72/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.72/1.01  --bmc1_ucm_relax_model                  4
% 2.72/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.72/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/1.01  --bmc1_ucm_layered_model                none
% 2.72/1.01  --bmc1_ucm_max_lemma_size               10
% 2.72/1.01  
% 2.72/1.01  ------ AIG Options
% 2.72/1.01  
% 2.72/1.01  --aig_mode                              false
% 2.72/1.01  
% 2.72/1.01  ------ Instantiation Options
% 2.72/1.01  
% 2.72/1.01  --instantiation_flag                    true
% 2.72/1.01  --inst_sos_flag                         true
% 2.72/1.01  --inst_sos_phase                        true
% 2.72/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/1.01  --inst_lit_sel_side                     none
% 2.72/1.01  --inst_solver_per_active                1400
% 2.72/1.01  --inst_solver_calls_frac                1.
% 2.72/1.01  --inst_passive_queue_type               priority_queues
% 2.72/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/1.01  --inst_passive_queues_freq              [25;2]
% 2.72/1.01  --inst_dismatching                      true
% 2.72/1.01  --inst_eager_unprocessed_to_passive     true
% 2.72/1.01  --inst_prop_sim_given                   true
% 2.72/1.01  --inst_prop_sim_new                     false
% 2.72/1.01  --inst_subs_new                         false
% 2.72/1.01  --inst_eq_res_simp                      false
% 2.72/1.01  --inst_subs_given                       false
% 2.72/1.01  --inst_orphan_elimination               true
% 2.72/1.01  --inst_learning_loop_flag               true
% 2.72/1.01  --inst_learning_start                   3000
% 2.72/1.01  --inst_learning_factor                  2
% 2.72/1.01  --inst_start_prop_sim_after_learn       3
% 2.72/1.01  --inst_sel_renew                        solver
% 2.72/1.01  --inst_lit_activity_flag                true
% 2.72/1.01  --inst_restr_to_given                   false
% 2.72/1.01  --inst_activity_threshold               500
% 2.72/1.01  --inst_out_proof                        true
% 2.72/1.01  
% 2.72/1.01  ------ Resolution Options
% 2.72/1.01  
% 2.72/1.01  --resolution_flag                       false
% 2.72/1.01  --res_lit_sel                           adaptive
% 2.72/1.01  --res_lit_sel_side                      none
% 2.72/1.01  --res_ordering                          kbo
% 2.72/1.01  --res_to_prop_solver                    active
% 2.72/1.01  --res_prop_simpl_new                    false
% 2.72/1.01  --res_prop_simpl_given                  true
% 2.72/1.01  --res_passive_queue_type                priority_queues
% 2.72/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/1.01  --res_passive_queues_freq               [15;5]
% 2.72/1.01  --res_forward_subs                      full
% 2.72/1.01  --res_backward_subs                     full
% 2.72/1.01  --res_forward_subs_resolution           true
% 2.72/1.01  --res_backward_subs_resolution          true
% 2.72/1.01  --res_orphan_elimination                true
% 2.72/1.01  --res_time_limit                        2.
% 2.72/1.01  --res_out_proof                         true
% 2.72/1.01  
% 2.72/1.01  ------ Superposition Options
% 2.72/1.01  
% 2.72/1.01  --superposition_flag                    true
% 2.72/1.01  --sup_passive_queue_type                priority_queues
% 2.72/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.72/1.01  --demod_completeness_check              fast
% 2.72/1.01  --demod_use_ground                      true
% 2.72/1.01  --sup_to_prop_solver                    passive
% 2.72/1.01  --sup_prop_simpl_new                    true
% 2.72/1.01  --sup_prop_simpl_given                  true
% 2.72/1.01  --sup_fun_splitting                     true
% 2.72/1.01  --sup_smt_interval                      50000
% 2.72/1.01  
% 2.72/1.01  ------ Superposition Simplification Setup
% 2.72/1.01  
% 2.72/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.72/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.72/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.72/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.72/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.72/1.01  --sup_immed_triv                        [TrivRules]
% 2.72/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/1.01  --sup_immed_bw_main                     []
% 2.72/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.72/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/1.01  --sup_input_bw                          []
% 2.72/1.01  
% 2.72/1.01  ------ Combination Options
% 2.72/1.01  
% 2.72/1.01  --comb_res_mult                         3
% 2.72/1.01  --comb_sup_mult                         2
% 2.72/1.01  --comb_inst_mult                        10
% 2.72/1.01  
% 2.72/1.01  ------ Debug Options
% 2.72/1.01  
% 2.72/1.01  --dbg_backtrace                         false
% 2.72/1.01  --dbg_dump_prop_clauses                 false
% 2.72/1.01  --dbg_dump_prop_clauses_file            -
% 2.72/1.01  --dbg_out_stat                          false
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  ------ Proving...
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  % SZS status Theorem for theBenchmark.p
% 2.72/1.01  
% 2.72/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.72/1.01  
% 2.72/1.01  fof(f17,conjecture,(
% 2.72/1.01    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f18,negated_conjecture,(
% 2.72/1.01    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.72/1.01    inference(negated_conjecture,[],[f17])).
% 2.72/1.01  
% 2.72/1.01  fof(f27,plain,(
% 2.72/1.01    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.72/1.01    inference(ennf_transformation,[],[f18])).
% 2.72/1.01  
% 2.72/1.01  fof(f50,plain,(
% 2.72/1.01    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.72/1.01    inference(nnf_transformation,[],[f27])).
% 2.72/1.01  
% 2.72/1.01  fof(f51,plain,(
% 2.72/1.01    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.72/1.01    inference(flattening,[],[f50])).
% 2.72/1.01  
% 2.72/1.01  fof(f53,plain,(
% 2.72/1.01    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK6) | ~r2_hidden(X0,k1_ordinal1(sK6))) & (r1_ordinal1(X0,sK6) | r2_hidden(X0,k1_ordinal1(sK6))) & v3_ordinal1(sK6))) )),
% 2.72/1.01    introduced(choice_axiom,[])).
% 2.72/1.01  
% 2.72/1.01  fof(f52,plain,(
% 2.72/1.01    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK5,X1) | ~r2_hidden(sK5,k1_ordinal1(X1))) & (r1_ordinal1(sK5,X1) | r2_hidden(sK5,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK5))),
% 2.72/1.01    introduced(choice_axiom,[])).
% 2.72/1.01  
% 2.72/1.01  fof(f54,plain,(
% 2.72/1.01    ((~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))) & (r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))) & v3_ordinal1(sK6)) & v3_ordinal1(sK5)),
% 2.72/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f51,f53,f52])).
% 2.72/1.01  
% 2.72/1.01  fof(f99,plain,(
% 2.72/1.01    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))),
% 2.72/1.01    inference(cnf_transformation,[],[f54])).
% 2.72/1.01  
% 2.72/1.01  fof(f13,axiom,(
% 2.72/1.01    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f91,plain,(
% 2.72/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f13])).
% 2.72/1.01  
% 2.72/1.01  fof(f10,axiom,(
% 2.72/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f74,plain,(
% 2.72/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.72/1.01    inference(cnf_transformation,[],[f10])).
% 2.72/1.01  
% 2.72/1.01  fof(f105,plain,(
% 2.72/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.72/1.01    inference(definition_unfolding,[],[f74,f104])).
% 2.72/1.01  
% 2.72/1.01  fof(f3,axiom,(
% 2.72/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f67,plain,(
% 2.72/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f3])).
% 2.72/1.01  
% 2.72/1.01  fof(f4,axiom,(
% 2.72/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f68,plain,(
% 2.72/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f4])).
% 2.72/1.01  
% 2.72/1.01  fof(f5,axiom,(
% 2.72/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f69,plain,(
% 2.72/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f5])).
% 2.72/1.01  
% 2.72/1.01  fof(f6,axiom,(
% 2.72/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f70,plain,(
% 2.72/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f6])).
% 2.72/1.01  
% 2.72/1.01  fof(f7,axiom,(
% 2.72/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f71,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f7])).
% 2.72/1.01  
% 2.72/1.01  fof(f8,axiom,(
% 2.72/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f72,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f8])).
% 2.72/1.01  
% 2.72/1.01  fof(f9,axiom,(
% 2.72/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f73,plain,(
% 2.72/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f9])).
% 2.72/1.01  
% 2.72/1.01  fof(f100,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f72,f73])).
% 2.72/1.01  
% 2.72/1.01  fof(f101,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f71,f100])).
% 2.72/1.01  
% 2.72/1.01  fof(f102,plain,(
% 2.72/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f70,f101])).
% 2.72/1.01  
% 2.72/1.01  fof(f103,plain,(
% 2.72/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f69,f102])).
% 2.72/1.01  
% 2.72/1.01  fof(f104,plain,(
% 2.72/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f68,f103])).
% 2.72/1.01  
% 2.72/1.01  fof(f106,plain,(
% 2.72/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f67,f104])).
% 2.72/1.01  
% 2.72/1.01  fof(f107,plain,(
% 2.72/1.01    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f91,f105,f106])).
% 2.72/1.01  
% 2.72/1.01  fof(f120,plain,(
% 2.72/1.01    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 2.72/1.01    inference(definition_unfolding,[],[f99,f107])).
% 2.72/1.01  
% 2.72/1.01  fof(f96,plain,(
% 2.72/1.01    v3_ordinal1(sK5)),
% 2.72/1.01    inference(cnf_transformation,[],[f54])).
% 2.72/1.01  
% 2.72/1.01  fof(f97,plain,(
% 2.72/1.01    v3_ordinal1(sK6)),
% 2.72/1.01    inference(cnf_transformation,[],[f54])).
% 2.72/1.01  
% 2.72/1.01  fof(f16,axiom,(
% 2.72/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f26,plain,(
% 2.72/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.72/1.01    inference(ennf_transformation,[],[f16])).
% 2.72/1.01  
% 2.72/1.01  fof(f95,plain,(
% 2.72/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f26])).
% 2.72/1.01  
% 2.72/1.01  fof(f15,axiom,(
% 2.72/1.01    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f24,plain,(
% 2.72/1.01    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.72/1.01    inference(ennf_transformation,[],[f15])).
% 2.72/1.01  
% 2.72/1.01  fof(f25,plain,(
% 2.72/1.01    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.72/1.01    inference(flattening,[],[f24])).
% 2.72/1.01  
% 2.72/1.01  fof(f94,plain,(
% 2.72/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f25])).
% 2.72/1.01  
% 2.72/1.01  fof(f14,axiom,(
% 2.72/1.01    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f22,plain,(
% 2.72/1.01    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.72/1.01    inference(ennf_transformation,[],[f14])).
% 2.72/1.01  
% 2.72/1.01  fof(f23,plain,(
% 2.72/1.01    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.72/1.01    inference(flattening,[],[f22])).
% 2.72/1.01  
% 2.72/1.01  fof(f49,plain,(
% 2.72/1.01    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.72/1.01    inference(nnf_transformation,[],[f23])).
% 2.72/1.01  
% 2.72/1.01  fof(f92,plain,(
% 2.72/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f49])).
% 2.72/1.01  
% 2.72/1.01  fof(f12,axiom,(
% 2.72/1.01    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f20,plain,(
% 2.72/1.01    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.72/1.01    inference(ennf_transformation,[],[f12])).
% 2.72/1.01  
% 2.72/1.01  fof(f21,plain,(
% 2.72/1.01    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.72/1.01    inference(flattening,[],[f20])).
% 2.72/1.01  
% 2.72/1.01  fof(f90,plain,(
% 2.72/1.01    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f21])).
% 2.72/1.01  
% 2.72/1.01  fof(f2,axiom,(
% 2.72/1.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f36,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.72/1.01    inference(nnf_transformation,[],[f2])).
% 2.72/1.01  
% 2.72/1.01  fof(f37,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.72/1.01    inference(flattening,[],[f36])).
% 2.72/1.01  
% 2.72/1.01  fof(f38,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.72/1.01    inference(rectify,[],[f37])).
% 2.72/1.01  
% 2.72/1.01  fof(f39,plain,(
% 2.72/1.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.72/1.01    introduced(choice_axiom,[])).
% 2.72/1.01  
% 2.72/1.01  fof(f40,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.72/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 2.72/1.01  
% 2.72/1.01  fof(f62,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.72/1.01    inference(cnf_transformation,[],[f40])).
% 2.72/1.01  
% 2.72/1.01  fof(f118,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 2.72/1.01    inference(definition_unfolding,[],[f62,f104])).
% 2.72/1.01  
% 2.72/1.01  fof(f127,plain,(
% 2.72/1.01    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 2.72/1.01    inference(equality_resolution,[],[f118])).
% 2.72/1.01  
% 2.72/1.01  fof(f128,plain,(
% 2.72/1.01    ( ! [X4,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1))) )),
% 2.72/1.01    inference(equality_resolution,[],[f127])).
% 2.72/1.01  
% 2.72/1.01  fof(f1,axiom,(
% 2.72/1.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f31,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.72/1.01    inference(nnf_transformation,[],[f1])).
% 2.72/1.01  
% 2.72/1.01  fof(f32,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.72/1.01    inference(flattening,[],[f31])).
% 2.72/1.01  
% 2.72/1.01  fof(f33,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.72/1.01    inference(rectify,[],[f32])).
% 2.72/1.01  
% 2.72/1.01  fof(f34,plain,(
% 2.72/1.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.72/1.01    introduced(choice_axiom,[])).
% 2.72/1.01  
% 2.72/1.01  fof(f35,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.72/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 2.72/1.01  
% 2.72/1.01  fof(f57,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.72/1.01    inference(cnf_transformation,[],[f35])).
% 2.72/1.01  
% 2.72/1.01  fof(f111,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.72/1.01    inference(definition_unfolding,[],[f57,f105])).
% 2.72/1.01  
% 2.72/1.01  fof(f122,plain,(
% 2.72/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.72/1.01    inference(equality_resolution,[],[f111])).
% 2.72/1.01  
% 2.72/1.01  fof(f56,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.72/1.01    inference(cnf_transformation,[],[f35])).
% 2.72/1.01  
% 2.72/1.01  fof(f112,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.72/1.01    inference(definition_unfolding,[],[f56,f105])).
% 2.72/1.01  
% 2.72/1.01  fof(f123,plain,(
% 2.72/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.72/1.01    inference(equality_resolution,[],[f112])).
% 2.72/1.01  
% 2.72/1.01  fof(f61,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.72/1.01    inference(cnf_transformation,[],[f40])).
% 2.72/1.01  
% 2.72/1.01  fof(f119,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 2.72/1.01    inference(definition_unfolding,[],[f61,f104])).
% 2.72/1.01  
% 2.72/1.01  fof(f129,plain,(
% 2.72/1.01    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.72/1.01    inference(equality_resolution,[],[f119])).
% 2.72/1.01  
% 2.72/1.01  fof(f55,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.72/1.01    inference(cnf_transformation,[],[f35])).
% 2.72/1.01  
% 2.72/1.01  fof(f113,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.72/1.01    inference(definition_unfolding,[],[f55,f105])).
% 2.72/1.01  
% 2.72/1.01  fof(f124,plain,(
% 2.72/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.72/1.01    inference(equality_resolution,[],[f113])).
% 2.72/1.01  
% 2.72/1.01  fof(f98,plain,(
% 2.72/1.01    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))),
% 2.72/1.01    inference(cnf_transformation,[],[f54])).
% 2.72/1.01  
% 2.72/1.01  fof(f121,plain,(
% 2.72/1.01    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 2.72/1.01    inference(definition_unfolding,[],[f98,f107])).
% 2.72/1.01  
% 2.72/1.01  cnf(c_1840,plain,
% 2.72/1.01      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.72/1.01      theory(equality) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_3156,plain,
% 2.72/1.01      ( ~ r1_ordinal1(X0,X1)
% 2.72/1.01      | r1_ordinal1(sK5,sK6)
% 2.72/1.01      | sK6 != X1
% 2.72/1.01      | sK5 != X0 ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_1840]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_3158,plain,
% 2.72/1.01      ( ~ r1_ordinal1(sK6,sK6)
% 2.72/1.01      | r1_ordinal1(sK5,sK6)
% 2.72/1.01      | sK6 != sK6
% 2.72/1.01      | sK5 != sK6 ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_3156]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_32,negated_conjecture,
% 2.72/1.01      ( ~ r1_ordinal1(sK5,sK6)
% 2.72/1.01      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.72/1.01      inference(cnf_transformation,[],[f120]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2562,plain,
% 2.72/1.01      ( r1_ordinal1(sK5,sK6) != iProver_top
% 2.72/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_35,negated_conjecture,
% 2.72/1.01      ( v3_ordinal1(sK5) ),
% 2.72/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_36,plain,
% 2.72/1.01      ( v3_ordinal1(sK5) = iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_34,negated_conjecture,
% 2.72/1.01      ( v3_ordinal1(sK6) ),
% 2.72/1.01      inference(cnf_transformation,[],[f97]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_37,plain,
% 2.72/1.01      ( v3_ordinal1(sK6) = iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_39,plain,
% 2.72/1.01      ( r1_ordinal1(sK5,sK6) != iProver_top
% 2.72/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_31,plain,
% 2.72/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.72/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_41,plain,
% 2.72/1.01      ( ~ r1_tarski(sK6,sK6) | ~ r2_hidden(sK6,sK6) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_31]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_30,plain,
% 2.72/1.01      ( r2_hidden(X0,X1)
% 2.72/1.01      | r2_hidden(X1,X0)
% 2.72/1.01      | ~ v3_ordinal1(X1)
% 2.72/1.01      | ~ v3_ordinal1(X0)
% 2.72/1.01      | X1 = X0 ),
% 2.72/1.01      inference(cnf_transformation,[],[f94]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_44,plain,
% 2.72/1.01      ( r2_hidden(sK6,sK6) | ~ v3_ordinal1(sK6) | sK6 = sK6 ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_29,plain,
% 2.72/1.01      ( r1_tarski(X0,X1)
% 2.72/1.01      | ~ r1_ordinal1(X0,X1)
% 2.72/1.01      | ~ v3_ordinal1(X1)
% 2.72/1.01      | ~ v3_ordinal1(X0) ),
% 2.72/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_47,plain,
% 2.72/1.01      ( r1_tarski(sK6,sK6)
% 2.72/1.01      | ~ r1_ordinal1(sK6,sK6)
% 2.72/1.01      | ~ v3_ordinal1(sK6) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_27,plain,
% 2.72/1.01      ( r1_ordinal1(X0,X1)
% 2.72/1.01      | r1_ordinal1(X1,X0)
% 2.72/1.01      | ~ v3_ordinal1(X1)
% 2.72/1.01      | ~ v3_ordinal1(X0) ),
% 2.72/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_53,plain,
% 2.72/1.01      ( r1_ordinal1(sK6,sK6) | ~ v3_ordinal1(sK6) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_27]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_10,plain,
% 2.72/1.01      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 2.72/1.01      inference(cnf_transformation,[],[f128]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_87,plain,
% 2.72/1.01      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_89,plain,
% 2.72/1.01      ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_87]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_1835,plain,
% 2.72/1.01      ( X0 != X1
% 2.72/1.01      | X2 != X3
% 2.72/1.01      | X4 != X5
% 2.72/1.01      | X6 != X7
% 2.72/1.01      | X8 != X9
% 2.72/1.01      | X10 != X11
% 2.72/1.01      | X12 != X13
% 2.72/1.01      | X14 != X15
% 2.72/1.01      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 2.72/1.01      theory(equality) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_1842,plain,
% 2.72/1.01      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.72/1.01      | sK6 != sK6 ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_1835]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_3,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,X1)
% 2.72/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.72/1.01      inference(cnf_transformation,[],[f122]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2635,plain,
% 2.72/1.01      ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.72/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2636,plain,
% 2.72/1.01      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.72/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2635]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_4,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,X1)
% 2.72/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 2.72/1.01      inference(cnf_transformation,[],[f123]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2638,plain,
% 2.72/1.01      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.72/1.01      | ~ r2_hidden(sK5,sK6) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2639,plain,
% 2.72/1.01      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top
% 2.72/1.01      | r2_hidden(sK5,sK6) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2638]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_455,plain,
% 2.72/1.01      ( ~ r1_ordinal1(X0,X1)
% 2.72/1.01      | ~ r2_hidden(X1,X0)
% 2.72/1.01      | ~ v3_ordinal1(X1)
% 2.72/1.01      | ~ v3_ordinal1(X0) ),
% 2.72/1.01      inference(resolution,[status(thm)],[c_29,c_31]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2651,plain,
% 2.72/1.01      ( ~ r1_ordinal1(sK5,sK6)
% 2.72/1.01      | ~ r2_hidden(sK6,sK5)
% 2.72/1.01      | ~ v3_ordinal1(sK6)
% 2.72/1.01      | ~ v3_ordinal1(sK5) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_455]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2652,plain,
% 2.72/1.01      ( r1_ordinal1(sK5,sK6) != iProver_top
% 2.72/1.01      | r2_hidden(sK6,sK5) != iProver_top
% 2.72/1.01      | v3_ordinal1(sK6) != iProver_top
% 2.72/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2651]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2804,plain,
% 2.72/1.01      ( r2_hidden(X0,sK5)
% 2.72/1.01      | r2_hidden(sK5,X0)
% 2.72/1.01      | ~ v3_ordinal1(X0)
% 2.72/1.01      | ~ v3_ordinal1(sK5)
% 2.72/1.01      | sK5 = X0 ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2805,plain,
% 2.72/1.01      ( sK5 = X0
% 2.72/1.01      | r2_hidden(X0,sK5) = iProver_top
% 2.72/1.01      | r2_hidden(sK5,X0) = iProver_top
% 2.72/1.01      | v3_ordinal1(X0) != iProver_top
% 2.72/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2804]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2807,plain,
% 2.72/1.01      ( sK5 = sK6
% 2.72/1.01      | r2_hidden(sK6,sK5) = iProver_top
% 2.72/1.01      | r2_hidden(sK5,sK6) = iProver_top
% 2.72/1.01      | v3_ordinal1(sK6) != iProver_top
% 2.72/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2805]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_1837,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.72/1.01      theory(equality) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2684,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,X1)
% 2.72/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.72/1.01      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != X1
% 2.72/1.01      | sK5 != X0 ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_1837]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2956,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
% 2.72/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.72/1.01      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)
% 2.72/1.01      | sK5 != X0 ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2684]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2957,plain,
% 2.72/1.01      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
% 2.72/1.01      | sK5 != X1
% 2.72/1.01      | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top
% 2.72/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2956]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2959,plain,
% 2.72/1.01      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.72/1.01      | sK5 != sK6
% 2.72/1.01      | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.72/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2957]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2993,plain,
% 2.72/1.01      ( r1_ordinal1(sK5,sK6) != iProver_top ),
% 2.72/1.01      inference(global_propositional_subsumption,
% 2.72/1.01                [status(thm)],
% 2.72/1.01                [c_2562,c_36,c_34,c_37,c_39,c_41,c_44,c_47,c_53,c_89,
% 2.72/1.01                 c_1842,c_2636,c_2639,c_2652,c_2807,c_2959]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2958,plain,
% 2.72/1.01      ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.72/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.72/1.01      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.72/1.01      | sK5 != sK6 ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2956]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_11,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 2.72/1.01      | X0 = X1
% 2.72/1.01      | X0 = X2 ),
% 2.72/1.01      inference(cnf_transformation,[],[f129]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2795,plain,
% 2.72/1.01      ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
% 2.72/1.01      | sK5 = X0
% 2.72/1.01      | sK5 = X1 ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2796,plain,
% 2.72/1.01      ( sK5 = X0
% 2.72/1.01      | sK5 = X1
% 2.72/1.01      | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2795]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2798,plain,
% 2.72/1.01      ( sK5 = sK6
% 2.72/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2796]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2769,plain,
% 2.72/1.01      ( r1_ordinal1(X0,sK5)
% 2.72/1.01      | r1_ordinal1(sK5,X0)
% 2.72/1.01      | ~ v3_ordinal1(X0)
% 2.72/1.01      | ~ v3_ordinal1(sK5) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_27]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2770,plain,
% 2.72/1.01      ( r1_ordinal1(X0,sK5) = iProver_top
% 2.72/1.01      | r1_ordinal1(sK5,X0) = iProver_top
% 2.72/1.01      | v3_ordinal1(X0) != iProver_top
% 2.72/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2769]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2772,plain,
% 2.72/1.01      ( r1_ordinal1(sK6,sK5) = iProver_top
% 2.72/1.01      | r1_ordinal1(sK5,sK6) = iProver_top
% 2.72/1.01      | v3_ordinal1(sK6) != iProver_top
% 2.72/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2770]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_5,plain,
% 2.72/1.01      ( r2_hidden(X0,X1)
% 2.72/1.01      | r2_hidden(X0,X2)
% 2.72/1.01      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.72/1.01      inference(cnf_transformation,[],[f124]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2674,plain,
% 2.72/1.01      ( r2_hidden(sK5,X0)
% 2.72/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.72/1.01      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2675,plain,
% 2.72/1.01      ( r2_hidden(sK5,X0) = iProver_top
% 2.72/1.01      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 2.72/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2674]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2677,plain,
% 2.72/1.01      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 2.72/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top
% 2.72/1.01      | r2_hidden(sK5,sK6) = iProver_top ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2675]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2666,plain,
% 2.72/1.01      ( ~ r1_ordinal1(X0,sK5)
% 2.72/1.01      | ~ r2_hidden(sK5,X0)
% 2.72/1.01      | ~ v3_ordinal1(X0)
% 2.72/1.01      | ~ v3_ordinal1(sK5) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_455]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2667,plain,
% 2.72/1.01      ( r1_ordinal1(X0,sK5) != iProver_top
% 2.72/1.01      | r2_hidden(sK5,X0) != iProver_top
% 2.72/1.01      | v3_ordinal1(X0) != iProver_top
% 2.72/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2666]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2669,plain,
% 2.72/1.01      ( r1_ordinal1(sK6,sK5) != iProver_top
% 2.72/1.01      | r2_hidden(sK5,sK6) != iProver_top
% 2.72/1.01      | v3_ordinal1(sK6) != iProver_top
% 2.72/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2667]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_88,plain,
% 2.72/1.01      ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_33,negated_conjecture,
% 2.72/1.01      ( r1_ordinal1(sK5,sK6)
% 2.72/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.72/1.01      inference(cnf_transformation,[],[f121]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_38,plain,
% 2.72/1.01      ( r1_ordinal1(sK5,sK6) = iProver_top
% 2.72/1.01      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(contradiction,plain,
% 2.72/1.01      ( $false ),
% 2.72/1.01      inference(minisat,
% 2.72/1.01                [status(thm)],
% 2.72/1.01                [c_3158,c_2993,c_2958,c_2798,c_2772,c_2677,c_2669,c_2635,
% 2.72/1.01                 c_1842,c_88,c_53,c_47,c_44,c_41,c_32,c_38,c_37,c_34,
% 2.72/1.01                 c_36]) ).
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.72/1.01  
% 2.72/1.01  ------                               Statistics
% 2.72/1.01  
% 2.72/1.01  ------ General
% 2.72/1.01  
% 2.72/1.01  abstr_ref_over_cycles:                  0
% 2.72/1.01  abstr_ref_under_cycles:                 0
% 2.72/1.01  gc_basic_clause_elim:                   0
% 2.72/1.01  forced_gc_time:                         0
% 2.72/1.01  parsing_time:                           0.013
% 2.72/1.01  unif_index_cands_time:                  0.
% 2.72/1.01  unif_index_add_time:                    0.
% 2.72/1.01  orderings_time:                         0.
% 2.72/1.01  out_proof_time:                         0.012
% 2.72/1.01  total_time:                             0.128
% 2.72/1.01  num_of_symbols:                         41
% 2.72/1.01  num_of_terms:                           1872
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing
% 2.72/1.01  
% 2.72/1.01  num_of_splits:                          0
% 2.72/1.01  num_of_split_atoms:                     0
% 2.72/1.01  num_of_reused_defs:                     0
% 2.72/1.01  num_eq_ax_congr_red:                    95
% 2.72/1.01  num_of_sem_filtered_clauses:            1
% 2.72/1.01  num_of_subtypes:                        0
% 2.72/1.01  monotx_restored_types:                  0
% 2.72/1.01  sat_num_of_epr_types:                   0
% 2.72/1.01  sat_num_of_non_cyclic_types:            0
% 2.72/1.01  sat_guarded_non_collapsed_types:        0
% 2.72/1.01  num_pure_diseq_elim:                    0
% 2.72/1.01  simp_replaced_by:                       0
% 2.72/1.01  res_preprocessed:                       157
% 2.72/1.01  prep_upred:                             0
% 2.72/1.01  prep_unflattend:                        596
% 2.72/1.01  smt_new_axioms:                         0
% 2.72/1.01  pred_elim_cands:                        5
% 2.72/1.01  pred_elim:                              1
% 2.72/1.01  pred_elim_cl:                           2
% 2.72/1.01  pred_elim_cycles:                       5
% 2.72/1.01  merged_defs:                            8
% 2.72/1.01  merged_defs_ncl:                        0
% 2.72/1.01  bin_hyper_res:                          8
% 2.72/1.01  prep_cycles:                            4
% 2.72/1.01  pred_elim_time:                         0.026
% 2.72/1.01  splitting_time:                         0.
% 2.72/1.01  sem_filter_time:                        0.
% 2.72/1.01  monotx_time:                            0.001
% 2.72/1.01  subtype_inf_time:                       0.
% 2.72/1.01  
% 2.72/1.01  ------ Problem properties
% 2.72/1.01  
% 2.72/1.01  clauses:                                34
% 2.72/1.01  conjectures:                            4
% 2.72/1.01  epr:                                    16
% 2.72/1.01  horn:                                   25
% 2.72/1.01  ground:                                 4
% 2.72/1.01  unary:                                  13
% 2.72/1.01  binary:                                 5
% 2.72/1.01  lits:                                   83
% 2.72/1.01  lits_eq:                                22
% 2.72/1.01  fd_pure:                                0
% 2.72/1.01  fd_pseudo:                              0
% 2.72/1.01  fd_cond:                                0
% 2.72/1.01  fd_pseudo_cond:                         9
% 2.72/1.01  ac_symbols:                             0
% 2.72/1.01  
% 2.72/1.01  ------ Propositional Solver
% 2.72/1.01  
% 2.72/1.01  prop_solver_calls:                      26
% 2.72/1.01  prop_fast_solver_calls:                 1014
% 2.72/1.01  smt_solver_calls:                       0
% 2.72/1.01  smt_fast_solver_calls:                  0
% 2.72/1.01  prop_num_of_clauses:                    510
% 2.72/1.01  prop_preprocess_simplified:             5224
% 2.72/1.01  prop_fo_subsumed:                       2
% 2.72/1.01  prop_solver_time:                       0.
% 2.72/1.01  smt_solver_time:                        0.
% 2.72/1.01  smt_fast_solver_time:                   0.
% 2.72/1.01  prop_fast_solver_time:                  0.
% 2.72/1.01  prop_unsat_core_time:                   0.
% 2.72/1.01  
% 2.72/1.01  ------ QBF
% 2.72/1.01  
% 2.72/1.01  qbf_q_res:                              0
% 2.72/1.01  qbf_num_tautologies:                    0
% 2.72/1.01  qbf_prep_cycles:                        0
% 2.72/1.01  
% 2.72/1.01  ------ BMC1
% 2.72/1.01  
% 2.72/1.01  bmc1_current_bound:                     -1
% 2.72/1.01  bmc1_last_solved_bound:                 -1
% 2.72/1.01  bmc1_unsat_core_size:                   -1
% 2.72/1.01  bmc1_unsat_core_parents_size:           -1
% 2.72/1.01  bmc1_merge_next_fun:                    0
% 2.72/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.72/1.01  
% 2.72/1.01  ------ Instantiation
% 2.72/1.01  
% 2.72/1.01  inst_num_of_clauses:                    102
% 2.72/1.01  inst_num_in_passive:                    75
% 2.72/1.01  inst_num_in_active:                     25
% 2.72/1.01  inst_num_in_unprocessed:                1
% 2.72/1.01  inst_num_of_loops:                      30
% 2.72/1.01  inst_num_of_learning_restarts:          0
% 2.72/1.01  inst_num_moves_active_passive:          4
% 2.72/1.01  inst_lit_activity:                      0
% 2.72/1.01  inst_lit_activity_moves:                0
% 2.72/1.01  inst_num_tautologies:                   0
% 2.72/1.01  inst_num_prop_implied:                  0
% 2.72/1.01  inst_num_existing_simplified:           0
% 2.72/1.01  inst_num_eq_res_simplified:             0
% 2.72/1.01  inst_num_child_elim:                    0
% 2.72/1.01  inst_num_of_dismatching_blockings:      11
% 2.72/1.01  inst_num_of_non_proper_insts:           63
% 2.72/1.01  inst_num_of_duplicates:                 0
% 2.72/1.01  inst_inst_num_from_inst_to_res:         0
% 2.72/1.01  inst_dismatching_checking_time:         0.
% 2.72/1.01  
% 2.72/1.01  ------ Resolution
% 2.72/1.01  
% 2.72/1.01  res_num_of_clauses:                     0
% 2.72/1.01  res_num_in_passive:                     0
% 2.72/1.01  res_num_in_active:                      0
% 2.72/1.01  res_num_of_loops:                       161
% 2.72/1.01  res_forward_subset_subsumed:            2
% 2.72/1.01  res_backward_subset_subsumed:           0
% 2.72/1.01  res_forward_subsumed:                   0
% 2.72/1.01  res_backward_subsumed:                  0
% 2.72/1.01  res_forward_subsumption_resolution:     0
% 2.72/1.01  res_backward_subsumption_resolution:    0
% 2.72/1.01  res_clause_to_clause_subsumption:       574
% 2.72/1.01  res_orphan_elimination:                 0
% 2.72/1.01  res_tautology_del:                      37
% 2.72/1.01  res_num_eq_res_simplified:              0
% 2.72/1.01  res_num_sel_changes:                    0
% 2.72/1.01  res_moves_from_active_to_pass:          0
% 2.72/1.01  
% 2.72/1.01  ------ Superposition
% 2.72/1.01  
% 2.72/1.01  sup_time_total:                         0.
% 2.72/1.01  sup_time_generating:                    0.
% 2.72/1.01  sup_time_sim_full:                      0.
% 2.72/1.01  sup_time_sim_immed:                     0.
% 2.72/1.01  
% 2.72/1.01  sup_num_of_clauses:                     34
% 2.72/1.01  sup_num_in_active:                      4
% 2.72/1.01  sup_num_in_passive:                     30
% 2.72/1.01  sup_num_of_loops:                       4
% 2.72/1.01  sup_fw_superposition:                   0
% 2.72/1.01  sup_bw_superposition:                   0
% 2.72/1.01  sup_immediate_simplified:               0
% 2.72/1.01  sup_given_eliminated:                   0
% 2.72/1.01  comparisons_done:                       0
% 2.72/1.01  comparisons_avoided:                    0
% 2.72/1.01  
% 2.72/1.01  ------ Simplifications
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  sim_fw_subset_subsumed:                 0
% 2.72/1.01  sim_bw_subset_subsumed:                 0
% 2.72/1.01  sim_fw_subsumed:                        0
% 2.72/1.01  sim_bw_subsumed:                        0
% 2.72/1.01  sim_fw_subsumption_res:                 0
% 2.72/1.01  sim_bw_subsumption_res:                 0
% 2.72/1.01  sim_tautology_del:                      0
% 2.72/1.01  sim_eq_tautology_del:                   0
% 2.72/1.01  sim_eq_res_simp:                        0
% 2.72/1.01  sim_fw_demodulated:                     0
% 2.72/1.01  sim_bw_demodulated:                     0
% 2.72/1.01  sim_light_normalised:                   0
% 2.72/1.01  sim_joinable_taut:                      0
% 2.72/1.01  sim_joinable_simp:                      0
% 2.72/1.01  sim_ac_normalised:                      0
% 2.72/1.01  sim_smt_subsumption:                    0
% 2.72/1.01  
%------------------------------------------------------------------------------
