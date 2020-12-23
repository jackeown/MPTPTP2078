%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:50 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 468 expanded)
%              Number of clauses        :   65 ( 114 expanded)
%              Number of leaves         :   18 ( 114 expanded)
%              Depth                    :   16
%              Number of atoms          :  499 (2232 expanded)
%              Number of equality atoms :  176 ( 446 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK3)
          | ~ r2_hidden(X0,k1_ordinal1(sK3)) )
        & ( r1_ordinal1(X0,sK3)
          | r2_hidden(X0,k1_ordinal1(sK3)) )
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK2,X1)
            | ~ r2_hidden(sK2,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK2,X1)
            | r2_hidden(sK2,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ r1_ordinal1(sK2,sK3)
      | ~ r2_hidden(sK2,k1_ordinal1(sK3)) )
    & ( r1_ordinal1(sK2,sK3)
      | r2_hidden(sK2,k1_ordinal1(sK3)) )
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).

fof(f62,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f64,plain,(
    ! [X0] : k2_xboole_0(X0,k1_enumset1(X0,X0,X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f53,f63])).

fof(f71,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f62,f64])).

fof(f59,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f78,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f69])).

fof(f79,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f78])).

cnf(c_507,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3112,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_3113,plain,
    ( sK3 != sK3
    | sK3 = sK2
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_3112])).

cnf(c_508,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3046,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,sK2)
    | X0 != sK3
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_3049,plain,
    ( r2_hidden(sK3,sK3)
    | ~ r2_hidden(sK3,sK2)
    | sK3 != sK3
    | sK3 != sK2 ),
    inference(instantiation,[status(thm)],[c_3046])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_911,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,negated_conjecture,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_166,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_309,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_166])).

cnf(c_310,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_21,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_312,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_310,c_21,c_20])).

cnf(c_402,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(prop_impl,[status(thm)],[c_21,c_20,c_310])).

cnf(c_900,plain,
    ( r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_1676,plain,
    ( r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_900])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_958,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_959,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_2490,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1676,c_959])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_286,plain,
    ( ~ r1_ordinal1(X0,X1)
    | ~ r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_14,c_17])).

cnf(c_19,negated_conjecture,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_168,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_323,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_286,c_168])).

cnf(c_324,plain,
    ( ~ r2_hidden(sK3,sK2)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_326,plain,
    ( ~ r2_hidden(sK3,sK2)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_21,c_20])).

cnf(c_404,plain,
    ( ~ r2_hidden(sK3,sK2)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(prop_impl,[status(thm)],[c_21,c_20,c_324])).

cnf(c_899,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_910,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2065,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_899,c_910])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2051,plain,
    ( r2_hidden(X0,sK2)
    | r2_hidden(sK2,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2052,plain,
    ( sK2 = X0
    | r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(sK2,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2051])).

cnf(c_2054,plain,
    ( sK2 = sK3
    | r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2052])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2046,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(X0,X0,X1))
    | sK2 = X0
    | sK2 = X1 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2047,plain,
    ( sK2 = X0
    | sK2 = X1
    | r2_hidden(sK2,k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2046])).

cnf(c_2049,plain,
    ( sK2 = sK3
    | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_912,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1675,plain,
    ( r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_900])).

cnf(c_1678,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1675])).

cnf(c_979,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_enumset1(X3,X3,X2))
    | X0 != X2
    | X1 != k1_enumset1(X3,X3,X2) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_1035,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X0))
    | r2_hidden(X2,k1_enumset1(X3,X3,X4))
    | X2 != X0
    | k1_enumset1(X3,X3,X4) != k1_enumset1(X1,X1,X0) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_1557,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X0))
    | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
    | k1_enumset1(sK3,sK3,sK3) != k1_enumset1(X1,X1,X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_1558,plain,
    ( k1_enumset1(sK3,sK3,sK3) != k1_enumset1(X0,X0,X1)
    | sK2 != X1
    | r2_hidden(X1,k1_enumset1(X0,X0,X1)) != iProver_top
    | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(c_1560,plain,
    ( k1_enumset1(sK3,sK3,sK3) != k1_enumset1(sK3,sK3,sK3)
    | sK2 != sK3
    | r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1558])).

cnf(c_1559,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
    | k1_enumset1(sK3,sK3,sK3) != k1_enumset1(sK3,sK3,sK3)
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_510,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
    theory(equality)).

cnf(c_514,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k1_enumset1(sK3,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_70,plain,
    ( ~ r2_hidden(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_44,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_46,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_45,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_42,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_23,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3113,c_3049,c_2490,c_2065,c_2054,c_2049,c_1678,c_1675,c_1560,c_1559,c_514,c_70,c_46,c_45,c_42,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.32/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/0.92  
% 3.32/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.92  
% 3.32/0.92  ------  iProver source info
% 3.32/0.92  
% 3.32/0.92  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.92  git: non_committed_changes: false
% 3.32/0.92  git: last_make_outside_of_git: false
% 3.32/0.92  
% 3.32/0.92  ------ 
% 3.32/0.92  
% 3.32/0.92  ------ Input Options
% 3.32/0.92  
% 3.32/0.92  --out_options                           all
% 3.32/0.92  --tptp_safe_out                         true
% 3.32/0.92  --problem_path                          ""
% 3.32/0.92  --include_path                          ""
% 3.32/0.92  --clausifier                            res/vclausify_rel
% 3.32/0.92  --clausifier_options                    ""
% 3.32/0.92  --stdin                                 false
% 3.32/0.92  --stats_out                             all
% 3.32/0.92  
% 3.32/0.92  ------ General Options
% 3.32/0.92  
% 3.32/0.92  --fof                                   false
% 3.32/0.92  --time_out_real                         305.
% 3.32/0.92  --time_out_virtual                      -1.
% 3.32/0.92  --symbol_type_check                     false
% 3.32/0.92  --clausify_out                          false
% 3.32/0.92  --sig_cnt_out                           false
% 3.32/0.92  --trig_cnt_out                          false
% 3.32/0.92  --trig_cnt_out_tolerance                1.
% 3.32/0.92  --trig_cnt_out_sk_spl                   false
% 3.32/0.92  --abstr_cl_out                          false
% 3.32/0.92  
% 3.32/0.92  ------ Global Options
% 3.32/0.92  
% 3.32/0.92  --schedule                              default
% 3.32/0.92  --add_important_lit                     false
% 3.32/0.92  --prop_solver_per_cl                    1000
% 3.32/0.92  --min_unsat_core                        false
% 3.32/0.92  --soft_assumptions                      false
% 3.32/0.92  --soft_lemma_size                       3
% 3.32/0.92  --prop_impl_unit_size                   0
% 3.32/0.92  --prop_impl_unit                        []
% 3.32/0.92  --share_sel_clauses                     true
% 3.32/0.92  --reset_solvers                         false
% 3.32/0.92  --bc_imp_inh                            [conj_cone]
% 3.32/0.92  --conj_cone_tolerance                   3.
% 3.32/0.92  --extra_neg_conj                        none
% 3.32/0.92  --large_theory_mode                     true
% 3.32/0.92  --prolific_symb_bound                   200
% 3.32/0.92  --lt_threshold                          2000
% 3.32/0.92  --clause_weak_htbl                      true
% 3.32/0.92  --gc_record_bc_elim                     false
% 3.32/0.92  
% 3.32/0.92  ------ Preprocessing Options
% 3.32/0.92  
% 3.32/0.92  --preprocessing_flag                    true
% 3.32/0.92  --time_out_prep_mult                    0.1
% 3.32/0.92  --splitting_mode                        input
% 3.32/0.92  --splitting_grd                         true
% 3.32/0.92  --splitting_cvd                         false
% 3.32/0.92  --splitting_cvd_svl                     false
% 3.32/0.92  --splitting_nvd                         32
% 3.32/0.92  --sub_typing                            true
% 3.32/0.92  --prep_gs_sim                           true
% 3.32/0.92  --prep_unflatten                        true
% 3.32/0.92  --prep_res_sim                          true
% 3.32/0.92  --prep_upred                            true
% 3.32/0.92  --prep_sem_filter                       exhaustive
% 3.32/0.92  --prep_sem_filter_out                   false
% 3.32/0.92  --pred_elim                             true
% 3.32/0.92  --res_sim_input                         true
% 3.32/0.92  --eq_ax_congr_red                       true
% 3.32/0.92  --pure_diseq_elim                       true
% 3.32/0.92  --brand_transform                       false
% 3.32/0.92  --non_eq_to_eq                          false
% 3.32/0.92  --prep_def_merge                        true
% 3.32/0.92  --prep_def_merge_prop_impl              false
% 3.32/0.92  --prep_def_merge_mbd                    true
% 3.32/0.92  --prep_def_merge_tr_red                 false
% 3.32/0.92  --prep_def_merge_tr_cl                  false
% 3.32/0.92  --smt_preprocessing                     true
% 3.32/0.92  --smt_ac_axioms                         fast
% 3.32/0.92  --preprocessed_out                      false
% 3.32/0.92  --preprocessed_stats                    false
% 3.32/0.92  
% 3.32/0.92  ------ Abstraction refinement Options
% 3.32/0.92  
% 3.32/0.92  --abstr_ref                             []
% 3.32/0.92  --abstr_ref_prep                        false
% 3.32/0.92  --abstr_ref_until_sat                   false
% 3.32/0.92  --abstr_ref_sig_restrict                funpre
% 3.32/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.92  --abstr_ref_under                       []
% 3.32/0.92  
% 3.32/0.92  ------ SAT Options
% 3.32/0.92  
% 3.32/0.92  --sat_mode                              false
% 3.32/0.92  --sat_fm_restart_options                ""
% 3.32/0.92  --sat_gr_def                            false
% 3.32/0.92  --sat_epr_types                         true
% 3.32/0.92  --sat_non_cyclic_types                  false
% 3.32/0.92  --sat_finite_models                     false
% 3.32/0.92  --sat_fm_lemmas                         false
% 3.32/0.92  --sat_fm_prep                           false
% 3.32/0.92  --sat_fm_uc_incr                        true
% 3.32/0.92  --sat_out_model                         small
% 3.32/0.92  --sat_out_clauses                       false
% 3.32/0.92  
% 3.32/0.92  ------ QBF Options
% 3.32/0.92  
% 3.32/0.92  --qbf_mode                              false
% 3.32/0.92  --qbf_elim_univ                         false
% 3.32/0.92  --qbf_dom_inst                          none
% 3.32/0.92  --qbf_dom_pre_inst                      false
% 3.32/0.92  --qbf_sk_in                             false
% 3.32/0.92  --qbf_pred_elim                         true
% 3.32/0.92  --qbf_split                             512
% 3.32/0.92  
% 3.32/0.92  ------ BMC1 Options
% 3.32/0.92  
% 3.32/0.92  --bmc1_incremental                      false
% 3.32/0.92  --bmc1_axioms                           reachable_all
% 3.32/0.92  --bmc1_min_bound                        0
% 3.32/0.92  --bmc1_max_bound                        -1
% 3.32/0.92  --bmc1_max_bound_default                -1
% 3.32/0.92  --bmc1_symbol_reachability              true
% 3.32/0.92  --bmc1_property_lemmas                  false
% 3.32/0.92  --bmc1_k_induction                      false
% 3.32/0.92  --bmc1_non_equiv_states                 false
% 3.32/0.92  --bmc1_deadlock                         false
% 3.32/0.92  --bmc1_ucm                              false
% 3.32/0.92  --bmc1_add_unsat_core                   none
% 3.32/0.92  --bmc1_unsat_core_children              false
% 3.32/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.92  --bmc1_out_stat                         full
% 3.32/0.92  --bmc1_ground_init                      false
% 3.32/0.92  --bmc1_pre_inst_next_state              false
% 3.32/0.92  --bmc1_pre_inst_state                   false
% 3.32/0.92  --bmc1_pre_inst_reach_state             false
% 3.32/0.92  --bmc1_out_unsat_core                   false
% 3.32/0.92  --bmc1_aig_witness_out                  false
% 3.32/0.92  --bmc1_verbose                          false
% 3.32/0.92  --bmc1_dump_clauses_tptp                false
% 3.32/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.92  --bmc1_dump_file                        -
% 3.32/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.92  --bmc1_ucm_extend_mode                  1
% 3.32/0.92  --bmc1_ucm_init_mode                    2
% 3.32/0.92  --bmc1_ucm_cone_mode                    none
% 3.32/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.92  --bmc1_ucm_relax_model                  4
% 3.32/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.92  --bmc1_ucm_layered_model                none
% 3.32/0.92  --bmc1_ucm_max_lemma_size               10
% 3.32/0.92  
% 3.32/0.92  ------ AIG Options
% 3.32/0.92  
% 3.32/0.92  --aig_mode                              false
% 3.32/0.92  
% 3.32/0.92  ------ Instantiation Options
% 3.32/0.92  
% 3.32/0.92  --instantiation_flag                    true
% 3.32/0.92  --inst_sos_flag                         true
% 3.32/0.92  --inst_sos_phase                        true
% 3.32/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.92  --inst_lit_sel_side                     num_symb
% 3.32/0.92  --inst_solver_per_active                1400
% 3.32/0.92  --inst_solver_calls_frac                1.
% 3.32/0.92  --inst_passive_queue_type               priority_queues
% 3.32/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.92  --inst_passive_queues_freq              [25;2]
% 3.32/0.92  --inst_dismatching                      true
% 3.32/0.92  --inst_eager_unprocessed_to_passive     true
% 3.32/0.92  --inst_prop_sim_given                   true
% 3.32/0.92  --inst_prop_sim_new                     false
% 3.32/0.92  --inst_subs_new                         false
% 3.32/0.92  --inst_eq_res_simp                      false
% 3.32/0.92  --inst_subs_given                       false
% 3.32/0.92  --inst_orphan_elimination               true
% 3.32/0.92  --inst_learning_loop_flag               true
% 3.32/0.92  --inst_learning_start                   3000
% 3.32/0.92  --inst_learning_factor                  2
% 3.32/0.92  --inst_start_prop_sim_after_learn       3
% 3.32/0.92  --inst_sel_renew                        solver
% 3.32/0.92  --inst_lit_activity_flag                true
% 3.32/0.92  --inst_restr_to_given                   false
% 3.32/0.92  --inst_activity_threshold               500
% 3.32/0.92  --inst_out_proof                        true
% 3.32/0.92  
% 3.32/0.92  ------ Resolution Options
% 3.32/0.92  
% 3.32/0.92  --resolution_flag                       true
% 3.32/0.92  --res_lit_sel                           adaptive
% 3.32/0.92  --res_lit_sel_side                      none
% 3.32/0.92  --res_ordering                          kbo
% 3.32/0.92  --res_to_prop_solver                    active
% 3.32/0.92  --res_prop_simpl_new                    false
% 3.32/0.92  --res_prop_simpl_given                  true
% 3.32/0.92  --res_passive_queue_type                priority_queues
% 3.32/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.92  --res_passive_queues_freq               [15;5]
% 3.32/0.92  --res_forward_subs                      full
% 3.32/0.92  --res_backward_subs                     full
% 3.32/0.92  --res_forward_subs_resolution           true
% 3.32/0.92  --res_backward_subs_resolution          true
% 3.32/0.92  --res_orphan_elimination                true
% 3.32/0.92  --res_time_limit                        2.
% 3.32/0.92  --res_out_proof                         true
% 3.32/0.92  
% 3.32/0.92  ------ Superposition Options
% 3.32/0.92  
% 3.32/0.92  --superposition_flag                    true
% 3.32/0.92  --sup_passive_queue_type                priority_queues
% 3.32/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.92  --demod_completeness_check              fast
% 3.32/0.92  --demod_use_ground                      true
% 3.32/0.92  --sup_to_prop_solver                    passive
% 3.32/0.92  --sup_prop_simpl_new                    true
% 3.32/0.92  --sup_prop_simpl_given                  true
% 3.32/0.92  --sup_fun_splitting                     true
% 3.32/0.92  --sup_smt_interval                      50000
% 3.32/0.92  
% 3.32/0.92  ------ Superposition Simplification Setup
% 3.32/0.92  
% 3.32/0.92  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.32/0.92  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.32/0.92  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.32/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.32/0.92  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.32/0.92  --sup_immed_triv                        [TrivRules]
% 3.32/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.92  --sup_immed_bw_main                     []
% 3.32/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.32/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.92  --sup_input_bw                          []
% 3.32/0.92  
% 3.32/0.92  ------ Combination Options
% 3.32/0.92  
% 3.32/0.92  --comb_res_mult                         3
% 3.32/0.92  --comb_sup_mult                         2
% 3.32/0.92  --comb_inst_mult                        10
% 3.32/0.92  
% 3.32/0.92  ------ Debug Options
% 3.32/0.92  
% 3.32/0.92  --dbg_backtrace                         false
% 3.32/0.92  --dbg_dump_prop_clauses                 false
% 3.32/0.92  --dbg_dump_prop_clauses_file            -
% 3.32/0.92  --dbg_out_stat                          false
% 3.32/0.92  ------ Parsing...
% 3.32/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.92  
% 3.32/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.32/0.92  
% 3.32/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.92  
% 3.32/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.92  ------ Proving...
% 3.32/0.92  ------ Problem Properties 
% 3.32/0.92  
% 3.32/0.92  
% 3.32/0.92  clauses                                 18
% 3.32/0.92  conjectures                             2
% 3.32/0.92  EPR                                     4
% 3.32/0.92  Horn                                    13
% 3.32/0.92  unary                                   4
% 3.32/0.92  binary                                  5
% 3.32/0.92  lits                                    45
% 3.32/0.92  lits eq                                 13
% 3.32/0.92  fd_pure                                 0
% 3.32/0.92  fd_pseudo                               0
% 3.32/0.92  fd_cond                                 0
% 3.32/0.92  fd_pseudo_cond                          7
% 3.32/0.92  AC symbols                              0
% 3.32/0.92  
% 3.32/0.92  ------ Schedule dynamic 5 is on 
% 3.32/0.92  
% 3.32/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/0.92  
% 3.32/0.92  
% 3.32/0.92  ------ 
% 3.32/0.92  Current options:
% 3.32/0.92  ------ 
% 3.32/0.92  
% 3.32/0.92  ------ Input Options
% 3.32/0.92  
% 3.32/0.92  --out_options                           all
% 3.32/0.92  --tptp_safe_out                         true
% 3.32/0.92  --problem_path                          ""
% 3.32/0.92  --include_path                          ""
% 3.32/0.92  --clausifier                            res/vclausify_rel
% 3.32/0.92  --clausifier_options                    ""
% 3.32/0.92  --stdin                                 false
% 3.32/0.92  --stats_out                             all
% 3.32/0.92  
% 3.32/0.92  ------ General Options
% 3.32/0.92  
% 3.32/0.92  --fof                                   false
% 3.32/0.92  --time_out_real                         305.
% 3.32/0.92  --time_out_virtual                      -1.
% 3.32/0.92  --symbol_type_check                     false
% 3.32/0.92  --clausify_out                          false
% 3.32/0.92  --sig_cnt_out                           false
% 3.32/0.92  --trig_cnt_out                          false
% 3.32/0.92  --trig_cnt_out_tolerance                1.
% 3.32/0.92  --trig_cnt_out_sk_spl                   false
% 3.32/0.92  --abstr_cl_out                          false
% 3.32/0.92  
% 3.32/0.92  ------ Global Options
% 3.32/0.92  
% 3.32/0.92  --schedule                              default
% 3.32/0.92  --add_important_lit                     false
% 3.32/0.92  --prop_solver_per_cl                    1000
% 3.32/0.92  --min_unsat_core                        false
% 3.32/0.92  --soft_assumptions                      false
% 3.32/0.92  --soft_lemma_size                       3
% 3.32/0.92  --prop_impl_unit_size                   0
% 3.32/0.92  --prop_impl_unit                        []
% 3.32/0.92  --share_sel_clauses                     true
% 3.32/0.92  --reset_solvers                         false
% 3.32/0.92  --bc_imp_inh                            [conj_cone]
% 3.32/0.92  --conj_cone_tolerance                   3.
% 3.32/0.92  --extra_neg_conj                        none
% 3.32/0.92  --large_theory_mode                     true
% 3.32/0.92  --prolific_symb_bound                   200
% 3.32/0.92  --lt_threshold                          2000
% 3.32/0.92  --clause_weak_htbl                      true
% 3.32/0.92  --gc_record_bc_elim                     false
% 3.32/0.92  
% 3.32/0.92  ------ Preprocessing Options
% 3.32/0.92  
% 3.32/0.92  --preprocessing_flag                    true
% 3.32/0.92  --time_out_prep_mult                    0.1
% 3.32/0.92  --splitting_mode                        input
% 3.32/0.92  --splitting_grd                         true
% 3.32/0.92  --splitting_cvd                         false
% 3.32/0.92  --splitting_cvd_svl                     false
% 3.32/0.92  --splitting_nvd                         32
% 3.32/0.92  --sub_typing                            true
% 3.32/0.92  --prep_gs_sim                           true
% 3.32/0.92  --prep_unflatten                        true
% 3.32/0.92  --prep_res_sim                          true
% 3.32/0.92  --prep_upred                            true
% 3.32/0.92  --prep_sem_filter                       exhaustive
% 3.32/0.92  --prep_sem_filter_out                   false
% 3.32/0.92  --pred_elim                             true
% 3.32/0.92  --res_sim_input                         true
% 3.32/0.92  --eq_ax_congr_red                       true
% 3.32/0.92  --pure_diseq_elim                       true
% 3.32/0.92  --brand_transform                       false
% 3.32/0.92  --non_eq_to_eq                          false
% 3.32/0.92  --prep_def_merge                        true
% 3.32/0.92  --prep_def_merge_prop_impl              false
% 3.32/0.92  --prep_def_merge_mbd                    true
% 3.32/0.92  --prep_def_merge_tr_red                 false
% 3.32/0.92  --prep_def_merge_tr_cl                  false
% 3.32/0.92  --smt_preprocessing                     true
% 3.32/0.92  --smt_ac_axioms                         fast
% 3.32/0.92  --preprocessed_out                      false
% 3.32/0.92  --preprocessed_stats                    false
% 3.32/0.92  
% 3.32/0.92  ------ Abstraction refinement Options
% 3.32/0.92  
% 3.32/0.92  --abstr_ref                             []
% 3.32/0.92  --abstr_ref_prep                        false
% 3.32/0.92  --abstr_ref_until_sat                   false
% 3.32/0.92  --abstr_ref_sig_restrict                funpre
% 3.32/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.92  --abstr_ref_under                       []
% 3.32/0.92  
% 3.32/0.92  ------ SAT Options
% 3.32/0.92  
% 3.32/0.92  --sat_mode                              false
% 3.32/0.92  --sat_fm_restart_options                ""
% 3.32/0.92  --sat_gr_def                            false
% 3.32/0.92  --sat_epr_types                         true
% 3.32/0.92  --sat_non_cyclic_types                  false
% 3.32/0.92  --sat_finite_models                     false
% 3.32/0.92  --sat_fm_lemmas                         false
% 3.32/0.92  --sat_fm_prep                           false
% 3.32/0.92  --sat_fm_uc_incr                        true
% 3.32/0.92  --sat_out_model                         small
% 3.32/0.92  --sat_out_clauses                       false
% 3.32/0.92  
% 3.32/0.92  ------ QBF Options
% 3.32/0.92  
% 3.32/0.92  --qbf_mode                              false
% 3.32/0.92  --qbf_elim_univ                         false
% 3.32/0.92  --qbf_dom_inst                          none
% 3.32/0.92  --qbf_dom_pre_inst                      false
% 3.32/0.92  --qbf_sk_in                             false
% 3.32/0.92  --qbf_pred_elim                         true
% 3.32/0.92  --qbf_split                             512
% 3.32/0.92  
% 3.32/0.92  ------ BMC1 Options
% 3.32/0.92  
% 3.32/0.92  --bmc1_incremental                      false
% 3.32/0.92  --bmc1_axioms                           reachable_all
% 3.32/0.92  --bmc1_min_bound                        0
% 3.32/0.92  --bmc1_max_bound                        -1
% 3.32/0.92  --bmc1_max_bound_default                -1
% 3.32/0.92  --bmc1_symbol_reachability              true
% 3.32/0.92  --bmc1_property_lemmas                  false
% 3.32/0.92  --bmc1_k_induction                      false
% 3.32/0.92  --bmc1_non_equiv_states                 false
% 3.32/0.92  --bmc1_deadlock                         false
% 3.32/0.92  --bmc1_ucm                              false
% 3.32/0.92  --bmc1_add_unsat_core                   none
% 3.32/0.92  --bmc1_unsat_core_children              false
% 3.32/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.92  --bmc1_out_stat                         full
% 3.32/0.92  --bmc1_ground_init                      false
% 3.32/0.92  --bmc1_pre_inst_next_state              false
% 3.32/0.92  --bmc1_pre_inst_state                   false
% 3.32/0.92  --bmc1_pre_inst_reach_state             false
% 3.32/0.92  --bmc1_out_unsat_core                   false
% 3.32/0.92  --bmc1_aig_witness_out                  false
% 3.32/0.92  --bmc1_verbose                          false
% 3.32/0.92  --bmc1_dump_clauses_tptp                false
% 3.32/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.92  --bmc1_dump_file                        -
% 3.32/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.92  --bmc1_ucm_extend_mode                  1
% 3.32/0.92  --bmc1_ucm_init_mode                    2
% 3.32/0.92  --bmc1_ucm_cone_mode                    none
% 3.32/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.92  --bmc1_ucm_relax_model                  4
% 3.32/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.92  --bmc1_ucm_layered_model                none
% 3.32/0.92  --bmc1_ucm_max_lemma_size               10
% 3.32/0.92  
% 3.32/0.92  ------ AIG Options
% 3.32/0.92  
% 3.32/0.92  --aig_mode                              false
% 3.32/0.92  
% 3.32/0.92  ------ Instantiation Options
% 3.32/0.92  
% 3.32/0.92  --instantiation_flag                    true
% 3.32/0.92  --inst_sos_flag                         true
% 3.32/0.92  --inst_sos_phase                        true
% 3.32/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.92  --inst_lit_sel_side                     none
% 3.32/0.92  --inst_solver_per_active                1400
% 3.32/0.92  --inst_solver_calls_frac                1.
% 3.32/0.92  --inst_passive_queue_type               priority_queues
% 3.32/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.92  --inst_passive_queues_freq              [25;2]
% 3.32/0.92  --inst_dismatching                      true
% 3.32/0.92  --inst_eager_unprocessed_to_passive     true
% 3.32/0.92  --inst_prop_sim_given                   true
% 3.32/0.92  --inst_prop_sim_new                     false
% 3.32/0.92  --inst_subs_new                         false
% 3.32/0.92  --inst_eq_res_simp                      false
% 3.32/0.92  --inst_subs_given                       false
% 3.32/0.92  --inst_orphan_elimination               true
% 3.32/0.92  --inst_learning_loop_flag               true
% 3.32/0.92  --inst_learning_start                   3000
% 3.32/0.92  --inst_learning_factor                  2
% 3.32/0.92  --inst_start_prop_sim_after_learn       3
% 3.32/0.92  --inst_sel_renew                        solver
% 3.32/0.92  --inst_lit_activity_flag                true
% 3.32/0.92  --inst_restr_to_given                   false
% 3.32/0.92  --inst_activity_threshold               500
% 3.32/0.92  --inst_out_proof                        true
% 3.32/0.92  
% 3.32/0.92  ------ Resolution Options
% 3.32/0.92  
% 3.32/0.92  --resolution_flag                       false
% 3.32/0.92  --res_lit_sel                           adaptive
% 3.32/0.92  --res_lit_sel_side                      none
% 3.32/0.92  --res_ordering                          kbo
% 3.32/0.92  --res_to_prop_solver                    active
% 3.32/0.92  --res_prop_simpl_new                    false
% 3.32/0.92  --res_prop_simpl_given                  true
% 3.32/0.92  --res_passive_queue_type                priority_queues
% 3.32/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.92  --res_passive_queues_freq               [15;5]
% 3.32/0.92  --res_forward_subs                      full
% 3.32/0.92  --res_backward_subs                     full
% 3.32/0.92  --res_forward_subs_resolution           true
% 3.32/0.92  --res_backward_subs_resolution          true
% 3.32/0.92  --res_orphan_elimination                true
% 3.32/0.92  --res_time_limit                        2.
% 3.32/0.92  --res_out_proof                         true
% 3.32/0.92  
% 3.32/0.92  ------ Superposition Options
% 3.32/0.92  
% 3.32/0.92  --superposition_flag                    true
% 3.32/0.92  --sup_passive_queue_type                priority_queues
% 3.32/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.92  --demod_completeness_check              fast
% 3.32/0.92  --demod_use_ground                      true
% 3.32/0.92  --sup_to_prop_solver                    passive
% 3.32/0.92  --sup_prop_simpl_new                    true
% 3.32/0.92  --sup_prop_simpl_given                  true
% 3.32/0.92  --sup_fun_splitting                     true
% 3.32/0.92  --sup_smt_interval                      50000
% 3.32/0.92  
% 3.32/0.92  ------ Superposition Simplification Setup
% 3.32/0.92  
% 3.32/0.92  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.32/0.92  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.32/0.92  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.32/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.32/0.92  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.32/0.92  --sup_immed_triv                        [TrivRules]
% 3.32/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.92  --sup_immed_bw_main                     []
% 3.32/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.32/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.92  --sup_input_bw                          []
% 3.32/0.92  
% 3.32/0.92  ------ Combination Options
% 3.32/0.92  
% 3.32/0.92  --comb_res_mult                         3
% 3.32/0.92  --comb_sup_mult                         2
% 3.32/0.92  --comb_inst_mult                        10
% 3.32/0.92  
% 3.32/0.92  ------ Debug Options
% 3.32/0.92  
% 3.32/0.92  --dbg_backtrace                         false
% 3.32/0.92  --dbg_dump_prop_clauses                 false
% 3.32/0.92  --dbg_dump_prop_clauses_file            -
% 3.32/0.92  --dbg_out_stat                          false
% 3.32/0.92  
% 3.32/0.92  
% 3.32/0.92  
% 3.32/0.92  
% 3.32/0.92  ------ Proving...
% 3.32/0.92  
% 3.32/0.92  
% 3.32/0.92  % SZS status Theorem for theBenchmark.p
% 3.32/0.92  
% 3.32/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.92  
% 3.32/0.92  fof(f2,axiom,(
% 3.32/0.92    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f22,plain,(
% 3.32/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.32/0.92    inference(nnf_transformation,[],[f2])).
% 3.32/0.92  
% 3.32/0.92  fof(f23,plain,(
% 3.32/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.32/0.92    inference(flattening,[],[f22])).
% 3.32/0.92  
% 3.32/0.92  fof(f24,plain,(
% 3.32/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.32/0.92    inference(rectify,[],[f23])).
% 3.32/0.92  
% 3.32/0.92  fof(f25,plain,(
% 3.32/0.92    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.32/0.92    introduced(choice_axiom,[])).
% 3.32/0.92  
% 3.32/0.92  fof(f26,plain,(
% 3.32/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.32/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.32/0.92  
% 3.32/0.92  fof(f40,plain,(
% 3.32/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.32/0.92    inference(cnf_transformation,[],[f26])).
% 3.32/0.92  
% 3.32/0.92  fof(f74,plain,(
% 3.32/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.32/0.92    inference(equality_resolution,[],[f40])).
% 3.32/0.92  
% 3.32/0.92  fof(f9,axiom,(
% 3.32/0.92    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f18,plain,(
% 3.32/0.92    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.32/0.92    inference(ennf_transformation,[],[f9])).
% 3.32/0.92  
% 3.32/0.92  fof(f19,plain,(
% 3.32/0.92    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.32/0.92    inference(flattening,[],[f18])).
% 3.32/0.92  
% 3.32/0.92  fof(f57,plain,(
% 3.32/0.92    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.32/0.92    inference(cnf_transformation,[],[f19])).
% 3.32/0.92  
% 3.32/0.92  fof(f11,conjecture,(
% 3.32/0.92    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f12,negated_conjecture,(
% 3.32/0.92    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.32/0.92    inference(negated_conjecture,[],[f11])).
% 3.32/0.92  
% 3.32/0.92  fof(f21,plain,(
% 3.32/0.92    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.32/0.92    inference(ennf_transformation,[],[f12])).
% 3.32/0.92  
% 3.32/0.92  fof(f33,plain,(
% 3.32/0.92    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.32/0.92    inference(nnf_transformation,[],[f21])).
% 3.32/0.92  
% 3.32/0.92  fof(f34,plain,(
% 3.32/0.92    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.32/0.92    inference(flattening,[],[f33])).
% 3.32/0.92  
% 3.32/0.92  fof(f36,plain,(
% 3.32/0.92    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK3) | ~r2_hidden(X0,k1_ordinal1(sK3))) & (r1_ordinal1(X0,sK3) | r2_hidden(X0,k1_ordinal1(sK3))) & v3_ordinal1(sK3))) )),
% 3.32/0.92    introduced(choice_axiom,[])).
% 3.32/0.92  
% 3.32/0.92  fof(f35,plain,(
% 3.32/0.92    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK2,X1) | ~r2_hidden(sK2,k1_ordinal1(X1))) & (r1_ordinal1(sK2,X1) | r2_hidden(sK2,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 3.32/0.92    introduced(choice_axiom,[])).
% 3.32/0.92  
% 3.32/0.92  fof(f37,plain,(
% 3.32/0.92    ((~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))) & (r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 3.32/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).
% 3.32/0.92  
% 3.32/0.92  fof(f62,plain,(
% 3.32/0.92    ~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))),
% 3.32/0.92    inference(cnf_transformation,[],[f37])).
% 3.32/0.92  
% 3.32/0.92  fof(f6,axiom,(
% 3.32/0.92    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f53,plain,(
% 3.32/0.92    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.32/0.92    inference(cnf_transformation,[],[f6])).
% 3.32/0.92  
% 3.32/0.92  fof(f4,axiom,(
% 3.32/0.92    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f51,plain,(
% 3.32/0.92    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.32/0.92    inference(cnf_transformation,[],[f4])).
% 3.32/0.92  
% 3.32/0.92  fof(f5,axiom,(
% 3.32/0.92    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f52,plain,(
% 3.32/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.32/0.92    inference(cnf_transformation,[],[f5])).
% 3.32/0.92  
% 3.32/0.92  fof(f63,plain,(
% 3.32/0.92    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.32/0.92    inference(definition_unfolding,[],[f51,f52])).
% 3.32/0.92  
% 3.32/0.92  fof(f64,plain,(
% 3.32/0.92    ( ! [X0] : (k2_xboole_0(X0,k1_enumset1(X0,X0,X0)) = k1_ordinal1(X0)) )),
% 3.32/0.92    inference(definition_unfolding,[],[f53,f63])).
% 3.32/0.92  
% 3.32/0.92  fof(f71,plain,(
% 3.32/0.92    ~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))),
% 3.32/0.92    inference(definition_unfolding,[],[f62,f64])).
% 3.32/0.92  
% 3.32/0.92  fof(f59,plain,(
% 3.32/0.92    v3_ordinal1(sK2)),
% 3.32/0.92    inference(cnf_transformation,[],[f37])).
% 3.32/0.92  
% 3.32/0.92  fof(f60,plain,(
% 3.32/0.92    v3_ordinal1(sK3)),
% 3.32/0.92    inference(cnf_transformation,[],[f37])).
% 3.32/0.92  
% 3.32/0.92  fof(f1,axiom,(
% 3.32/0.92    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f13,plain,(
% 3.32/0.92    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.32/0.92    inference(ennf_transformation,[],[f1])).
% 3.32/0.92  
% 3.32/0.92  fof(f38,plain,(
% 3.32/0.92    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.32/0.92    inference(cnf_transformation,[],[f13])).
% 3.32/0.92  
% 3.32/0.92  fof(f7,axiom,(
% 3.32/0.92    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f14,plain,(
% 3.32/0.92    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.32/0.92    inference(ennf_transformation,[],[f7])).
% 3.32/0.92  
% 3.32/0.92  fof(f15,plain,(
% 3.32/0.92    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.32/0.92    inference(flattening,[],[f14])).
% 3.32/0.92  
% 3.32/0.92  fof(f32,plain,(
% 3.32/0.92    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.32/0.92    inference(nnf_transformation,[],[f15])).
% 3.32/0.92  
% 3.32/0.92  fof(f54,plain,(
% 3.32/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.32/0.92    inference(cnf_transformation,[],[f32])).
% 3.32/0.92  
% 3.32/0.92  fof(f10,axiom,(
% 3.32/0.92    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f20,plain,(
% 3.32/0.92    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.32/0.92    inference(ennf_transformation,[],[f10])).
% 3.32/0.92  
% 3.32/0.92  fof(f58,plain,(
% 3.32/0.92    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.32/0.92    inference(cnf_transformation,[],[f20])).
% 3.32/0.92  
% 3.32/0.92  fof(f61,plain,(
% 3.32/0.92    r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))),
% 3.32/0.92    inference(cnf_transformation,[],[f37])).
% 3.32/0.92  
% 3.32/0.92  fof(f72,plain,(
% 3.32/0.92    r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))),
% 3.32/0.92    inference(definition_unfolding,[],[f61,f64])).
% 3.32/0.92  
% 3.32/0.92  fof(f39,plain,(
% 3.32/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.32/0.92    inference(cnf_transformation,[],[f26])).
% 3.32/0.92  
% 3.32/0.92  fof(f75,plain,(
% 3.32/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.32/0.92    inference(equality_resolution,[],[f39])).
% 3.32/0.92  
% 3.32/0.92  fof(f8,axiom,(
% 3.32/0.92    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f16,plain,(
% 3.32/0.92    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.32/0.92    inference(ennf_transformation,[],[f8])).
% 3.32/0.92  
% 3.32/0.92  fof(f17,plain,(
% 3.32/0.92    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.32/0.92    inference(flattening,[],[f16])).
% 3.32/0.92  
% 3.32/0.92  fof(f56,plain,(
% 3.32/0.92    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.32/0.92    inference(cnf_transformation,[],[f17])).
% 3.32/0.92  
% 3.32/0.92  fof(f3,axiom,(
% 3.32/0.92    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.32/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.92  
% 3.32/0.92  fof(f27,plain,(
% 3.32/0.92    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.32/0.92    inference(nnf_transformation,[],[f3])).
% 3.32/0.92  
% 3.32/0.92  fof(f28,plain,(
% 3.32/0.92    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.32/0.92    inference(flattening,[],[f27])).
% 3.32/0.92  
% 3.32/0.92  fof(f29,plain,(
% 3.32/0.92    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.32/0.92    inference(rectify,[],[f28])).
% 3.32/0.92  
% 3.32/0.92  fof(f30,plain,(
% 3.32/0.92    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.32/0.92    introduced(choice_axiom,[])).
% 3.32/0.92  
% 3.32/0.92  fof(f31,plain,(
% 3.32/0.92    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.32/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 3.32/0.92  
% 3.32/0.92  fof(f45,plain,(
% 3.32/0.92    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.32/0.92    inference(cnf_transformation,[],[f31])).
% 3.32/0.92  
% 3.32/0.92  fof(f70,plain,(
% 3.32/0.92    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 3.32/0.92    inference(definition_unfolding,[],[f45,f52])).
% 3.32/0.92  
% 3.32/0.92  fof(f80,plain,(
% 3.32/0.92    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 3.32/0.92    inference(equality_resolution,[],[f70])).
% 3.32/0.92  
% 3.32/0.92  fof(f41,plain,(
% 3.32/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.32/0.92    inference(cnf_transformation,[],[f26])).
% 3.32/0.92  
% 3.32/0.92  fof(f73,plain,(
% 3.32/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.32/0.92    inference(equality_resolution,[],[f41])).
% 3.32/0.92  
% 3.32/0.92  fof(f46,plain,(
% 3.32/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.32/0.92    inference(cnf_transformation,[],[f31])).
% 3.32/0.92  
% 3.32/0.92  fof(f69,plain,(
% 3.32/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 3.32/0.92    inference(definition_unfolding,[],[f46,f52])).
% 3.32/0.92  
% 3.32/0.92  fof(f78,plain,(
% 3.32/0.92    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 3.32/0.92    inference(equality_resolution,[],[f69])).
% 3.32/0.92  
% 3.32/0.92  fof(f79,plain,(
% 3.32/0.92    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 3.32/0.92    inference(equality_resolution,[],[f78])).
% 3.32/0.92  
% 3.32/0.92  cnf(c_507,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_3112,plain,
% 3.32/0.92      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_507]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_3113,plain,
% 3.32/0.92      ( sK3 != sK3 | sK3 = sK2 | sK2 != sK3 ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_3112]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_508,plain,
% 3.32/0.92      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.32/0.92      theory(equality) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_3046,plain,
% 3.32/0.92      ( r2_hidden(X0,X1) | ~ r2_hidden(sK3,sK2) | X0 != sK3 | X1 != sK2 ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_508]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_3049,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK3)
% 3.32/0.92      | ~ r2_hidden(sK3,sK2)
% 3.32/0.92      | sK3 != sK3
% 3.32/0.92      | sK3 != sK2 ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_3046]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_5,plain,
% 3.32/0.92      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.32/0.92      inference(cnf_transformation,[],[f74]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_911,plain,
% 3.32/0.92      ( r2_hidden(X0,X1) != iProver_top
% 3.32/0.92      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_16,plain,
% 3.32/0.92      ( r1_ordinal1(X0,X1)
% 3.32/0.92      | r2_hidden(X1,X0)
% 3.32/0.92      | ~ v3_ordinal1(X1)
% 3.32/0.92      | ~ v3_ordinal1(X0) ),
% 3.32/0.92      inference(cnf_transformation,[],[f57]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_18,negated_conjecture,
% 3.32/0.92      ( ~ r1_ordinal1(sK2,sK3)
% 3.32/0.92      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.32/0.92      inference(cnf_transformation,[],[f71]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_166,plain,
% 3.32/0.92      ( ~ r1_ordinal1(sK2,sK3)
% 3.32/0.92      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.32/0.92      inference(prop_impl,[status(thm)],[c_18]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_309,plain,
% 3.32/0.92      ( r2_hidden(X0,X1)
% 3.32/0.92      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.32/0.92      | ~ v3_ordinal1(X1)
% 3.32/0.92      | ~ v3_ordinal1(X0)
% 3.32/0.92      | sK3 != X0
% 3.32/0.92      | sK2 != X1 ),
% 3.32/0.92      inference(resolution_lifted,[status(thm)],[c_16,c_166]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_310,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK2)
% 3.32/0.92      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.32/0.92      | ~ v3_ordinal1(sK3)
% 3.32/0.92      | ~ v3_ordinal1(sK2) ),
% 3.32/0.92      inference(unflattening,[status(thm)],[c_309]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_21,negated_conjecture,
% 3.32/0.92      ( v3_ordinal1(sK2) ),
% 3.32/0.92      inference(cnf_transformation,[],[f59]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_20,negated_conjecture,
% 3.32/0.92      ( v3_ordinal1(sK3) ),
% 3.32/0.92      inference(cnf_transformation,[],[f60]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_312,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK2)
% 3.32/0.92      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.32/0.92      inference(global_propositional_subsumption,
% 3.32/0.92                [status(thm)],
% 3.32/0.92                [c_310,c_21,c_20]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_402,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK2)
% 3.32/0.92      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.32/0.92      inference(prop_impl,[status(thm)],[c_21,c_20,c_310]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_900,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK2) = iProver_top
% 3.32/0.92      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) != iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_1676,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK2) = iProver_top
% 3.32/0.92      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.32/0.92      inference(superposition,[status(thm)],[c_911,c_900]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_0,plain,
% 3.32/0.92      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.32/0.92      inference(cnf_transformation,[],[f38]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_958,plain,
% 3.32/0.92      ( ~ r2_hidden(sK3,sK2) | ~ r2_hidden(sK2,sK3) ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_0]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_959,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK2) != iProver_top
% 3.32/0.92      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_958]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_2490,plain,
% 3.32/0.92      ( r2_hidden(sK2,sK3) != iProver_top ),
% 3.32/0.92      inference(global_propositional_subsumption,
% 3.32/0.92                [status(thm)],
% 3.32/0.92                [c_1676,c_959]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_14,plain,
% 3.32/0.92      ( r1_tarski(X0,X1)
% 3.32/0.92      | ~ r1_ordinal1(X0,X1)
% 3.32/0.92      | ~ v3_ordinal1(X1)
% 3.32/0.92      | ~ v3_ordinal1(X0) ),
% 3.32/0.92      inference(cnf_transformation,[],[f54]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_17,plain,
% 3.32/0.92      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.32/0.92      inference(cnf_transformation,[],[f58]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_286,plain,
% 3.32/0.92      ( ~ r1_ordinal1(X0,X1)
% 3.32/0.92      | ~ r2_hidden(X1,X0)
% 3.32/0.92      | ~ v3_ordinal1(X0)
% 3.32/0.92      | ~ v3_ordinal1(X1) ),
% 3.32/0.92      inference(resolution,[status(thm)],[c_14,c_17]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_19,negated_conjecture,
% 3.32/0.92      ( r1_ordinal1(sK2,sK3)
% 3.32/0.92      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.32/0.92      inference(cnf_transformation,[],[f72]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_168,plain,
% 3.32/0.92      ( r1_ordinal1(sK2,sK3)
% 3.32/0.92      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.32/0.92      inference(prop_impl,[status(thm)],[c_19]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_323,plain,
% 3.32/0.92      ( ~ r2_hidden(X0,X1)
% 3.32/0.92      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.32/0.92      | ~ v3_ordinal1(X1)
% 3.32/0.92      | ~ v3_ordinal1(X0)
% 3.32/0.92      | sK3 != X0
% 3.32/0.92      | sK2 != X1 ),
% 3.32/0.92      inference(resolution_lifted,[status(thm)],[c_286,c_168]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_324,plain,
% 3.32/0.92      ( ~ r2_hidden(sK3,sK2)
% 3.32/0.92      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.32/0.92      | ~ v3_ordinal1(sK3)
% 3.32/0.92      | ~ v3_ordinal1(sK2) ),
% 3.32/0.92      inference(unflattening,[status(thm)],[c_323]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_326,plain,
% 3.32/0.92      ( ~ r2_hidden(sK3,sK2)
% 3.32/0.92      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.32/0.92      inference(global_propositional_subsumption,
% 3.32/0.92                [status(thm)],
% 3.32/0.92                [c_324,c_21,c_20]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_404,plain,
% 3.32/0.92      ( ~ r2_hidden(sK3,sK2)
% 3.32/0.92      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.32/0.92      inference(prop_impl,[status(thm)],[c_21,c_20,c_324]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_899,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK2) != iProver_top
% 3.32/0.92      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) = iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_6,plain,
% 3.32/0.92      ( r2_hidden(X0,X1)
% 3.32/0.92      | r2_hidden(X0,X2)
% 3.32/0.92      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.32/0.92      inference(cnf_transformation,[],[f75]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_910,plain,
% 3.32/0.92      ( r2_hidden(X0,X1) = iProver_top
% 3.32/0.92      | r2_hidden(X0,X2) = iProver_top
% 3.32/0.92      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_2065,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK2) != iProver_top
% 3.32/0.92      | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 3.32/0.92      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.32/0.92      inference(superposition,[status(thm)],[c_899,c_910]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_15,plain,
% 3.32/0.92      ( r2_hidden(X0,X1)
% 3.32/0.92      | r2_hidden(X1,X0)
% 3.32/0.92      | ~ v3_ordinal1(X0)
% 3.32/0.92      | ~ v3_ordinal1(X1)
% 3.32/0.92      | X1 = X0 ),
% 3.32/0.92      inference(cnf_transformation,[],[f56]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_2051,plain,
% 3.32/0.92      ( r2_hidden(X0,sK2)
% 3.32/0.92      | r2_hidden(sK2,X0)
% 3.32/0.92      | ~ v3_ordinal1(X0)
% 3.32/0.92      | ~ v3_ordinal1(sK2)
% 3.32/0.92      | sK2 = X0 ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_15]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_2052,plain,
% 3.32/0.92      ( sK2 = X0
% 3.32/0.92      | r2_hidden(X0,sK2) = iProver_top
% 3.32/0.92      | r2_hidden(sK2,X0) = iProver_top
% 3.32/0.92      | v3_ordinal1(X0) != iProver_top
% 3.32/0.92      | v3_ordinal1(sK2) != iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_2051]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_2054,plain,
% 3.32/0.92      ( sK2 = sK3
% 3.32/0.92      | r2_hidden(sK3,sK2) = iProver_top
% 3.32/0.92      | r2_hidden(sK2,sK3) = iProver_top
% 3.32/0.92      | v3_ordinal1(sK3) != iProver_top
% 3.32/0.92      | v3_ordinal1(sK2) != iProver_top ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_2052]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_12,plain,
% 3.32/0.92      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.32/0.92      inference(cnf_transformation,[],[f80]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_2046,plain,
% 3.32/0.92      ( ~ r2_hidden(sK2,k1_enumset1(X0,X0,X1)) | sK2 = X0 | sK2 = X1 ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_12]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_2047,plain,
% 3.32/0.92      ( sK2 = X0
% 3.32/0.92      | sK2 = X1
% 3.32/0.92      | r2_hidden(sK2,k1_enumset1(X0,X0,X1)) != iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_2046]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_2049,plain,
% 3.32/0.92      ( sK2 = sK3
% 3.32/0.92      | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_2047]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_4,plain,
% 3.32/0.92      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.32/0.92      inference(cnf_transformation,[],[f73]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_912,plain,
% 3.32/0.92      ( r2_hidden(X0,X1) != iProver_top
% 3.32/0.92      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_1675,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK2) = iProver_top
% 3.32/0.92      | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
% 3.32/0.92      inference(superposition,[status(thm)],[c_912,c_900]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_1678,plain,
% 3.32/0.92      ( r2_hidden(sK3,sK2) | ~ r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) ),
% 3.32/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_1675]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_979,plain,
% 3.32/0.92      ( r2_hidden(X0,X1)
% 3.32/0.92      | ~ r2_hidden(X2,k1_enumset1(X3,X3,X2))
% 3.32/0.92      | X0 != X2
% 3.32/0.92      | X1 != k1_enumset1(X3,X3,X2) ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_508]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_1035,plain,
% 3.32/0.92      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X0))
% 3.32/0.92      | r2_hidden(X2,k1_enumset1(X3,X3,X4))
% 3.32/0.92      | X2 != X0
% 3.32/0.92      | k1_enumset1(X3,X3,X4) != k1_enumset1(X1,X1,X0) ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_979]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_1557,plain,
% 3.32/0.92      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X0))
% 3.32/0.92      | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
% 3.32/0.92      | k1_enumset1(sK3,sK3,sK3) != k1_enumset1(X1,X1,X0)
% 3.32/0.92      | sK2 != X0 ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_1035]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_1558,plain,
% 3.32/0.92      ( k1_enumset1(sK3,sK3,sK3) != k1_enumset1(X0,X0,X1)
% 3.32/0.92      | sK2 != X1
% 3.32/0.92      | r2_hidden(X1,k1_enumset1(X0,X0,X1)) != iProver_top
% 3.32/0.92      | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_1557]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_1560,plain,
% 3.32/0.92      ( k1_enumset1(sK3,sK3,sK3) != k1_enumset1(sK3,sK3,sK3)
% 3.32/0.92      | sK2 != sK3
% 3.32/0.92      | r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) != iProver_top
% 3.32/0.92      | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_1558]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_1559,plain,
% 3.32/0.92      ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
% 3.32/0.92      | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
% 3.32/0.92      | k1_enumset1(sK3,sK3,sK3) != k1_enumset1(sK3,sK3,sK3)
% 3.32/0.92      | sK2 != sK3 ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_1557]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_510,plain,
% 3.32/0.92      ( X0 != X1
% 3.32/0.92      | X2 != X3
% 3.32/0.92      | X4 != X5
% 3.32/0.92      | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
% 3.32/0.92      theory(equality) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_514,plain,
% 3.32/0.92      ( k1_enumset1(sK3,sK3,sK3) = k1_enumset1(sK3,sK3,sK3)
% 3.32/0.92      | sK3 != sK3 ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_510]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_70,plain,
% 3.32/0.92      ( ~ r2_hidden(sK3,sK3) ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_0]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_11,plain,
% 3.32/0.92      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 3.32/0.92      inference(cnf_transformation,[],[f79]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_44,plain,
% 3.32/0.92      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_46,plain,
% 3.32/0.92      ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_44]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_45,plain,
% 3.32/0.92      ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_11]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_42,plain,
% 3.32/0.92      ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | sK3 = sK3 ),
% 3.32/0.92      inference(instantiation,[status(thm)],[c_12]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_23,plain,
% 3.32/0.92      ( v3_ordinal1(sK3) = iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(c_22,plain,
% 3.32/0.92      ( v3_ordinal1(sK2) = iProver_top ),
% 3.32/0.92      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.32/0.92  
% 3.32/0.92  cnf(contradiction,plain,
% 3.32/0.92      ( $false ),
% 3.32/0.92      inference(minisat,
% 3.32/0.92                [status(thm)],
% 3.32/0.92                [c_3113,c_3049,c_2490,c_2065,c_2054,c_2049,c_1678,c_1675,
% 3.32/0.92                 c_1560,c_1559,c_514,c_70,c_46,c_45,c_42,c_23,c_22]) ).
% 3.32/0.92  
% 3.32/0.92  
% 3.32/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/0.92  
% 3.32/0.92  ------                               Statistics
% 3.32/0.92  
% 3.32/0.92  ------ General
% 3.32/0.92  
% 3.32/0.92  abstr_ref_over_cycles:                  0
% 3.32/0.92  abstr_ref_under_cycles:                 0
% 3.32/0.92  gc_basic_clause_elim:                   0
% 3.32/0.92  forced_gc_time:                         0
% 3.32/0.92  parsing_time:                           0.009
% 3.32/0.92  unif_index_cands_time:                  0.
% 3.32/0.92  unif_index_add_time:                    0.
% 3.32/0.92  orderings_time:                         0.
% 3.32/0.92  out_proof_time:                         0.013
% 3.32/0.92  total_time:                             0.163
% 3.32/0.92  num_of_symbols:                         41
% 3.32/0.92  num_of_terms:                           4672
% 3.32/0.92  
% 3.32/0.92  ------ Preprocessing
% 3.32/0.92  
% 3.32/0.92  num_of_splits:                          0
% 3.32/0.92  num_of_split_atoms:                     0
% 3.32/0.92  num_of_reused_defs:                     0
% 3.32/0.92  num_eq_ax_congr_red:                    20
% 3.32/0.92  num_of_sem_filtered_clauses:            1
% 3.32/0.92  num_of_subtypes:                        0
% 3.32/0.92  monotx_restored_types:                  0
% 3.32/0.92  sat_num_of_epr_types:                   0
% 3.32/0.92  sat_num_of_non_cyclic_types:            0
% 3.32/0.92  sat_guarded_non_collapsed_types:        0
% 3.32/0.92  num_pure_diseq_elim:                    0
% 3.32/0.92  simp_replaced_by:                       0
% 3.32/0.92  res_preprocessed:                       89
% 3.32/0.92  prep_upred:                             0
% 3.32/0.92  prep_unflattend:                        4
% 3.32/0.92  smt_new_axioms:                         0
% 3.32/0.92  pred_elim_cands:                        2
% 3.32/0.92  pred_elim:                              2
% 3.32/0.92  pred_elim_cl:                           4
% 3.32/0.92  pred_elim_cycles:                       4
% 3.32/0.92  merged_defs:                            8
% 3.32/0.92  merged_defs_ncl:                        0
% 3.32/0.92  bin_hyper_res:                          8
% 3.32/0.92  prep_cycles:                            4
% 3.32/0.92  pred_elim_time:                         0.001
% 3.32/0.92  splitting_time:                         0.
% 3.32/0.92  sem_filter_time:                        0.
% 3.32/0.92  monotx_time:                            0.
% 3.32/0.92  subtype_inf_time:                       0.
% 3.32/0.92  
% 3.32/0.92  ------ Problem properties
% 3.32/0.92  
% 3.32/0.92  clauses:                                18
% 3.32/0.92  conjectures:                            2
% 3.32/0.92  epr:                                    4
% 3.32/0.92  horn:                                   13
% 3.32/0.92  ground:                                 4
% 3.32/0.92  unary:                                  4
% 3.32/0.92  binary:                                 5
% 3.32/0.92  lits:                                   45
% 3.32/0.92  lits_eq:                                13
% 3.32/0.92  fd_pure:                                0
% 3.32/0.92  fd_pseudo:                              0
% 3.32/0.92  fd_cond:                                0
% 3.32/0.92  fd_pseudo_cond:                         7
% 3.32/0.92  ac_symbols:                             0
% 3.32/0.92  
% 3.32/0.92  ------ Propositional Solver
% 3.32/0.92  
% 3.32/0.92  prop_solver_calls:                      28
% 3.32/0.92  prop_fast_solver_calls:                 509
% 3.32/0.92  smt_solver_calls:                       0
% 3.32/0.92  smt_fast_solver_calls:                  0
% 3.32/0.92  prop_num_of_clauses:                    1364
% 3.32/0.92  prop_preprocess_simplified:             5371
% 3.32/0.92  prop_fo_subsumed:                       5
% 3.32/0.92  prop_solver_time:                       0.
% 3.32/0.92  smt_solver_time:                        0.
% 3.32/0.92  smt_fast_solver_time:                   0.
% 3.32/0.92  prop_fast_solver_time:                  0.
% 3.32/0.92  prop_unsat_core_time:                   0.
% 3.32/0.92  
% 3.32/0.92  ------ QBF
% 3.32/0.92  
% 3.32/0.92  qbf_q_res:                              0
% 3.32/0.92  qbf_num_tautologies:                    0
% 3.32/0.92  qbf_prep_cycles:                        0
% 3.32/0.92  
% 3.32/0.92  ------ BMC1
% 3.32/0.92  
% 3.32/0.92  bmc1_current_bound:                     -1
% 3.32/0.92  bmc1_last_solved_bound:                 -1
% 3.32/0.92  bmc1_unsat_core_size:                   -1
% 3.32/0.92  bmc1_unsat_core_parents_size:           -1
% 3.32/0.92  bmc1_merge_next_fun:                    0
% 3.32/0.92  bmc1_unsat_core_clauses_time:           0.
% 3.32/0.92  
% 3.32/0.92  ------ Instantiation
% 3.32/0.92  
% 3.32/0.92  inst_num_of_clauses:                    388
% 3.32/0.92  inst_num_in_passive:                    288
% 3.32/0.92  inst_num_in_active:                     90
% 3.32/0.92  inst_num_in_unprocessed:                9
% 3.32/0.92  inst_num_of_loops:                      103
% 3.32/0.92  inst_num_of_learning_restarts:          0
% 3.32/0.92  inst_num_moves_active_passive:          8
% 3.32/0.92  inst_lit_activity:                      0
% 3.32/0.92  inst_lit_activity_moves:                0
% 3.32/0.92  inst_num_tautologies:                   0
% 3.32/0.92  inst_num_prop_implied:                  0
% 3.32/0.92  inst_num_existing_simplified:           0
% 3.32/0.92  inst_num_eq_res_simplified:             0
% 3.32/0.92  inst_num_child_elim:                    0
% 3.32/0.92  inst_num_of_dismatching_blockings:      48
% 3.32/0.92  inst_num_of_non_proper_insts:           192
% 3.32/0.92  inst_num_of_duplicates:                 0
% 3.32/0.92  inst_inst_num_from_inst_to_res:         0
% 3.32/0.92  inst_dismatching_checking_time:         0.
% 3.32/0.92  
% 3.32/0.92  ------ Resolution
% 3.32/0.92  
% 3.32/0.92  res_num_of_clauses:                     0
% 3.32/0.92  res_num_in_passive:                     0
% 3.32/0.92  res_num_in_active:                      0
% 3.32/0.92  res_num_of_loops:                       93
% 3.32/0.92  res_forward_subset_subsumed:            0
% 3.32/0.92  res_backward_subset_subsumed:           0
% 3.32/0.92  res_forward_subsumed:                   0
% 3.32/0.92  res_backward_subsumed:                  0
% 3.32/0.92  res_forward_subsumption_resolution:     0
% 3.32/0.92  res_backward_subsumption_resolution:    0
% 3.32/0.92  res_clause_to_clause_subsumption:       193
% 3.32/0.92  res_orphan_elimination:                 0
% 3.32/0.92  res_tautology_del:                      24
% 3.32/0.92  res_num_eq_res_simplified:              0
% 3.32/0.92  res_num_sel_changes:                    0
% 3.32/0.92  res_moves_from_active_to_pass:          0
% 3.32/0.92  
% 3.32/0.92  ------ Superposition
% 3.32/0.92  
% 3.32/0.92  sup_time_total:                         0.
% 3.32/0.92  sup_time_generating:                    0.
% 3.32/0.92  sup_time_sim_full:                      0.
% 3.32/0.92  sup_time_sim_immed:                     0.
% 3.32/0.92  
% 3.32/0.92  sup_num_of_clauses:                     43
% 3.32/0.92  sup_num_in_active:                      20
% 3.32/0.92  sup_num_in_passive:                     23
% 3.32/0.92  sup_num_of_loops:                       20
% 3.32/0.92  sup_fw_superposition:                   22
% 3.32/0.92  sup_bw_superposition:                   7
% 3.32/0.92  sup_immediate_simplified:               0
% 3.32/0.92  sup_given_eliminated:                   0
% 3.32/0.92  comparisons_done:                       0
% 3.32/0.92  comparisons_avoided:                    0
% 3.32/0.92  
% 3.32/0.92  ------ Simplifications
% 3.32/0.92  
% 3.32/0.92  
% 3.32/0.92  sim_fw_subset_subsumed:                 0
% 3.32/0.92  sim_bw_subset_subsumed:                 0
% 3.32/0.92  sim_fw_subsumed:                        0
% 3.32/0.92  sim_bw_subsumed:                        0
% 3.32/0.92  sim_fw_subsumption_res:                 0
% 3.32/0.92  sim_bw_subsumption_res:                 0
% 3.32/0.92  sim_tautology_del:                      2
% 3.32/0.92  sim_eq_tautology_del:                   0
% 3.32/0.92  sim_eq_res_simp:                        0
% 3.32/0.92  sim_fw_demodulated:                     0
% 3.32/0.92  sim_bw_demodulated:                     0
% 3.32/0.92  sim_light_normalised:                   0
% 3.32/0.92  sim_joinable_taut:                      0
% 3.32/0.92  sim_joinable_simp:                      0
% 3.32/0.92  sim_ac_normalised:                      0
% 3.32/0.92  sim_smt_subsumption:                    0
% 3.32/0.92  
%------------------------------------------------------------------------------
