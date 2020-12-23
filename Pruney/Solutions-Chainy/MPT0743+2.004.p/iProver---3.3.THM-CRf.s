%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:37 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  163 (1664 expanded)
%              Number of clauses        :   97 ( 405 expanded)
%              Number of leaves         :   18 ( 398 expanded)
%              Depth                    :   20
%              Number of atoms          :  519 (5501 expanded)
%              Number of equality atoms :  192 (1158 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(k1_ordinal1(X0),sK2)
          | ~ r2_hidden(X0,sK2) )
        & ( r1_ordinal1(k1_ordinal1(X0),sK2)
          | r2_hidden(X0,sK2) )
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK1),X1)
            | ~ r2_hidden(sK1,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK1),X1)
            | r2_hidden(sK1,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
      | ~ r2_hidden(sK1,sK2) )
    & ( r1_ordinal1(k1_ordinal1(sK1),sK2)
      | r2_hidden(sK1,sK2) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).

fof(f67,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f70,plain,(
    ! [X0] : k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f75,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f64,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f66,plain,
    ( r1_ordinal1(k1_ordinal1(sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f66,f70])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f82,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f71])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

cnf(c_16,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4720,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4724,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5196,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4720,c_4724])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4728,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6863,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_4728])).

cnf(c_10710,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_6863])).

cnf(c_19,negated_conjecture,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4717,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5120,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4720,c_4717])).

cnf(c_22,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_35,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_5229,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5120,c_23,c_24,c_35])).

cnf(c_20,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4716,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5197,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4716,c_4724])).

cnf(c_5283,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5197,c_23,c_24,c_35])).

cnf(c_5289,plain,
    ( k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = sK2
    | r1_tarski(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5283,c_4728])).

cnf(c_6866,plain,
    ( k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = sK2
    | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_5289])).

cnf(c_0,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_31,plain,
    ( ~ r2_hidden(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_30,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_32,plain,
    ( r2_hidden(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_38,plain,
    ( r1_ordinal1(sK1,sK1) = iProver_top
    | r2_hidden(sK1,sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_40,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | r2_hidden(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_44,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3749,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3750,plain,
    ( r1_tarski(sK2,sK1) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3749])).

cnf(c_4935,plain,
    ( ~ r1_ordinal1(sK2,X0)
    | r1_tarski(sK2,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4936,plain,
    ( r1_ordinal1(sK2,X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4935])).

cnf(c_4938,plain,
    ( r1_ordinal1(sK2,sK1) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top
    | v3_ordinal1(sK2) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4936])).

cnf(c_4721,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5237,plain,
    ( sK2 = sK1
    | r2_hidden(sK2,sK1) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5229,c_4721])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4730,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4718,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5290,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5283,c_4718])).

cnf(c_5312,plain,
    ( r2_hidden(sK2,sK1) != iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4730,c_5290])).

cnf(c_3746,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3747,plain,
    ( r2_hidden(sK2,sK1) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3746])).

cnf(c_5334,plain,
    ( r2_hidden(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5312,c_3747])).

cnf(c_484,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6769,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_6770,plain,
    ( X0 != X1
    | sK2 != X2
    | r1_ordinal1(X2,X1) != iProver_top
    | r1_ordinal1(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6769])).

cnf(c_6772,plain,
    ( sK2 != sK1
    | sK1 != sK1
    | r1_ordinal1(sK2,sK1) = iProver_top
    | r1_ordinal1(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6770])).

cnf(c_6986,plain,
    ( r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top
    | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6866,c_23,c_24,c_31,c_32,c_35,c_38,c_40,c_44,c_3747,c_3750,c_4938,c_5237,c_5312,c_6772])).

cnf(c_6987,plain,
    ( k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = sK2
    | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_6986])).

cnf(c_4732,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6992,plain,
    ( k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = sK2
    | r2_hidden(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6987,c_4732])).

cnf(c_34,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_37,plain,
    ( r1_ordinal1(sK1,sK1)
    | r2_hidden(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1894,plain,
    ( ~ r1_tarski(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)),X0)
    | ~ r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1896,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1)
    | ~ r2_hidden(sK1,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_3265,plain,
    ( ~ r1_ordinal1(X0,sK1)
    | r1_tarski(X0,sK1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3291,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1)
    | r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_3265])).

cnf(c_5539,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_ordinal1(sK2,X2)
    | X1 != X2
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_6306,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1)
    | ~ r1_ordinal1(sK2,X0)
    | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) != sK2
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_5539])).

cnf(c_6308,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1)
    | ~ r1_ordinal1(sK2,sK1)
    | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_6306])).

cnf(c_6771,plain,
    ( r1_ordinal1(sK2,sK1)
    | ~ r1_ordinal1(sK1,sK1)
    | sK2 != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_6769])).

cnf(c_7039,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6992,c_23,c_24,c_31,c_32,c_38,c_40,c_44,c_3747,c_3750,c_4938,c_5237,c_5290,c_5312,c_6772])).

cnf(c_7046,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5229,c_7039])).

cnf(c_16667,plain,
    ( sK2 = sK1
    | r2_hidden(sK2,sK1) = iProver_top
    | v3_ordinal1(sK2) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10710,c_7046])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6157,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | X0 != k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_7862,plain,
    ( r2_hidden(k2_xboole_0(sK1,X0),X1)
    | ~ r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | X1 != sK2
    | k2_xboole_0(sK1,X0) != k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_6157])).

cnf(c_15168,plain,
    ( r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),X0)
    | ~ r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | X0 != sK2
    | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) != k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_7862])).

cnf(c_15169,plain,
    ( X0 != sK2
    | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) != k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),X0) = iProver_top
    | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15168])).

cnf(c_15171,plain,
    ( k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) != k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 != sK2
    | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) != iProver_top
    | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_15169])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8844,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5831,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),X0)
    | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6573,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_5831])).

cnf(c_5336,plain,
    ( ~ r2_hidden(sK2,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5334])).

cnf(c_4937,plain,
    ( ~ r1_ordinal1(sK2,sK1)
    | r1_tarski(sK2,sK1)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_4935])).

cnf(c_4868,plain,
    ( r1_ordinal1(X0,sK2)
    | r2_hidden(sK2,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4870,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK2,sK1)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_4868])).

cnf(c_4244,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4246,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK1,sK2)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_4244])).

cnf(c_3255,plain,
    ( ~ r1_ordinal1(X0,sK2)
    | r1_tarski(X0,sK2)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3257,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_3255])).

cnf(c_997,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)))
    | ~ r2_hidden(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_998,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_1000,plain,
    ( r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1) != iProver_top
    | r2_hidden(sK1,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_43,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_45,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16667,c_15171,c_8844,c_6987,c_6771,c_6573,c_6308,c_5336,c_5334,c_4937,c_4870,c_4246,c_3291,c_3257,c_1896,c_1000,c_45,c_44,c_40,c_37,c_34,c_31,c_24,c_21,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:28:37 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 7.81/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.48  
% 7.81/1.48  ------  iProver source info
% 7.81/1.48  
% 7.81/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.48  git: non_committed_changes: false
% 7.81/1.48  git: last_make_outside_of_git: false
% 7.81/1.48  
% 7.81/1.48  ------ 
% 7.81/1.48  ------ Parsing...
% 7.81/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  ------ Proving...
% 7.81/1.48  ------ Problem Properties 
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  clauses                                 22
% 7.81/1.48  conjectures                             6
% 7.81/1.48  EPR                                     10
% 7.81/1.48  Horn                                    16
% 7.81/1.48  unary                                   4
% 7.81/1.48  binary                                  8
% 7.81/1.48  lits                                    55
% 7.81/1.48  lits eq                                 5
% 7.81/1.48  fd_pure                                 0
% 7.81/1.48  fd_pseudo                               0
% 7.81/1.48  fd_cond                                 0
% 7.81/1.48  fd_pseudo_cond                          5
% 7.81/1.48  AC symbols                              0
% 7.81/1.48  
% 7.81/1.48  ------ Input Options Time Limit: Unbounded
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing...
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 7.81/1.48  Current options:
% 7.81/1.48  ------ 
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing...
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing...
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing...
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  % SZS status Theorem for theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  fof(f11,axiom,(
% 7.81/1.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f21,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.81/1.48    inference(ennf_transformation,[],[f11])).
% 7.81/1.48  
% 7.81/1.48  fof(f22,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.81/1.48    inference(flattening,[],[f21])).
% 7.81/1.48  
% 7.81/1.48  fof(f61,plain,(
% 7.81/1.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f22])).
% 7.81/1.48  
% 7.81/1.48  fof(f9,axiom,(
% 7.81/1.48    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f19,plain,(
% 7.81/1.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 7.81/1.48    inference(ennf_transformation,[],[f9])).
% 7.81/1.48  
% 7.81/1.48  fof(f20,plain,(
% 7.81/1.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 7.81/1.48    inference(flattening,[],[f19])).
% 7.81/1.48  
% 7.81/1.48  fof(f33,plain,(
% 7.81/1.48    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 7.81/1.48    inference(nnf_transformation,[],[f20])).
% 7.81/1.48  
% 7.81/1.48  fof(f56,plain,(
% 7.81/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f33])).
% 7.81/1.48  
% 7.81/1.48  fof(f3,axiom,(
% 7.81/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f31,plain,(
% 7.81/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.81/1.48    inference(nnf_transformation,[],[f3])).
% 7.81/1.48  
% 7.81/1.48  fof(f32,plain,(
% 7.81/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.81/1.48    inference(flattening,[],[f31])).
% 7.81/1.48  
% 7.81/1.48  fof(f50,plain,(
% 7.81/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f32])).
% 7.81/1.48  
% 7.81/1.48  fof(f14,conjecture,(
% 7.81/1.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f15,negated_conjecture,(
% 7.81/1.48    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 7.81/1.48    inference(negated_conjecture,[],[f14])).
% 7.81/1.48  
% 7.81/1.48  fof(f25,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 7.81/1.48    inference(ennf_transformation,[],[f15])).
% 7.81/1.48  
% 7.81/1.48  fof(f36,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 7.81/1.48    inference(nnf_transformation,[],[f25])).
% 7.81/1.48  
% 7.81/1.48  fof(f37,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 7.81/1.48    inference(flattening,[],[f36])).
% 7.81/1.48  
% 7.81/1.48  fof(f39,plain,(
% 7.81/1.48    ( ! [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(X0),sK2) | ~r2_hidden(X0,sK2)) & (r1_ordinal1(k1_ordinal1(X0),sK2) | r2_hidden(X0,sK2)) & v3_ordinal1(sK2))) )),
% 7.81/1.48    introduced(choice_axiom,[])).
% 7.81/1.48  
% 7.81/1.48  fof(f38,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK1),X1) | ~r2_hidden(sK1,X1)) & (r1_ordinal1(k1_ordinal1(sK1),X1) | r2_hidden(sK1,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 7.81/1.48    introduced(choice_axiom,[])).
% 7.81/1.48  
% 7.81/1.48  fof(f40,plain,(
% 7.81/1.48    ((~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)) & (r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 7.81/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).
% 7.81/1.48  
% 7.81/1.48  fof(f67,plain,(
% 7.81/1.48    ~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 7.81/1.48    inference(cnf_transformation,[],[f40])).
% 7.81/1.48  
% 7.81/1.48  fof(f8,axiom,(
% 7.81/1.48    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f55,plain,(
% 7.81/1.48    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f8])).
% 7.81/1.48  
% 7.81/1.48  fof(f4,axiom,(
% 7.81/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f51,plain,(
% 7.81/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f4])).
% 7.81/1.48  
% 7.81/1.48  fof(f5,axiom,(
% 7.81/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f52,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f5])).
% 7.81/1.48  
% 7.81/1.48  fof(f6,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f53,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f6])).
% 7.81/1.48  
% 7.81/1.48  fof(f68,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f52,f53])).
% 7.81/1.48  
% 7.81/1.48  fof(f69,plain,(
% 7.81/1.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f51,f68])).
% 7.81/1.48  
% 7.81/1.48  fof(f70,plain,(
% 7.81/1.48    ( ! [X0] : (k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) = k1_ordinal1(X0)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f55,f69])).
% 7.81/1.48  
% 7.81/1.48  fof(f75,plain,(
% 7.81/1.48    ~r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | ~r2_hidden(sK1,sK2)),
% 7.81/1.48    inference(definition_unfolding,[],[f67,f70])).
% 7.81/1.48  
% 7.81/1.48  fof(f64,plain,(
% 7.81/1.48    v3_ordinal1(sK1)),
% 7.81/1.48    inference(cnf_transformation,[],[f40])).
% 7.81/1.48  
% 7.81/1.48  fof(f65,plain,(
% 7.81/1.48    v3_ordinal1(sK2)),
% 7.81/1.48    inference(cnf_transformation,[],[f40])).
% 7.81/1.48  
% 7.81/1.48  fof(f12,axiom,(
% 7.81/1.48    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f23,plain,(
% 7.81/1.48    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 7.81/1.48    inference(ennf_transformation,[],[f12])).
% 7.81/1.48  
% 7.81/1.48  fof(f62,plain,(
% 7.81/1.48    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f23])).
% 7.81/1.48  
% 7.81/1.48  fof(f74,plain,(
% 7.81/1.48    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) | ~v3_ordinal1(X0)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f62,f70])).
% 7.81/1.48  
% 7.81/1.48  fof(f66,plain,(
% 7.81/1.48    r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)),
% 7.81/1.48    inference(cnf_transformation,[],[f40])).
% 7.81/1.48  
% 7.81/1.48  fof(f76,plain,(
% 7.81/1.48    r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | r2_hidden(sK1,sK2)),
% 7.81/1.48    inference(definition_unfolding,[],[f66,f70])).
% 7.81/1.48  
% 7.81/1.48  fof(f1,axiom,(
% 7.81/1.48    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f16,plain,(
% 7.81/1.48    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 7.81/1.48    inference(ennf_transformation,[],[f1])).
% 7.81/1.48  
% 7.81/1.48  fof(f41,plain,(
% 7.81/1.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f16])).
% 7.81/1.48  
% 7.81/1.48  fof(f10,axiom,(
% 7.81/1.48    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f34,plain,(
% 7.81/1.48    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 7.81/1.48    inference(nnf_transformation,[],[f10])).
% 7.81/1.48  
% 7.81/1.48  fof(f35,plain,(
% 7.81/1.48    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 7.81/1.48    inference(flattening,[],[f34])).
% 7.81/1.48  
% 7.81/1.48  fof(f58,plain,(
% 7.81/1.48    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f35])).
% 7.81/1.48  
% 7.81/1.48  fof(f73,plain,(
% 7.81/1.48    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))) )),
% 7.81/1.48    inference(definition_unfolding,[],[f58,f70])).
% 7.81/1.48  
% 7.81/1.48  fof(f60,plain,(
% 7.81/1.48    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 7.81/1.48    inference(cnf_transformation,[],[f35])).
% 7.81/1.48  
% 7.81/1.48  fof(f71,plain,(
% 7.81/1.48    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) | X0 != X1) )),
% 7.81/1.48    inference(definition_unfolding,[],[f60,f70])).
% 7.81/1.48  
% 7.81/1.48  fof(f82,plain,(
% 7.81/1.48    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))) )),
% 7.81/1.48    inference(equality_resolution,[],[f71])).
% 7.81/1.48  
% 7.81/1.48  fof(f13,axiom,(
% 7.81/1.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f24,plain,(
% 7.81/1.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.81/1.48    inference(ennf_transformation,[],[f13])).
% 7.81/1.48  
% 7.81/1.48  fof(f63,plain,(
% 7.81/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f24])).
% 7.81/1.48  
% 7.81/1.48  fof(f2,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.81/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f26,plain,(
% 7.81/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.81/1.48    inference(nnf_transformation,[],[f2])).
% 7.81/1.48  
% 7.81/1.48  fof(f27,plain,(
% 7.81/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.81/1.48    inference(flattening,[],[f26])).
% 7.81/1.48  
% 7.81/1.48  fof(f28,plain,(
% 7.81/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.81/1.48    inference(rectify,[],[f27])).
% 7.81/1.48  
% 7.81/1.48  fof(f29,plain,(
% 7.81/1.48    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.81/1.48    introduced(choice_axiom,[])).
% 7.81/1.48  
% 7.81/1.48  fof(f30,plain,(
% 7.81/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.81/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 7.81/1.48  
% 7.81/1.48  fof(f43,plain,(
% 7.81/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 7.81/1.48    inference(cnf_transformation,[],[f30])).
% 7.81/1.48  
% 7.81/1.48  fof(f78,plain,(
% 7.81/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 7.81/1.48    inference(equality_resolution,[],[f43])).
% 7.81/1.48  
% 7.81/1.48  fof(f49,plain,(
% 7.81/1.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.81/1.48    inference(cnf_transformation,[],[f32])).
% 7.81/1.48  
% 7.81/1.48  fof(f80,plain,(
% 7.81/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.81/1.48    inference(equality_resolution,[],[f49])).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16,plain,
% 7.81/1.48      ( r1_ordinal1(X0,X1)
% 7.81/1.48      | r2_hidden(X1,X0)
% 7.81/1.48      | ~ v3_ordinal1(X1)
% 7.81/1.48      | ~ v3_ordinal1(X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4720,plain,
% 7.81/1.48      ( r1_ordinal1(X0,X1) = iProver_top
% 7.81/1.48      | r2_hidden(X1,X0) = iProver_top
% 7.81/1.48      | v3_ordinal1(X0) != iProver_top
% 7.81/1.48      | v3_ordinal1(X1) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_12,plain,
% 7.81/1.48      ( ~ r1_ordinal1(X0,X1)
% 7.81/1.48      | r1_tarski(X0,X1)
% 7.81/1.48      | ~ v3_ordinal1(X1)
% 7.81/1.48      | ~ v3_ordinal1(X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4724,plain,
% 7.81/1.48      ( r1_ordinal1(X0,X1) != iProver_top
% 7.81/1.48      | r1_tarski(X0,X1) = iProver_top
% 7.81/1.48      | v3_ordinal1(X0) != iProver_top
% 7.81/1.48      | v3_ordinal1(X1) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5196,plain,
% 7.81/1.48      ( r1_tarski(X0,X1) = iProver_top
% 7.81/1.48      | r2_hidden(X1,X0) = iProver_top
% 7.81/1.48      | v3_ordinal1(X1) != iProver_top
% 7.81/1.48      | v3_ordinal1(X0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4720,c_4724]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_7,plain,
% 7.81/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.81/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4728,plain,
% 7.81/1.48      ( X0 = X1
% 7.81/1.48      | r1_tarski(X1,X0) != iProver_top
% 7.81/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6863,plain,
% 7.81/1.48      ( X0 = X1
% 7.81/1.48      | r1_tarski(X1,X0) != iProver_top
% 7.81/1.48      | r2_hidden(X1,X0) = iProver_top
% 7.81/1.48      | v3_ordinal1(X1) != iProver_top
% 7.81/1.48      | v3_ordinal1(X0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5196,c_4728]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_10710,plain,
% 7.81/1.48      ( X0 = X1
% 7.81/1.48      | r2_hidden(X0,X1) = iProver_top
% 7.81/1.48      | r2_hidden(X1,X0) = iProver_top
% 7.81/1.48      | v3_ordinal1(X1) != iProver_top
% 7.81/1.48      | v3_ordinal1(X0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5196,c_6863]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_19,negated_conjecture,
% 7.81/1.48      ( ~ r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
% 7.81/1.48      | ~ r2_hidden(sK1,sK2) ),
% 7.81/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4717,plain,
% 7.81/1.48      ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) != iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5120,plain,
% 7.81/1.48      ( r2_hidden(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) = iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) != iProver_top
% 7.81/1.48      | v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top
% 7.81/1.48      | v3_ordinal1(sK2) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4720,c_4717]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_22,negated_conjecture,
% 7.81/1.48      ( v3_ordinal1(sK1) ),
% 7.81/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_23,plain,
% 7.81/1.48      ( v3_ordinal1(sK1) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_21,negated_conjecture,
% 7.81/1.48      ( v3_ordinal1(sK2) ),
% 7.81/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_24,plain,
% 7.81/1.48      ( v3_ordinal1(sK2) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_17,plain,
% 7.81/1.48      ( ~ v3_ordinal1(X0)
% 7.81/1.48      | v3_ordinal1(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
% 7.81/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_33,plain,
% 7.81/1.48      ( v3_ordinal1(X0) != iProver_top
% 7.81/1.48      | v3_ordinal1(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_35,plain,
% 7.81/1.48      ( v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) = iProver_top
% 7.81/1.48      | v3_ordinal1(sK1) != iProver_top ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_33]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5229,plain,
% 7.81/1.48      ( r2_hidden(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) = iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) != iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_5120,c_23,c_24,c_35]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_20,negated_conjecture,
% 7.81/1.48      ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
% 7.81/1.48      | r2_hidden(sK1,sK2) ),
% 7.81/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4716,plain,
% 7.81/1.48      ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5197,plain,
% 7.81/1.48      ( r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) = iProver_top
% 7.81/1.48      | v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top
% 7.81/1.48      | v3_ordinal1(sK2) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4716,c_4724]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5283,plain,
% 7.81/1.48      ( r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) = iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_5197,c_23,c_24,c_35]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5289,plain,
% 7.81/1.48      ( k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = sK2
% 7.81/1.48      | r1_tarski(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) = iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5283,c_4728]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6866,plain,
% 7.81/1.48      ( k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = sK2
% 7.81/1.48      | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) = iProver_top
% 7.81/1.48      | v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top
% 7.81/1.48      | v3_ordinal1(sK2) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5196,c_5289]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_0,negated_conjecture,
% 7.81/1.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_31,plain,
% 7.81/1.48      ( ~ r2_hidden(sK1,sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_30,plain,
% 7.81/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.81/1.48      | r2_hidden(X1,X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_32,plain,
% 7.81/1.48      ( r2_hidden(sK1,sK1) != iProver_top ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_30]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_36,plain,
% 7.81/1.48      ( r1_ordinal1(X0,X1) = iProver_top
% 7.81/1.48      | r2_hidden(X1,X0) = iProver_top
% 7.81/1.48      | v3_ordinal1(X0) != iProver_top
% 7.81/1.48      | v3_ordinal1(X1) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_38,plain,
% 7.81/1.48      ( r1_ordinal1(sK1,sK1) = iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK1) = iProver_top
% 7.81/1.48      | v3_ordinal1(sK1) != iProver_top ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_36]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15,plain,
% 7.81/1.48      ( r2_hidden(X0,X1)
% 7.81/1.48      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
% 7.81/1.48      | X0 = X1 ),
% 7.81/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_40,plain,
% 7.81/1.48      ( ~ r2_hidden(sK1,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
% 7.81/1.48      | r2_hidden(sK1,sK1)
% 7.81/1.48      | sK1 = sK1 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_13,plain,
% 7.81/1.48      ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
% 7.81/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_44,plain,
% 7.81/1.48      ( r2_hidden(sK1,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_18,negated_conjecture,
% 7.81/1.48      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3749,plain,
% 7.81/1.48      ( ~ r1_tarski(sK2,sK1) | ~ r2_hidden(sK1,sK2) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3750,plain,
% 7.81/1.48      ( r1_tarski(sK2,sK1) != iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_3749]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4935,plain,
% 7.81/1.48      ( ~ r1_ordinal1(sK2,X0)
% 7.81/1.48      | r1_tarski(sK2,X0)
% 7.81/1.48      | ~ v3_ordinal1(X0)
% 7.81/1.48      | ~ v3_ordinal1(sK2) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4936,plain,
% 7.81/1.48      ( r1_ordinal1(sK2,X0) != iProver_top
% 7.81/1.48      | r1_tarski(sK2,X0) = iProver_top
% 7.81/1.48      | v3_ordinal1(X0) != iProver_top
% 7.81/1.48      | v3_ordinal1(sK2) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_4935]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4938,plain,
% 7.81/1.48      ( r1_ordinal1(sK2,sK1) != iProver_top
% 7.81/1.48      | r1_tarski(sK2,sK1) = iProver_top
% 7.81/1.48      | v3_ordinal1(sK2) != iProver_top
% 7.81/1.48      | v3_ordinal1(sK1) != iProver_top ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_4936]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4721,plain,
% 7.81/1.48      ( X0 = X1
% 7.81/1.48      | r2_hidden(X0,X1) = iProver_top
% 7.81/1.48      | r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5237,plain,
% 7.81/1.48      ( sK2 = sK1
% 7.81/1.48      | r2_hidden(sK2,sK1) = iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5229,c_4721]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5,plain,
% 7.81/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 7.81/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4730,plain,
% 7.81/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.81/1.48      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4718,plain,
% 7.81/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.81/1.48      | r2_hidden(X1,X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5290,plain,
% 7.81/1.48      ( r2_hidden(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) = iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5283,c_4718]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5312,plain,
% 7.81/1.48      ( r2_hidden(sK2,sK1) != iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) = iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4730,c_5290]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3746,plain,
% 7.81/1.48      ( ~ r2_hidden(sK2,sK1) | ~ r2_hidden(sK1,sK2) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3747,plain,
% 7.81/1.48      ( r2_hidden(sK2,sK1) != iProver_top
% 7.81/1.48      | r2_hidden(sK1,sK2) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_3746]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5334,plain,
% 7.81/1.48      ( r2_hidden(sK2,sK1) != iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_5312,c_3747]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_484,plain,
% 7.81/1.48      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.81/1.48      theory(equality) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6769,plain,
% 7.81/1.48      ( ~ r1_ordinal1(X0,X1)
% 7.81/1.48      | r1_ordinal1(sK2,X2)
% 7.81/1.48      | X2 != X1
% 7.81/1.48      | sK2 != X0 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_484]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6770,plain,
% 7.81/1.48      ( X0 != X1
% 7.81/1.48      | sK2 != X2
% 7.81/1.48      | r1_ordinal1(X2,X1) != iProver_top
% 7.81/1.48      | r1_ordinal1(sK2,X0) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_6769]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6772,plain,
% 7.81/1.48      ( sK2 != sK1
% 7.81/1.48      | sK1 != sK1
% 7.81/1.48      | r1_ordinal1(sK2,sK1) = iProver_top
% 7.81/1.48      | r1_ordinal1(sK1,sK1) != iProver_top ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_6770]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6986,plain,
% 7.81/1.48      ( r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top
% 7.81/1.48      | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = sK2 ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_6866,c_23,c_24,c_31,c_32,c_35,c_38,c_40,c_44,c_3747,
% 7.81/1.48                 c_3750,c_4938,c_5237,c_5312,c_6772]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6987,plain,
% 7.81/1.48      ( k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = sK2
% 7.81/1.48      | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) = iProver_top ),
% 7.81/1.48      inference(renaming,[status(thm)],[c_6986]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4732,plain,
% 7.81/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.81/1.48      | r2_hidden(X1,X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6992,plain,
% 7.81/1.48      ( k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = sK2
% 7.81/1.48      | r2_hidden(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_6987,c_4732]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_34,plain,
% 7.81/1.48      ( v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
% 7.81/1.48      | ~ v3_ordinal1(sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_37,plain,
% 7.81/1.48      ( r1_ordinal1(sK1,sK1) | r2_hidden(sK1,sK1) | ~ v3_ordinal1(sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_1894,plain,
% 7.81/1.48      ( ~ r1_tarski(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)),X0)
% 7.81/1.48      | ~ r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_1896,plain,
% 7.81/1.48      ( ~ r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1)
% 7.81/1.48      | ~ r2_hidden(sK1,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_1894]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3265,plain,
% 7.81/1.48      ( ~ r1_ordinal1(X0,sK1)
% 7.81/1.48      | r1_tarski(X0,sK1)
% 7.81/1.48      | ~ v3_ordinal1(X0)
% 7.81/1.48      | ~ v3_ordinal1(sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3291,plain,
% 7.81/1.48      ( ~ r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1)
% 7.81/1.48      | r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1)
% 7.81/1.48      | ~ v3_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
% 7.81/1.48      | ~ v3_ordinal1(sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3265]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5539,plain,
% 7.81/1.48      ( r1_ordinal1(X0,X1)
% 7.81/1.48      | ~ r1_ordinal1(sK2,X2)
% 7.81/1.48      | X1 != X2
% 7.81/1.48      | X0 != sK2 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_484]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6306,plain,
% 7.81/1.48      ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1)
% 7.81/1.48      | ~ r1_ordinal1(sK2,X0)
% 7.81/1.48      | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) != sK2
% 7.81/1.48      | sK1 != X0 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_5539]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6308,plain,
% 7.81/1.48      ( r1_ordinal1(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1)
% 7.81/1.48      | ~ r1_ordinal1(sK2,sK1)
% 7.81/1.48      | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) != sK2
% 7.81/1.48      | sK1 != sK1 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_6306]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6771,plain,
% 7.81/1.48      ( r1_ordinal1(sK2,sK1)
% 7.81/1.48      | ~ r1_ordinal1(sK1,sK1)
% 7.81/1.48      | sK2 != sK1
% 7.81/1.48      | sK1 != sK1 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_6769]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_7039,plain,
% 7.81/1.48      ( r2_hidden(sK2,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_6992,c_23,c_24,c_31,c_32,c_38,c_40,c_44,c_3747,c_3750,
% 7.81/1.48                 c_4938,c_5237,c_5290,c_5312,c_6772]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_7046,plain,
% 7.81/1.48      ( r2_hidden(sK1,sK2) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_5229,c_7039]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16667,plain,
% 7.81/1.48      ( sK2 = sK1
% 7.81/1.48      | r2_hidden(sK2,sK1) = iProver_top
% 7.81/1.48      | v3_ordinal1(sK2) != iProver_top
% 7.81/1.48      | v3_ordinal1(sK1) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_10710,c_7046]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_482,plain,
% 7.81/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.81/1.48      theory(equality) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6157,plain,
% 7.81/1.48      ( r2_hidden(X0,X1)
% 7.81/1.48      | ~ r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
% 7.81/1.48      | X0 != k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
% 7.81/1.48      | X1 != sK2 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_482]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_7862,plain,
% 7.81/1.48      ( r2_hidden(k2_xboole_0(sK1,X0),X1)
% 7.81/1.48      | ~ r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
% 7.81/1.48      | X1 != sK2
% 7.81/1.48      | k2_xboole_0(sK1,X0) != k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_6157]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15168,plain,
% 7.81/1.48      ( r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),X0)
% 7.81/1.48      | ~ r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
% 7.81/1.48      | X0 != sK2
% 7.81/1.48      | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) != k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_7862]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15169,plain,
% 7.81/1.48      ( X0 != sK2
% 7.81/1.48      | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) != k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
% 7.81/1.48      | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),X0) = iProver_top
% 7.81/1.48      | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_15168]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15171,plain,
% 7.81/1.48      ( k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) != k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
% 7.81/1.48      | sK1 != sK2
% 7.81/1.48      | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) != iProver_top
% 7.81/1.48      | r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1) = iProver_top ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_15169]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8,plain,
% 7.81/1.48      ( r1_tarski(X0,X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8844,plain,
% 7.81/1.48      ( r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5831,plain,
% 7.81/1.48      ( ~ r1_tarski(X0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
% 7.81/1.48      | ~ r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),X0)
% 7.81/1.48      | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = X0 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6573,plain,
% 7.81/1.48      ( ~ r1_tarski(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
% 7.81/1.48      | k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_5831]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5336,plain,
% 7.81/1.48      ( ~ r2_hidden(sK2,sK1) ),
% 7.81/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_5334]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4937,plain,
% 7.81/1.48      ( ~ r1_ordinal1(sK2,sK1)
% 7.81/1.48      | r1_tarski(sK2,sK1)
% 7.81/1.48      | ~ v3_ordinal1(sK2)
% 7.81/1.48      | ~ v3_ordinal1(sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_4935]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4868,plain,
% 7.81/1.48      ( r1_ordinal1(X0,sK2)
% 7.81/1.48      | r2_hidden(sK2,X0)
% 7.81/1.48      | ~ v3_ordinal1(X0)
% 7.81/1.48      | ~ v3_ordinal1(sK2) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4870,plain,
% 7.81/1.48      ( r1_ordinal1(sK1,sK2)
% 7.81/1.48      | r2_hidden(sK2,sK1)
% 7.81/1.48      | ~ v3_ordinal1(sK2)
% 7.81/1.48      | ~ v3_ordinal1(sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_4868]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4244,plain,
% 7.81/1.48      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4246,plain,
% 7.81/1.48      ( ~ r1_tarski(sK2,sK1) | ~ r1_tarski(sK1,sK2) | sK1 = sK2 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_4244]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3255,plain,
% 7.81/1.48      ( ~ r1_ordinal1(X0,sK2)
% 7.81/1.48      | r1_tarski(X0,sK2)
% 7.81/1.48      | ~ v3_ordinal1(X0)
% 7.81/1.48      | ~ v3_ordinal1(sK2) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3257,plain,
% 7.81/1.48      ( ~ r1_ordinal1(sK1,sK2)
% 7.81/1.48      | r1_tarski(sK1,sK2)
% 7.81/1.48      | ~ v3_ordinal1(sK2)
% 7.81/1.48      | ~ v3_ordinal1(sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_3255]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_997,plain,
% 7.81/1.48      ( ~ r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)))
% 7.81/1.48      | ~ r2_hidden(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)),X0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_998,plain,
% 7.81/1.48      ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) != iProver_top
% 7.81/1.48      | r2_hidden(k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)),X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_997]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_1000,plain,
% 7.81/1.48      ( r2_hidden(k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)),sK1) != iProver_top
% 7.81/1.48      | r2_hidden(sK1,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_998]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_43,plain,
% 7.81/1.48      ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_45,plain,
% 7.81/1.48      ( r2_hidden(sK1,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) = iProver_top ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_43]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(contradiction,plain,
% 7.81/1.48      ( $false ),
% 7.81/1.48      inference(minisat,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_16667,c_15171,c_8844,c_6987,c_6771,c_6573,c_6308,
% 7.81/1.48                 c_5336,c_5334,c_4937,c_4870,c_4246,c_3291,c_3257,c_1896,
% 7.81/1.48                 c_1000,c_45,c_44,c_40,c_37,c_34,c_31,c_24,c_21,c_23,
% 7.81/1.48                 c_22]) ).
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  ------                               Statistics
% 7.81/1.48  
% 7.81/1.48  ------ Selected
% 7.81/1.48  
% 7.81/1.48  total_time:                             0.742
% 7.81/1.48  
%------------------------------------------------------------------------------
