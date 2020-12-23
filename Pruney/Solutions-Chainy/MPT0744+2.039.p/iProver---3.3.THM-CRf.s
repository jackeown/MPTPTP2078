%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:53 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 458 expanded)
%              Number of clauses        :   71 ( 121 expanded)
%              Number of leaves         :   16 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  477 (2239 expanded)
%              Number of equality atoms :  134 ( 312 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    inference(nnf_transformation,[],[f1])).

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
    inference(flattening,[],[f23])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ( ~ r1_ordinal1(sK2,sK3)
      | ~ r2_hidden(sK2,k1_ordinal1(sK3)) )
    & ( r1_ordinal1(sK2,sK3)
      | r2_hidden(sK2,k1_ordinal1(sK3)) )
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).

fof(f68,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f72,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
    inference(definition_unfolding,[],[f68,f56])).

fof(f65,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f52])).

fof(f80,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f79])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
    inference(definition_unfolding,[],[f67,f56])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_628,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1398,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_tarski(X2))
    | X0 != X2
    | X1 != k1_tarski(X2) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_2492,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(X1,k1_tarski(X0))
    | X1 != X0
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_8371,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(sK2,k1_tarski(X0))
    | k1_tarski(X0) != k1_tarski(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_2492])).

cnf(c_8373,plain,
    ( ~ r2_hidden(sK3,k1_tarski(sK3))
    | r2_hidden(sK2,k1_tarski(sK3))
    | k1_tarski(sK3) != k1_tarski(sK3)
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_8371])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1154,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_201,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_381,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_201])).

cnf(c_382,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3)))
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_384,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_25,c_24])).

cnf(c_500,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
    inference(prop_impl,[status(thm)],[c_25,c_24,c_382])).

cnf(c_1137,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_1758,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r2_hidden(sK2,k1_tarski(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1137])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_58,plain,
    ( ~ r2_hidden(sK3,k1_tarski(sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_61,plain,
    ( r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_71,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_629,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1417,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,sK3)
    | sK3 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1418,plain,
    ( sK3 != X0
    | sK2 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1417])).

cnf(c_1420,plain,
    ( sK3 != sK3
    | sK2 != sK3
    | r1_tarski(sK3,sK3) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1418])).

cnf(c_1496,plain,
    ( ~ r2_hidden(sK2,k1_tarski(X0))
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1497,plain,
    ( sK2 = X0
    | r2_hidden(sK2,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1496])).

cnf(c_1499,plain,
    ( sK2 = sK3
    | r2_hidden(sK2,k1_tarski(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_5818,plain,
    ( r2_hidden(sK2,k1_tarski(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1758,c_58,c_61,c_71,c_1420,c_1499])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1153,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1759,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_1137])).

cnf(c_27,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_333,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_14])).

cnf(c_334,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_1375,plain,
    ( r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_1376,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_5598,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1759,c_27,c_1376])).

cnf(c_16,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_203,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_395,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_203])).

cnf(c_396,plain,
    ( r1_tarski(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3)))
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_398,plain,
    ( r1_tarski(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_25,c_24])).

cnf(c_502,plain,
    ( r1_tarski(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
    inference(prop_impl,[status(thm)],[c_25,c_24,c_396])).

cnf(c_1136,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1152,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5117,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r2_hidden(sK2,k1_tarski(sK3)) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1152])).

cnf(c_20,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_350,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_20,c_16])).

cnf(c_1895,plain,
    ( r1_tarski(X0,sK2)
    | r2_hidden(sK2,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_1901,plain,
    ( r1_tarski(X0,sK2) = iProver_top
    | r2_hidden(sK2,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1895])).

cnf(c_1903,plain,
    ( r1_tarski(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_1769,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k1_tarski(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1758])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1495,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1501,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1495])).

cnf(c_1503,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_1419,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r1_tarski(sK2,sK3)
    | sK3 != sK3
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_630,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_635,plain,
    ( k1_tarski(sK3) = k1_tarski(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_70,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_26,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8373,c_5818,c_5598,c_5117,c_1903,c_1769,c_1503,c_1419,c_635,c_70,c_61,c_58,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:41:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.14/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/0.94  
% 3.14/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/0.94  
% 3.14/0.94  ------  iProver source info
% 3.14/0.94  
% 3.14/0.94  git: date: 2020-06-30 10:37:57 +0100
% 3.14/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/0.94  git: non_committed_changes: false
% 3.14/0.94  git: last_make_outside_of_git: false
% 3.14/0.94  
% 3.14/0.94  ------ 
% 3.14/0.94  
% 3.14/0.94  ------ Input Options
% 3.14/0.94  
% 3.14/0.94  --out_options                           all
% 3.14/0.94  --tptp_safe_out                         true
% 3.14/0.94  --problem_path                          ""
% 3.14/0.94  --include_path                          ""
% 3.14/0.94  --clausifier                            res/vclausify_rel
% 3.14/0.94  --clausifier_options                    --mode clausify
% 3.14/0.94  --stdin                                 false
% 3.14/0.94  --stats_out                             all
% 3.14/0.94  
% 3.14/0.94  ------ General Options
% 3.14/0.94  
% 3.14/0.94  --fof                                   false
% 3.14/0.94  --time_out_real                         305.
% 3.14/0.94  --time_out_virtual                      -1.
% 3.14/0.94  --symbol_type_check                     false
% 3.14/0.94  --clausify_out                          false
% 3.14/0.94  --sig_cnt_out                           false
% 3.14/0.94  --trig_cnt_out                          false
% 3.14/0.94  --trig_cnt_out_tolerance                1.
% 3.14/0.94  --trig_cnt_out_sk_spl                   false
% 3.14/0.94  --abstr_cl_out                          false
% 3.14/0.94  
% 3.14/0.94  ------ Global Options
% 3.14/0.94  
% 3.14/0.94  --schedule                              default
% 3.14/0.94  --add_important_lit                     false
% 3.14/0.94  --prop_solver_per_cl                    1000
% 3.14/0.94  --min_unsat_core                        false
% 3.14/0.94  --soft_assumptions                      false
% 3.14/0.94  --soft_lemma_size                       3
% 3.14/0.94  --prop_impl_unit_size                   0
% 3.14/0.94  --prop_impl_unit                        []
% 3.14/0.94  --share_sel_clauses                     true
% 3.14/0.94  --reset_solvers                         false
% 3.14/0.94  --bc_imp_inh                            [conj_cone]
% 3.14/0.94  --conj_cone_tolerance                   3.
% 3.14/0.94  --extra_neg_conj                        none
% 3.14/0.94  --large_theory_mode                     true
% 3.14/0.94  --prolific_symb_bound                   200
% 3.14/0.94  --lt_threshold                          2000
% 3.14/0.94  --clause_weak_htbl                      true
% 3.14/0.94  --gc_record_bc_elim                     false
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing Options
% 3.14/0.94  
% 3.14/0.94  --preprocessing_flag                    true
% 3.14/0.94  --time_out_prep_mult                    0.1
% 3.14/0.94  --splitting_mode                        input
% 3.14/0.94  --splitting_grd                         true
% 3.14/0.94  --splitting_cvd                         false
% 3.14/0.94  --splitting_cvd_svl                     false
% 3.14/0.94  --splitting_nvd                         32
% 3.14/0.94  --sub_typing                            true
% 3.14/0.94  --prep_gs_sim                           true
% 3.14/0.94  --prep_unflatten                        true
% 3.14/0.94  --prep_res_sim                          true
% 3.14/0.94  --prep_upred                            true
% 3.14/0.94  --prep_sem_filter                       exhaustive
% 3.14/0.94  --prep_sem_filter_out                   false
% 3.14/0.94  --pred_elim                             true
% 3.14/0.94  --res_sim_input                         true
% 3.14/0.94  --eq_ax_congr_red                       true
% 3.14/0.94  --pure_diseq_elim                       true
% 3.14/0.94  --brand_transform                       false
% 3.14/0.94  --non_eq_to_eq                          false
% 3.14/0.94  --prep_def_merge                        true
% 3.14/0.94  --prep_def_merge_prop_impl              false
% 3.14/0.94  --prep_def_merge_mbd                    true
% 3.14/0.94  --prep_def_merge_tr_red                 false
% 3.14/0.94  --prep_def_merge_tr_cl                  false
% 3.14/0.94  --smt_preprocessing                     true
% 3.14/0.94  --smt_ac_axioms                         fast
% 3.14/0.94  --preprocessed_out                      false
% 3.14/0.94  --preprocessed_stats                    false
% 3.14/0.94  
% 3.14/0.94  ------ Abstraction refinement Options
% 3.14/0.94  
% 3.14/0.94  --abstr_ref                             []
% 3.14/0.94  --abstr_ref_prep                        false
% 3.14/0.94  --abstr_ref_until_sat                   false
% 3.14/0.94  --abstr_ref_sig_restrict                funpre
% 3.14/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.94  --abstr_ref_under                       []
% 3.14/0.94  
% 3.14/0.94  ------ SAT Options
% 3.14/0.94  
% 3.14/0.94  --sat_mode                              false
% 3.14/0.94  --sat_fm_restart_options                ""
% 3.14/0.94  --sat_gr_def                            false
% 3.14/0.94  --sat_epr_types                         true
% 3.14/0.94  --sat_non_cyclic_types                  false
% 3.14/0.94  --sat_finite_models                     false
% 3.14/0.94  --sat_fm_lemmas                         false
% 3.14/0.94  --sat_fm_prep                           false
% 3.14/0.94  --sat_fm_uc_incr                        true
% 3.14/0.94  --sat_out_model                         small
% 3.14/0.94  --sat_out_clauses                       false
% 3.14/0.94  
% 3.14/0.94  ------ QBF Options
% 3.14/0.94  
% 3.14/0.94  --qbf_mode                              false
% 3.14/0.94  --qbf_elim_univ                         false
% 3.14/0.94  --qbf_dom_inst                          none
% 3.14/0.94  --qbf_dom_pre_inst                      false
% 3.14/0.94  --qbf_sk_in                             false
% 3.14/0.94  --qbf_pred_elim                         true
% 3.14/0.94  --qbf_split                             512
% 3.14/0.94  
% 3.14/0.94  ------ BMC1 Options
% 3.14/0.94  
% 3.14/0.94  --bmc1_incremental                      false
% 3.14/0.94  --bmc1_axioms                           reachable_all
% 3.14/0.94  --bmc1_min_bound                        0
% 3.14/0.94  --bmc1_max_bound                        -1
% 3.14/0.94  --bmc1_max_bound_default                -1
% 3.14/0.94  --bmc1_symbol_reachability              true
% 3.14/0.94  --bmc1_property_lemmas                  false
% 3.14/0.94  --bmc1_k_induction                      false
% 3.14/0.94  --bmc1_non_equiv_states                 false
% 3.14/0.94  --bmc1_deadlock                         false
% 3.14/0.94  --bmc1_ucm                              false
% 3.14/0.94  --bmc1_add_unsat_core                   none
% 3.14/0.94  --bmc1_unsat_core_children              false
% 3.14/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.94  --bmc1_out_stat                         full
% 3.14/0.94  --bmc1_ground_init                      false
% 3.14/0.94  --bmc1_pre_inst_next_state              false
% 3.14/0.94  --bmc1_pre_inst_state                   false
% 3.14/0.94  --bmc1_pre_inst_reach_state             false
% 3.14/0.94  --bmc1_out_unsat_core                   false
% 3.14/0.94  --bmc1_aig_witness_out                  false
% 3.14/0.94  --bmc1_verbose                          false
% 3.14/0.94  --bmc1_dump_clauses_tptp                false
% 3.14/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.94  --bmc1_dump_file                        -
% 3.14/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.94  --bmc1_ucm_extend_mode                  1
% 3.14/0.94  --bmc1_ucm_init_mode                    2
% 3.14/0.94  --bmc1_ucm_cone_mode                    none
% 3.14/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.94  --bmc1_ucm_relax_model                  4
% 3.14/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.94  --bmc1_ucm_layered_model                none
% 3.14/0.94  --bmc1_ucm_max_lemma_size               10
% 3.14/0.94  
% 3.14/0.94  ------ AIG Options
% 3.14/0.94  
% 3.14/0.94  --aig_mode                              false
% 3.14/0.94  
% 3.14/0.94  ------ Instantiation Options
% 3.14/0.94  
% 3.14/0.94  --instantiation_flag                    true
% 3.14/0.94  --inst_sos_flag                         false
% 3.14/0.94  --inst_sos_phase                        true
% 3.14/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.94  --inst_lit_sel_side                     num_symb
% 3.14/0.94  --inst_solver_per_active                1400
% 3.14/0.94  --inst_solver_calls_frac                1.
% 3.14/0.94  --inst_passive_queue_type               priority_queues
% 3.14/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.94  --inst_passive_queues_freq              [25;2]
% 3.14/0.94  --inst_dismatching                      true
% 3.14/0.94  --inst_eager_unprocessed_to_passive     true
% 3.14/0.94  --inst_prop_sim_given                   true
% 3.14/0.94  --inst_prop_sim_new                     false
% 3.14/0.94  --inst_subs_new                         false
% 3.14/0.94  --inst_eq_res_simp                      false
% 3.14/0.94  --inst_subs_given                       false
% 3.14/0.94  --inst_orphan_elimination               true
% 3.14/0.94  --inst_learning_loop_flag               true
% 3.14/0.94  --inst_learning_start                   3000
% 3.14/0.94  --inst_learning_factor                  2
% 3.14/0.94  --inst_start_prop_sim_after_learn       3
% 3.14/0.94  --inst_sel_renew                        solver
% 3.14/0.94  --inst_lit_activity_flag                true
% 3.14/0.94  --inst_restr_to_given                   false
% 3.14/0.94  --inst_activity_threshold               500
% 3.14/0.94  --inst_out_proof                        true
% 3.14/0.94  
% 3.14/0.94  ------ Resolution Options
% 3.14/0.94  
% 3.14/0.94  --resolution_flag                       true
% 3.14/0.94  --res_lit_sel                           adaptive
% 3.14/0.94  --res_lit_sel_side                      none
% 3.14/0.94  --res_ordering                          kbo
% 3.14/0.94  --res_to_prop_solver                    active
% 3.14/0.94  --res_prop_simpl_new                    false
% 3.14/0.94  --res_prop_simpl_given                  true
% 3.14/0.94  --res_passive_queue_type                priority_queues
% 3.14/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.94  --res_passive_queues_freq               [15;5]
% 3.14/0.94  --res_forward_subs                      full
% 3.14/0.94  --res_backward_subs                     full
% 3.14/0.94  --res_forward_subs_resolution           true
% 3.14/0.94  --res_backward_subs_resolution          true
% 3.14/0.94  --res_orphan_elimination                true
% 3.14/0.94  --res_time_limit                        2.
% 3.14/0.94  --res_out_proof                         true
% 3.14/0.94  
% 3.14/0.94  ------ Superposition Options
% 3.14/0.94  
% 3.14/0.94  --superposition_flag                    true
% 3.14/0.94  --sup_passive_queue_type                priority_queues
% 3.14/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.94  --demod_completeness_check              fast
% 3.14/0.94  --demod_use_ground                      true
% 3.14/0.94  --sup_to_prop_solver                    passive
% 3.14/0.94  --sup_prop_simpl_new                    true
% 3.14/0.94  --sup_prop_simpl_given                  true
% 3.14/0.94  --sup_fun_splitting                     false
% 3.14/0.94  --sup_smt_interval                      50000
% 3.14/0.94  
% 3.14/0.94  ------ Superposition Simplification Setup
% 3.14/0.94  
% 3.14/0.94  --sup_indices_passive                   []
% 3.14/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_full_bw                           [BwDemod]
% 3.14/0.94  --sup_immed_triv                        [TrivRules]
% 3.14/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_immed_bw_main                     []
% 3.14/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.94  
% 3.14/0.94  ------ Combination Options
% 3.14/0.94  
% 3.14/0.94  --comb_res_mult                         3
% 3.14/0.94  --comb_sup_mult                         2
% 3.14/0.94  --comb_inst_mult                        10
% 3.14/0.94  
% 3.14/0.94  ------ Debug Options
% 3.14/0.94  
% 3.14/0.94  --dbg_backtrace                         false
% 3.14/0.94  --dbg_dump_prop_clauses                 false
% 3.14/0.94  --dbg_dump_prop_clauses_file            -
% 3.14/0.94  --dbg_out_stat                          false
% 3.14/0.94  ------ Parsing...
% 3.14/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/0.94  ------ Proving...
% 3.14/0.94  ------ Problem Properties 
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  clauses                                 23
% 3.14/0.94  conjectures                             2
% 3.14/0.94  EPR                                     8
% 3.14/0.94  Horn                                    16
% 3.14/0.94  unary                                   5
% 3.14/0.94  binary                                  8
% 3.14/0.94  lits                                    53
% 3.14/0.94  lits eq                                 10
% 3.14/0.94  fd_pure                                 0
% 3.14/0.94  fd_pseudo                               0
% 3.14/0.94  fd_cond                                 0
% 3.14/0.94  fd_pseudo_cond                          7
% 3.14/0.94  AC symbols                              0
% 3.14/0.94  
% 3.14/0.94  ------ Schedule dynamic 5 is on 
% 3.14/0.94  
% 3.14/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  ------ 
% 3.14/0.94  Current options:
% 3.14/0.94  ------ 
% 3.14/0.94  
% 3.14/0.94  ------ Input Options
% 3.14/0.94  
% 3.14/0.94  --out_options                           all
% 3.14/0.94  --tptp_safe_out                         true
% 3.14/0.94  --problem_path                          ""
% 3.14/0.94  --include_path                          ""
% 3.14/0.94  --clausifier                            res/vclausify_rel
% 3.14/0.94  --clausifier_options                    --mode clausify
% 3.14/0.94  --stdin                                 false
% 3.14/0.94  --stats_out                             all
% 3.14/0.94  
% 3.14/0.94  ------ General Options
% 3.14/0.94  
% 3.14/0.94  --fof                                   false
% 3.14/0.94  --time_out_real                         305.
% 3.14/0.94  --time_out_virtual                      -1.
% 3.14/0.94  --symbol_type_check                     false
% 3.14/0.94  --clausify_out                          false
% 3.14/0.94  --sig_cnt_out                           false
% 3.14/0.94  --trig_cnt_out                          false
% 3.14/0.94  --trig_cnt_out_tolerance                1.
% 3.14/0.94  --trig_cnt_out_sk_spl                   false
% 3.14/0.94  --abstr_cl_out                          false
% 3.14/0.94  
% 3.14/0.94  ------ Global Options
% 3.14/0.94  
% 3.14/0.94  --schedule                              default
% 3.14/0.94  --add_important_lit                     false
% 3.14/0.94  --prop_solver_per_cl                    1000
% 3.14/0.94  --min_unsat_core                        false
% 3.14/0.94  --soft_assumptions                      false
% 3.14/0.94  --soft_lemma_size                       3
% 3.14/0.94  --prop_impl_unit_size                   0
% 3.14/0.94  --prop_impl_unit                        []
% 3.14/0.94  --share_sel_clauses                     true
% 3.14/0.94  --reset_solvers                         false
% 3.14/0.94  --bc_imp_inh                            [conj_cone]
% 3.14/0.94  --conj_cone_tolerance                   3.
% 3.14/0.94  --extra_neg_conj                        none
% 3.14/0.94  --large_theory_mode                     true
% 3.14/0.94  --prolific_symb_bound                   200
% 3.14/0.94  --lt_threshold                          2000
% 3.14/0.94  --clause_weak_htbl                      true
% 3.14/0.94  --gc_record_bc_elim                     false
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing Options
% 3.14/0.94  
% 3.14/0.94  --preprocessing_flag                    true
% 3.14/0.94  --time_out_prep_mult                    0.1
% 3.14/0.94  --splitting_mode                        input
% 3.14/0.94  --splitting_grd                         true
% 3.14/0.94  --splitting_cvd                         false
% 3.14/0.94  --splitting_cvd_svl                     false
% 3.14/0.94  --splitting_nvd                         32
% 3.14/0.94  --sub_typing                            true
% 3.14/0.94  --prep_gs_sim                           true
% 3.14/0.94  --prep_unflatten                        true
% 3.14/0.94  --prep_res_sim                          true
% 3.14/0.94  --prep_upred                            true
% 3.14/0.94  --prep_sem_filter                       exhaustive
% 3.14/0.94  --prep_sem_filter_out                   false
% 3.14/0.94  --pred_elim                             true
% 3.14/0.94  --res_sim_input                         true
% 3.14/0.94  --eq_ax_congr_red                       true
% 3.14/0.94  --pure_diseq_elim                       true
% 3.14/0.94  --brand_transform                       false
% 3.14/0.94  --non_eq_to_eq                          false
% 3.14/0.94  --prep_def_merge                        true
% 3.14/0.94  --prep_def_merge_prop_impl              false
% 3.14/0.94  --prep_def_merge_mbd                    true
% 3.14/0.94  --prep_def_merge_tr_red                 false
% 3.14/0.94  --prep_def_merge_tr_cl                  false
% 3.14/0.94  --smt_preprocessing                     true
% 3.14/0.94  --smt_ac_axioms                         fast
% 3.14/0.94  --preprocessed_out                      false
% 3.14/0.94  --preprocessed_stats                    false
% 3.14/0.94  
% 3.14/0.94  ------ Abstraction refinement Options
% 3.14/0.94  
% 3.14/0.94  --abstr_ref                             []
% 3.14/0.94  --abstr_ref_prep                        false
% 3.14/0.94  --abstr_ref_until_sat                   false
% 3.14/0.94  --abstr_ref_sig_restrict                funpre
% 3.14/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.94  --abstr_ref_under                       []
% 3.14/0.94  
% 3.14/0.94  ------ SAT Options
% 3.14/0.94  
% 3.14/0.94  --sat_mode                              false
% 3.14/0.94  --sat_fm_restart_options                ""
% 3.14/0.94  --sat_gr_def                            false
% 3.14/0.94  --sat_epr_types                         true
% 3.14/0.94  --sat_non_cyclic_types                  false
% 3.14/0.94  --sat_finite_models                     false
% 3.14/0.94  --sat_fm_lemmas                         false
% 3.14/0.94  --sat_fm_prep                           false
% 3.14/0.94  --sat_fm_uc_incr                        true
% 3.14/0.94  --sat_out_model                         small
% 3.14/0.94  --sat_out_clauses                       false
% 3.14/0.94  
% 3.14/0.94  ------ QBF Options
% 3.14/0.94  
% 3.14/0.94  --qbf_mode                              false
% 3.14/0.94  --qbf_elim_univ                         false
% 3.14/0.94  --qbf_dom_inst                          none
% 3.14/0.94  --qbf_dom_pre_inst                      false
% 3.14/0.94  --qbf_sk_in                             false
% 3.14/0.94  --qbf_pred_elim                         true
% 3.14/0.94  --qbf_split                             512
% 3.14/0.94  
% 3.14/0.94  ------ BMC1 Options
% 3.14/0.94  
% 3.14/0.94  --bmc1_incremental                      false
% 3.14/0.94  --bmc1_axioms                           reachable_all
% 3.14/0.94  --bmc1_min_bound                        0
% 3.14/0.94  --bmc1_max_bound                        -1
% 3.14/0.94  --bmc1_max_bound_default                -1
% 3.14/0.94  --bmc1_symbol_reachability              true
% 3.14/0.94  --bmc1_property_lemmas                  false
% 3.14/0.94  --bmc1_k_induction                      false
% 3.14/0.94  --bmc1_non_equiv_states                 false
% 3.14/0.94  --bmc1_deadlock                         false
% 3.14/0.94  --bmc1_ucm                              false
% 3.14/0.94  --bmc1_add_unsat_core                   none
% 3.14/0.94  --bmc1_unsat_core_children              false
% 3.14/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.94  --bmc1_out_stat                         full
% 3.14/0.94  --bmc1_ground_init                      false
% 3.14/0.94  --bmc1_pre_inst_next_state              false
% 3.14/0.94  --bmc1_pre_inst_state                   false
% 3.14/0.94  --bmc1_pre_inst_reach_state             false
% 3.14/0.94  --bmc1_out_unsat_core                   false
% 3.14/0.94  --bmc1_aig_witness_out                  false
% 3.14/0.94  --bmc1_verbose                          false
% 3.14/0.94  --bmc1_dump_clauses_tptp                false
% 3.14/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.94  --bmc1_dump_file                        -
% 3.14/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.94  --bmc1_ucm_extend_mode                  1
% 3.14/0.94  --bmc1_ucm_init_mode                    2
% 3.14/0.94  --bmc1_ucm_cone_mode                    none
% 3.14/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.94  --bmc1_ucm_relax_model                  4
% 3.14/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.94  --bmc1_ucm_layered_model                none
% 3.14/0.94  --bmc1_ucm_max_lemma_size               10
% 3.14/0.94  
% 3.14/0.94  ------ AIG Options
% 3.14/0.94  
% 3.14/0.94  --aig_mode                              false
% 3.14/0.94  
% 3.14/0.94  ------ Instantiation Options
% 3.14/0.94  
% 3.14/0.94  --instantiation_flag                    true
% 3.14/0.94  --inst_sos_flag                         false
% 3.14/0.94  --inst_sos_phase                        true
% 3.14/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.94  --inst_lit_sel_side                     none
% 3.14/0.94  --inst_solver_per_active                1400
% 3.14/0.94  --inst_solver_calls_frac                1.
% 3.14/0.94  --inst_passive_queue_type               priority_queues
% 3.14/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.94  --inst_passive_queues_freq              [25;2]
% 3.14/0.94  --inst_dismatching                      true
% 3.14/0.94  --inst_eager_unprocessed_to_passive     true
% 3.14/0.94  --inst_prop_sim_given                   true
% 3.14/0.94  --inst_prop_sim_new                     false
% 3.14/0.94  --inst_subs_new                         false
% 3.14/0.94  --inst_eq_res_simp                      false
% 3.14/0.94  --inst_subs_given                       false
% 3.14/0.94  --inst_orphan_elimination               true
% 3.14/0.94  --inst_learning_loop_flag               true
% 3.14/0.94  --inst_learning_start                   3000
% 3.14/0.94  --inst_learning_factor                  2
% 3.14/0.94  --inst_start_prop_sim_after_learn       3
% 3.14/0.94  --inst_sel_renew                        solver
% 3.14/0.94  --inst_lit_activity_flag                true
% 3.14/0.94  --inst_restr_to_given                   false
% 3.14/0.94  --inst_activity_threshold               500
% 3.14/0.94  --inst_out_proof                        true
% 3.14/0.94  
% 3.14/0.94  ------ Resolution Options
% 3.14/0.94  
% 3.14/0.94  --resolution_flag                       false
% 3.14/0.94  --res_lit_sel                           adaptive
% 3.14/0.94  --res_lit_sel_side                      none
% 3.14/0.94  --res_ordering                          kbo
% 3.14/0.94  --res_to_prop_solver                    active
% 3.14/0.94  --res_prop_simpl_new                    false
% 3.14/0.94  --res_prop_simpl_given                  true
% 3.14/0.94  --res_passive_queue_type                priority_queues
% 3.14/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.94  --res_passive_queues_freq               [15;5]
% 3.14/0.94  --res_forward_subs                      full
% 3.14/0.94  --res_backward_subs                     full
% 3.14/0.94  --res_forward_subs_resolution           true
% 3.14/0.94  --res_backward_subs_resolution          true
% 3.14/0.94  --res_orphan_elimination                true
% 3.14/0.94  --res_time_limit                        2.
% 3.14/0.94  --res_out_proof                         true
% 3.14/0.94  
% 3.14/0.94  ------ Superposition Options
% 3.14/0.94  
% 3.14/0.94  --superposition_flag                    true
% 3.14/0.94  --sup_passive_queue_type                priority_queues
% 3.14/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.94  --demod_completeness_check              fast
% 3.14/0.94  --demod_use_ground                      true
% 3.14/0.94  --sup_to_prop_solver                    passive
% 3.14/0.94  --sup_prop_simpl_new                    true
% 3.14/0.94  --sup_prop_simpl_given                  true
% 3.14/0.94  --sup_fun_splitting                     false
% 3.14/0.94  --sup_smt_interval                      50000
% 3.14/0.94  
% 3.14/0.94  ------ Superposition Simplification Setup
% 3.14/0.94  
% 3.14/0.94  --sup_indices_passive                   []
% 3.14/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_full_bw                           [BwDemod]
% 3.14/0.94  --sup_immed_triv                        [TrivRules]
% 3.14/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_immed_bw_main                     []
% 3.14/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.94  
% 3.14/0.94  ------ Combination Options
% 3.14/0.94  
% 3.14/0.94  --comb_res_mult                         3
% 3.14/0.94  --comb_sup_mult                         2
% 3.14/0.94  --comb_inst_mult                        10
% 3.14/0.94  
% 3.14/0.94  ------ Debug Options
% 3.14/0.94  
% 3.14/0.94  --dbg_backtrace                         false
% 3.14/0.94  --dbg_dump_prop_clauses                 false
% 3.14/0.94  --dbg_dump_prop_clauses_file            -
% 3.14/0.94  --dbg_out_stat                          false
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  ------ Proving...
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  % SZS status Theorem for theBenchmark.p
% 3.14/0.94  
% 3.14/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/0.94  
% 3.14/0.94  fof(f1,axiom,(
% 3.14/0.94    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.14/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.94  
% 3.14/0.94  fof(f23,plain,(
% 3.14/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.14/0.94    inference(nnf_transformation,[],[f1])).
% 3.14/0.94  
% 3.14/0.94  fof(f24,plain,(
% 3.14/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.14/0.94    inference(flattening,[],[f23])).
% 3.14/0.94  
% 3.14/0.94  fof(f25,plain,(
% 3.14/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.14/0.94    inference(rectify,[],[f24])).
% 3.14/0.94  
% 3.14/0.94  fof(f26,plain,(
% 3.14/0.94    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.14/0.94    introduced(choice_axiom,[])).
% 3.14/0.94  
% 3.14/0.94  fof(f27,plain,(
% 3.14/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.14/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.14/0.94  
% 3.14/0.94  fof(f44,plain,(
% 3.14/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.14/0.94    inference(cnf_transformation,[],[f27])).
% 3.14/0.94  
% 3.14/0.94  fof(f74,plain,(
% 3.14/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.14/0.94    inference(equality_resolution,[],[f44])).
% 3.14/0.94  
% 3.14/0.94  fof(f7,axiom,(
% 3.14/0.94    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.14/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.94  
% 3.14/0.94  fof(f17,plain,(
% 3.14/0.94    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.14/0.94    inference(ennf_transformation,[],[f7])).
% 3.14/0.94  
% 3.14/0.94  fof(f18,plain,(
% 3.14/0.94    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.14/0.94    inference(flattening,[],[f17])).
% 3.14/0.94  
% 3.14/0.94  fof(f34,plain,(
% 3.14/0.94    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.14/0.94    inference(nnf_transformation,[],[f18])).
% 3.14/0.94  
% 3.14/0.94  fof(f59,plain,(
% 3.14/0.94    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.14/0.94    inference(cnf_transformation,[],[f34])).
% 3.14/0.94  
% 3.14/0.94  fof(f11,conjecture,(
% 3.14/0.94    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.14/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.94  
% 3.14/0.94  fof(f12,negated_conjecture,(
% 3.14/0.94    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.14/0.94    inference(negated_conjecture,[],[f11])).
% 3.14/0.94  
% 3.14/0.94  fof(f22,plain,(
% 3.14/0.94    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.14/0.94    inference(ennf_transformation,[],[f12])).
% 3.14/0.94  
% 3.14/0.94  fof(f37,plain,(
% 3.14/0.94    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.14/0.94    inference(nnf_transformation,[],[f22])).
% 3.14/0.94  
% 3.14/0.94  fof(f38,plain,(
% 3.14/0.94    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.14/0.94    inference(flattening,[],[f37])).
% 3.14/0.94  
% 3.14/0.94  fof(f40,plain,(
% 3.14/0.94    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK3) | ~r2_hidden(X0,k1_ordinal1(sK3))) & (r1_ordinal1(X0,sK3) | r2_hidden(X0,k1_ordinal1(sK3))) & v3_ordinal1(sK3))) )),
% 3.14/0.94    introduced(choice_axiom,[])).
% 3.14/0.94  
% 3.14/0.94  fof(f39,plain,(
% 3.14/0.94    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK2,X1) | ~r2_hidden(sK2,k1_ordinal1(X1))) & (r1_ordinal1(sK2,X1) | r2_hidden(sK2,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 3.14/0.94    introduced(choice_axiom,[])).
% 3.14/0.94  
% 3.14/0.94  fof(f41,plain,(
% 3.14/0.94    ((~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))) & (r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 3.14/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).
% 3.14/0.94  
% 3.14/0.94  fof(f68,plain,(
% 3.14/0.94    ~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))),
% 3.14/0.94    inference(cnf_transformation,[],[f41])).
% 3.14/0.94  
% 3.14/0.94  fof(f5,axiom,(
% 3.14/0.94    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.14/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.94  
% 3.14/0.94  fof(f56,plain,(
% 3.14/0.94    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.14/0.94    inference(cnf_transformation,[],[f5])).
% 3.14/0.94  
% 3.14/0.94  fof(f72,plain,(
% 3.14/0.94    ~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3)))),
% 3.14/0.94    inference(definition_unfolding,[],[f68,f56])).
% 3.14/0.94  
% 3.14/0.94  fof(f65,plain,(
% 3.14/0.94    v3_ordinal1(sK2)),
% 3.14/0.94    inference(cnf_transformation,[],[f41])).
% 3.14/0.94  
% 3.14/0.94  fof(f66,plain,(
% 3.14/0.94    v3_ordinal1(sK3)),
% 3.14/0.94    inference(cnf_transformation,[],[f41])).
% 3.14/0.94  
% 3.14/0.94  fof(f3,axiom,(
% 3.14/0.94    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.14/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.94  
% 3.14/0.94  fof(f30,plain,(
% 3.14/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.14/0.94    inference(nnf_transformation,[],[f3])).
% 3.14/0.94  
% 3.14/0.94  fof(f31,plain,(
% 3.14/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.14/0.94    inference(rectify,[],[f30])).
% 3.14/0.94  
% 3.14/0.94  fof(f32,plain,(
% 3.14/0.94    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.14/0.94    introduced(choice_axiom,[])).
% 3.14/0.94  
% 3.14/0.94  fof(f33,plain,(
% 3.14/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.14/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.14/0.94  
% 3.14/0.94  fof(f51,plain,(
% 3.14/0.94    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.14/0.94    inference(cnf_transformation,[],[f33])).
% 3.14/0.94  
% 3.14/0.94  fof(f81,plain,(
% 3.14/0.94    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.14/0.94    inference(equality_resolution,[],[f51])).
% 3.14/0.94  
% 3.14/0.94  fof(f52,plain,(
% 3.14/0.94    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.14/0.94    inference(cnf_transformation,[],[f33])).
% 3.14/0.94  
% 3.14/0.94  fof(f79,plain,(
% 3.14/0.94    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.14/0.94    inference(equality_resolution,[],[f52])).
% 3.14/0.94  
% 3.14/0.94  fof(f80,plain,(
% 3.14/0.94    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.14/0.94    inference(equality_resolution,[],[f79])).
% 3.14/0.94  
% 3.14/0.94  fof(f2,axiom,(
% 3.14/0.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.14/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.94  
% 3.14/0.94  fof(f28,plain,(
% 3.14/0.94    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/0.94    inference(nnf_transformation,[],[f2])).
% 3.14/0.94  
% 3.14/0.94  fof(f29,plain,(
% 3.14/0.94    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/0.94    inference(flattening,[],[f28])).
% 3.14/0.94  
% 3.14/0.94  fof(f48,plain,(
% 3.14/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.14/0.94    inference(cnf_transformation,[],[f29])).
% 3.14/0.94  
% 3.14/0.94  fof(f78,plain,(
% 3.14/0.94    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.14/0.94    inference(equality_resolution,[],[f48])).
% 3.14/0.94  
% 3.14/0.94  fof(f43,plain,(
% 3.14/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.14/0.94    inference(cnf_transformation,[],[f27])).
% 3.14/0.94  
% 3.14/0.94  fof(f75,plain,(
% 3.14/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.14/0.94    inference(equality_resolution,[],[f43])).
% 3.14/0.94  
% 3.14/0.94  fof(f4,axiom,(
% 3.14/0.94    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 3.14/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.94  
% 3.14/0.94  fof(f14,plain,(
% 3.14/0.94    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 3.14/0.94    inference(pure_predicate_removal,[],[f4])).
% 3.14/0.94  
% 3.14/0.94  fof(f15,plain,(
% 3.14/0.94    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 3.14/0.94    inference(ennf_transformation,[],[f14])).
% 3.14/0.94  
% 3.14/0.94  fof(f55,plain,(
% 3.14/0.94    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.14/0.94    inference(cnf_transformation,[],[f15])).
% 3.14/0.94  
% 3.14/0.94  fof(f6,axiom,(
% 3.14/0.94    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.14/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.94  
% 3.14/0.94  fof(f13,plain,(
% 3.14/0.94    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.14/0.94    inference(unused_predicate_definition_removal,[],[f6])).
% 3.14/0.94  
% 3.14/0.94  fof(f16,plain,(
% 3.14/0.94    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 3.14/0.94    inference(ennf_transformation,[],[f13])).
% 3.14/0.94  
% 3.14/0.94  fof(f57,plain,(
% 3.14/0.94    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 3.14/0.94    inference(cnf_transformation,[],[f16])).
% 3.14/0.94  
% 3.14/0.94  fof(f58,plain,(
% 3.14/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.14/0.94    inference(cnf_transformation,[],[f34])).
% 3.14/0.94  
% 3.14/0.94  fof(f67,plain,(
% 3.14/0.94    r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))),
% 3.14/0.94    inference(cnf_transformation,[],[f41])).
% 3.14/0.94  
% 3.14/0.94  fof(f73,plain,(
% 3.14/0.94    r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3)))),
% 3.14/0.94    inference(definition_unfolding,[],[f67,f56])).
% 3.14/0.94  
% 3.14/0.94  fof(f42,plain,(
% 3.14/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.14/0.94    inference(cnf_transformation,[],[f27])).
% 3.14/0.94  
% 3.14/0.94  fof(f76,plain,(
% 3.14/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.14/0.94    inference(equality_resolution,[],[f42])).
% 3.14/0.94  
% 3.14/0.94  fof(f9,axiom,(
% 3.14/0.94    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.14/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.94  
% 3.14/0.94  fof(f19,plain,(
% 3.14/0.94    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.14/0.94    inference(ennf_transformation,[],[f9])).
% 3.14/0.94  
% 3.14/0.94  fof(f20,plain,(
% 3.14/0.94    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.14/0.94    inference(flattening,[],[f19])).
% 3.14/0.94  
% 3.14/0.94  fof(f63,plain,(
% 3.14/0.94    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.14/0.94    inference(cnf_transformation,[],[f20])).
% 3.14/0.94  
% 3.14/0.94  fof(f50,plain,(
% 3.14/0.94    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.14/0.94    inference(cnf_transformation,[],[f29])).
% 3.14/0.94  
% 3.14/0.94  cnf(c_628,plain,
% 3.14/0.94      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.14/0.94      theory(equality) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1398,plain,
% 3.14/0.94      ( r2_hidden(X0,X1)
% 3.14/0.94      | ~ r2_hidden(X2,k1_tarski(X2))
% 3.14/0.94      | X0 != X2
% 3.14/0.94      | X1 != k1_tarski(X2) ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_628]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_2492,plain,
% 3.14/0.94      ( ~ r2_hidden(X0,k1_tarski(X0))
% 3.14/0.94      | r2_hidden(X1,k1_tarski(X0))
% 3.14/0.94      | X1 != X0
% 3.14/0.94      | k1_tarski(X0) != k1_tarski(X0) ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_1398]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_8371,plain,
% 3.14/0.94      ( ~ r2_hidden(X0,k1_tarski(X0))
% 3.14/0.94      | r2_hidden(sK2,k1_tarski(X0))
% 3.14/0.94      | k1_tarski(X0) != k1_tarski(X0)
% 3.14/0.94      | sK2 != X0 ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_2492]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_8373,plain,
% 3.14/0.94      ( ~ r2_hidden(sK3,k1_tarski(sK3))
% 3.14/0.94      | r2_hidden(sK2,k1_tarski(sK3))
% 3.14/0.94      | k1_tarski(sK3) != k1_tarski(sK3)
% 3.14/0.94      | sK2 != sK3 ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_8371]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_3,plain,
% 3.14/0.94      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.14/0.94      inference(cnf_transformation,[],[f74]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1154,plain,
% 3.14/0.94      ( r2_hidden(X0,X1) != iProver_top
% 3.14/0.94      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_15,plain,
% 3.14/0.94      ( r1_ordinal1(X0,X1)
% 3.14/0.94      | ~ r1_tarski(X0,X1)
% 3.14/0.94      | ~ v3_ordinal1(X0)
% 3.14/0.94      | ~ v3_ordinal1(X1) ),
% 3.14/0.94      inference(cnf_transformation,[],[f59]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_22,negated_conjecture,
% 3.14/0.94      ( ~ r1_ordinal1(sK2,sK3)
% 3.14/0.94      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
% 3.14/0.94      inference(cnf_transformation,[],[f72]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_201,plain,
% 3.14/0.94      ( ~ r1_ordinal1(sK2,sK3)
% 3.14/0.94      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
% 3.14/0.94      inference(prop_impl,[status(thm)],[c_22]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_381,plain,
% 3.14/0.94      ( ~ r1_tarski(X0,X1)
% 3.14/0.94      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3)))
% 3.14/0.94      | ~ v3_ordinal1(X0)
% 3.14/0.94      | ~ v3_ordinal1(X1)
% 3.14/0.94      | sK3 != X1
% 3.14/0.94      | sK2 != X0 ),
% 3.14/0.94      inference(resolution_lifted,[status(thm)],[c_15,c_201]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_382,plain,
% 3.14/0.94      ( ~ r1_tarski(sK2,sK3)
% 3.14/0.94      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3)))
% 3.14/0.94      | ~ v3_ordinal1(sK3)
% 3.14/0.94      | ~ v3_ordinal1(sK2) ),
% 3.14/0.94      inference(unflattening,[status(thm)],[c_381]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_25,negated_conjecture,
% 3.14/0.94      ( v3_ordinal1(sK2) ),
% 3.14/0.94      inference(cnf_transformation,[],[f65]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_24,negated_conjecture,
% 3.14/0.94      ( v3_ordinal1(sK3) ),
% 3.14/0.94      inference(cnf_transformation,[],[f66]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_384,plain,
% 3.14/0.94      ( ~ r1_tarski(sK2,sK3)
% 3.14/0.94      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
% 3.14/0.94      inference(global_propositional_subsumption,
% 3.14/0.94                [status(thm)],
% 3.14/0.94                [c_382,c_25,c_24]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_500,plain,
% 3.14/0.94      ( ~ r1_tarski(sK2,sK3)
% 3.14/0.94      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
% 3.14/0.94      inference(prop_impl,[status(thm)],[c_25,c_24,c_382]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1137,plain,
% 3.14/0.94      ( r1_tarski(sK2,sK3) != iProver_top
% 3.14/0.94      | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1758,plain,
% 3.14/0.94      ( r1_tarski(sK2,sK3) != iProver_top
% 3.14/0.94      | r2_hidden(sK2,k1_tarski(sK3)) != iProver_top ),
% 3.14/0.94      inference(superposition,[status(thm)],[c_1154,c_1137]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_12,plain,
% 3.14/0.94      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.14/0.94      inference(cnf_transformation,[],[f81]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_58,plain,
% 3.14/0.94      ( ~ r2_hidden(sK3,k1_tarski(sK3)) | sK3 = sK3 ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_12]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_11,plain,
% 3.14/0.94      ( r2_hidden(X0,k1_tarski(X0)) ),
% 3.14/0.94      inference(cnf_transformation,[],[f80]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_61,plain,
% 3.14/0.94      ( r2_hidden(sK3,k1_tarski(sK3)) ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_11]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_8,plain,
% 3.14/0.94      ( r1_tarski(X0,X0) ),
% 3.14/0.94      inference(cnf_transformation,[],[f78]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_69,plain,
% 3.14/0.94      ( r1_tarski(X0,X0) = iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_71,plain,
% 3.14/0.94      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_69]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_629,plain,
% 3.14/0.94      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.14/0.94      theory(equality) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1417,plain,
% 3.14/0.94      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,sK3) | sK3 != X1 | sK2 != X0 ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_629]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1418,plain,
% 3.14/0.94      ( sK3 != X0
% 3.14/0.94      | sK2 != X1
% 3.14/0.94      | r1_tarski(X1,X0) != iProver_top
% 3.14/0.94      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_1417]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1420,plain,
% 3.14/0.94      ( sK3 != sK3
% 3.14/0.94      | sK2 != sK3
% 3.14/0.94      | r1_tarski(sK3,sK3) != iProver_top
% 3.14/0.94      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_1418]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1496,plain,
% 3.14/0.94      ( ~ r2_hidden(sK2,k1_tarski(X0)) | sK2 = X0 ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_12]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1497,plain,
% 3.14/0.94      ( sK2 = X0 | r2_hidden(sK2,k1_tarski(X0)) != iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_1496]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1499,plain,
% 3.14/0.94      ( sK2 = sK3 | r2_hidden(sK2,k1_tarski(sK3)) != iProver_top ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_1497]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_5818,plain,
% 3.14/0.94      ( r2_hidden(sK2,k1_tarski(sK3)) != iProver_top ),
% 3.14/0.94      inference(global_propositional_subsumption,
% 3.14/0.94                [status(thm)],
% 3.14/0.94                [c_1758,c_58,c_61,c_71,c_1420,c_1499]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_4,plain,
% 3.14/0.94      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.14/0.94      inference(cnf_transformation,[],[f75]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1153,plain,
% 3.14/0.94      ( r2_hidden(X0,X1) != iProver_top
% 3.14/0.94      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1759,plain,
% 3.14/0.94      ( r1_tarski(sK2,sK3) != iProver_top
% 3.14/0.94      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.14/0.94      inference(superposition,[status(thm)],[c_1153,c_1137]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_27,plain,
% 3.14/0.94      ( v3_ordinal1(sK3) = iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_13,plain,
% 3.14/0.94      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 3.14/0.94      inference(cnf_transformation,[],[f55]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_14,plain,
% 3.14/0.94      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 3.14/0.94      inference(cnf_transformation,[],[f57]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_333,plain,
% 3.14/0.94      ( r1_tarski(X0,X1)
% 3.14/0.94      | ~ r2_hidden(X0,X1)
% 3.14/0.94      | ~ v3_ordinal1(X2)
% 3.14/0.94      | X1 != X2 ),
% 3.14/0.94      inference(resolution_lifted,[status(thm)],[c_13,c_14]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_334,plain,
% 3.14/0.94      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) ),
% 3.14/0.94      inference(unflattening,[status(thm)],[c_333]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1375,plain,
% 3.14/0.94      ( r1_tarski(sK2,sK3) | ~ r2_hidden(sK2,sK3) | ~ v3_ordinal1(sK3) ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_334]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1376,plain,
% 3.14/0.94      ( r1_tarski(sK2,sK3) = iProver_top
% 3.14/0.94      | r2_hidden(sK2,sK3) != iProver_top
% 3.14/0.94      | v3_ordinal1(sK3) != iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_5598,plain,
% 3.14/0.94      ( r2_hidden(sK2,sK3) != iProver_top ),
% 3.14/0.94      inference(global_propositional_subsumption,
% 3.14/0.94                [status(thm)],
% 3.14/0.94                [c_1759,c_27,c_1376]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_16,plain,
% 3.14/0.94      ( ~ r1_ordinal1(X0,X1)
% 3.14/0.94      | r1_tarski(X0,X1)
% 3.14/0.94      | ~ v3_ordinal1(X0)
% 3.14/0.94      | ~ v3_ordinal1(X1) ),
% 3.14/0.94      inference(cnf_transformation,[],[f58]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_23,negated_conjecture,
% 3.14/0.94      ( r1_ordinal1(sK2,sK3)
% 3.14/0.94      | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
% 3.14/0.94      inference(cnf_transformation,[],[f73]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_203,plain,
% 3.14/0.94      ( r1_ordinal1(sK2,sK3)
% 3.14/0.94      | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
% 3.14/0.94      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_395,plain,
% 3.14/0.94      ( r1_tarski(X0,X1)
% 3.14/0.94      | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3)))
% 3.14/0.94      | ~ v3_ordinal1(X0)
% 3.14/0.94      | ~ v3_ordinal1(X1)
% 3.14/0.94      | sK3 != X1
% 3.14/0.94      | sK2 != X0 ),
% 3.14/0.94      inference(resolution_lifted,[status(thm)],[c_16,c_203]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_396,plain,
% 3.14/0.94      ( r1_tarski(sK2,sK3)
% 3.14/0.94      | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3)))
% 3.14/0.94      | ~ v3_ordinal1(sK3)
% 3.14/0.94      | ~ v3_ordinal1(sK2) ),
% 3.14/0.94      inference(unflattening,[status(thm)],[c_395]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_398,plain,
% 3.14/0.94      ( r1_tarski(sK2,sK3)
% 3.14/0.94      | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
% 3.14/0.94      inference(global_propositional_subsumption,
% 3.14/0.94                [status(thm)],
% 3.14/0.94                [c_396,c_25,c_24]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_502,plain,
% 3.14/0.94      ( r1_tarski(sK2,sK3)
% 3.14/0.94      | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) ),
% 3.14/0.94      inference(prop_impl,[status(thm)],[c_25,c_24,c_396]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1136,plain,
% 3.14/0.94      ( r1_tarski(sK2,sK3) = iProver_top
% 3.14/0.94      | r2_hidden(sK2,k2_xboole_0(sK3,k1_tarski(sK3))) = iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_5,plain,
% 3.14/0.94      ( r2_hidden(X0,X1)
% 3.14/0.94      | r2_hidden(X0,X2)
% 3.14/0.94      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.14/0.94      inference(cnf_transformation,[],[f76]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1152,plain,
% 3.14/0.94      ( r2_hidden(X0,X1) = iProver_top
% 3.14/0.94      | r2_hidden(X0,X2) = iProver_top
% 3.14/0.94      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_5117,plain,
% 3.14/0.94      ( r1_tarski(sK2,sK3) = iProver_top
% 3.14/0.94      | r2_hidden(sK2,k1_tarski(sK3)) = iProver_top
% 3.14/0.94      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.14/0.94      inference(superposition,[status(thm)],[c_1136,c_1152]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_20,plain,
% 3.14/0.94      ( r1_ordinal1(X0,X1)
% 3.14/0.94      | r2_hidden(X1,X0)
% 3.14/0.94      | ~ v3_ordinal1(X0)
% 3.14/0.94      | ~ v3_ordinal1(X1) ),
% 3.14/0.94      inference(cnf_transformation,[],[f63]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_350,plain,
% 3.14/0.94      ( r1_tarski(X0,X1)
% 3.14/0.94      | r2_hidden(X1,X0)
% 3.14/0.94      | ~ v3_ordinal1(X0)
% 3.14/0.94      | ~ v3_ordinal1(X1) ),
% 3.14/0.94      inference(resolution,[status(thm)],[c_20,c_16]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1895,plain,
% 3.14/0.94      ( r1_tarski(X0,sK2)
% 3.14/0.94      | r2_hidden(sK2,X0)
% 3.14/0.94      | ~ v3_ordinal1(X0)
% 3.14/0.94      | ~ v3_ordinal1(sK2) ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_350]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1901,plain,
% 3.14/0.94      ( r1_tarski(X0,sK2) = iProver_top
% 3.14/0.94      | r2_hidden(sK2,X0) = iProver_top
% 3.14/0.94      | v3_ordinal1(X0) != iProver_top
% 3.14/0.94      | v3_ordinal1(sK2) != iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_1895]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1903,plain,
% 3.14/0.94      ( r1_tarski(sK3,sK2) = iProver_top
% 3.14/0.94      | r2_hidden(sK2,sK3) = iProver_top
% 3.14/0.94      | v3_ordinal1(sK3) != iProver_top
% 3.14/0.94      | v3_ordinal1(sK2) != iProver_top ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_1901]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1769,plain,
% 3.14/0.94      ( ~ r1_tarski(sK2,sK3) | ~ r2_hidden(sK2,k1_tarski(sK3)) ),
% 3.14/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_1758]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_6,plain,
% 3.14/0.94      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.14/0.94      inference(cnf_transformation,[],[f50]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1495,plain,
% 3.14/0.94      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_6]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1501,plain,
% 3.14/0.94      ( sK2 = X0
% 3.14/0.94      | r1_tarski(X0,sK2) != iProver_top
% 3.14/0.94      | r1_tarski(sK2,X0) != iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_1495]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1503,plain,
% 3.14/0.94      ( sK2 = sK3
% 3.14/0.94      | r1_tarski(sK3,sK2) != iProver_top
% 3.14/0.94      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_1501]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_1419,plain,
% 3.14/0.94      ( ~ r1_tarski(sK3,sK3)
% 3.14/0.94      | r1_tarski(sK2,sK3)
% 3.14/0.94      | sK3 != sK3
% 3.14/0.94      | sK2 != sK3 ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_1417]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_630,plain,
% 3.14/0.94      ( X0 != X1 | k1_tarski(X0) = k1_tarski(X1) ),
% 3.14/0.94      theory(equality) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_635,plain,
% 3.14/0.94      ( k1_tarski(sK3) = k1_tarski(sK3) | sK3 != sK3 ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_630]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_70,plain,
% 3.14/0.94      ( r1_tarski(sK3,sK3) ),
% 3.14/0.94      inference(instantiation,[status(thm)],[c_8]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(c_26,plain,
% 3.14/0.94      ( v3_ordinal1(sK2) = iProver_top ),
% 3.14/0.94      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.14/0.94  
% 3.14/0.94  cnf(contradiction,plain,
% 3.14/0.94      ( $false ),
% 3.14/0.94      inference(minisat,
% 3.14/0.94                [status(thm)],
% 3.14/0.94                [c_8373,c_5818,c_5598,c_5117,c_1903,c_1769,c_1503,c_1419,
% 3.14/0.94                 c_635,c_70,c_61,c_58,c_27,c_26]) ).
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/0.94  
% 3.14/0.94  ------                               Statistics
% 3.14/0.94  
% 3.14/0.94  ------ General
% 3.14/0.94  
% 3.14/0.94  abstr_ref_over_cycles:                  0
% 3.14/0.94  abstr_ref_under_cycles:                 0
% 3.14/0.94  gc_basic_clause_elim:                   0
% 3.14/0.94  forced_gc_time:                         0
% 3.14/0.94  parsing_time:                           0.009
% 3.14/0.94  unif_index_cands_time:                  0.
% 3.14/0.94  unif_index_add_time:                    0.
% 3.14/0.94  orderings_time:                         0.
% 3.14/0.94  out_proof_time:                         0.009
% 3.14/0.94  total_time:                             0.261
% 3.14/0.94  num_of_symbols:                         42
% 3.14/0.94  num_of_terms:                           10503
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing
% 3.14/0.94  
% 3.14/0.94  num_of_splits:                          0
% 3.14/0.94  num_of_split_atoms:                     0
% 3.14/0.94  num_of_reused_defs:                     0
% 3.14/0.94  num_eq_ax_congr_red:                    18
% 3.14/0.94  num_of_sem_filtered_clauses:            1
% 3.14/0.94  num_of_subtypes:                        0
% 3.14/0.94  monotx_restored_types:                  0
% 3.14/0.94  sat_num_of_epr_types:                   0
% 3.14/0.94  sat_num_of_non_cyclic_types:            0
% 3.14/0.94  sat_guarded_non_collapsed_types:        0
% 3.14/0.94  num_pure_diseq_elim:                    0
% 3.14/0.94  simp_replaced_by:                       0
% 3.14/0.94  res_preprocessed:                       109
% 3.14/0.94  prep_upred:                             0
% 3.14/0.94  prep_unflattend:                        7
% 3.14/0.94  smt_new_axioms:                         0
% 3.14/0.94  pred_elim_cands:                        3
% 3.14/0.94  pred_elim:                              2
% 3.14/0.94  pred_elim_cl:                           2
% 3.14/0.94  pred_elim_cycles:                       4
% 3.14/0.94  merged_defs:                            8
% 3.14/0.94  merged_defs_ncl:                        0
% 3.14/0.94  bin_hyper_res:                          9
% 3.14/0.94  prep_cycles:                            4
% 3.14/0.94  pred_elim_time:                         0.003
% 3.14/0.94  splitting_time:                         0.
% 3.14/0.94  sem_filter_time:                        0.
% 3.14/0.94  monotx_time:                            0.001
% 3.14/0.94  subtype_inf_time:                       0.
% 3.14/0.94  
% 3.14/0.94  ------ Problem properties
% 3.14/0.94  
% 3.14/0.94  clauses:                                23
% 3.14/0.94  conjectures:                            2
% 3.14/0.94  epr:                                    8
% 3.14/0.94  horn:                                   16
% 3.14/0.94  ground:                                 5
% 3.14/0.94  unary:                                  5
% 3.14/0.94  binary:                                 8
% 3.14/0.94  lits:                                   53
% 3.14/0.94  lits_eq:                                10
% 3.14/0.94  fd_pure:                                0
% 3.14/0.94  fd_pseudo:                              0
% 3.14/0.94  fd_cond:                                0
% 3.14/0.94  fd_pseudo_cond:                         7
% 3.14/0.94  ac_symbols:                             0
% 3.14/0.94  
% 3.14/0.94  ------ Propositional Solver
% 3.14/0.94  
% 3.14/0.94  prop_solver_calls:                      27
% 3.14/0.94  prop_fast_solver_calls:                 636
% 3.14/0.94  smt_solver_calls:                       0
% 3.14/0.94  smt_fast_solver_calls:                  0
% 3.14/0.94  prop_num_of_clauses:                    3468
% 3.14/0.94  prop_preprocess_simplified:             9597
% 3.14/0.94  prop_fo_subsumed:                       8
% 3.14/0.94  prop_solver_time:                       0.
% 3.14/0.94  smt_solver_time:                        0.
% 3.14/0.94  smt_fast_solver_time:                   0.
% 3.14/0.94  prop_fast_solver_time:                  0.
% 3.14/0.94  prop_unsat_core_time:                   0.
% 3.14/0.94  
% 3.14/0.94  ------ QBF
% 3.14/0.94  
% 3.14/0.94  qbf_q_res:                              0
% 3.14/0.94  qbf_num_tautologies:                    0
% 3.14/0.94  qbf_prep_cycles:                        0
% 3.14/0.94  
% 3.14/0.94  ------ BMC1
% 3.14/0.94  
% 3.14/0.94  bmc1_current_bound:                     -1
% 3.14/0.94  bmc1_last_solved_bound:                 -1
% 3.14/0.94  bmc1_unsat_core_size:                   -1
% 3.14/0.94  bmc1_unsat_core_parents_size:           -1
% 3.14/0.94  bmc1_merge_next_fun:                    0
% 3.14/0.94  bmc1_unsat_core_clauses_time:           0.
% 3.14/0.94  
% 3.14/0.94  ------ Instantiation
% 3.14/0.94  
% 3.14/0.94  inst_num_of_clauses:                    1011
% 3.14/0.94  inst_num_in_passive:                    281
% 3.14/0.94  inst_num_in_active:                     270
% 3.14/0.94  inst_num_in_unprocessed:                459
% 3.14/0.94  inst_num_of_loops:                      280
% 3.14/0.94  inst_num_of_learning_restarts:          0
% 3.14/0.94  inst_num_moves_active_passive:          8
% 3.14/0.94  inst_lit_activity:                      0
% 3.14/0.94  inst_lit_activity_moves:                0
% 3.14/0.94  inst_num_tautologies:                   0
% 3.14/0.94  inst_num_prop_implied:                  0
% 3.14/0.94  inst_num_existing_simplified:           0
% 3.14/0.94  inst_num_eq_res_simplified:             0
% 3.14/0.94  inst_num_child_elim:                    0
% 3.14/0.94  inst_num_of_dismatching_blockings:      474
% 3.14/0.94  inst_num_of_non_proper_insts:           624
% 3.14/0.94  inst_num_of_duplicates:                 0
% 3.14/0.94  inst_inst_num_from_inst_to_res:         0
% 3.14/0.94  inst_dismatching_checking_time:         0.
% 3.14/0.94  
% 3.14/0.94  ------ Resolution
% 3.14/0.94  
% 3.14/0.94  res_num_of_clauses:                     0
% 3.14/0.94  res_num_in_passive:                     0
% 3.14/0.94  res_num_in_active:                      0
% 3.14/0.94  res_num_of_loops:                       113
% 3.14/0.94  res_forward_subset_subsumed:            109
% 3.14/0.94  res_backward_subset_subsumed:           0
% 3.14/0.94  res_forward_subsumed:                   0
% 3.14/0.94  res_backward_subsumed:                  0
% 3.14/0.94  res_forward_subsumption_resolution:     0
% 3.14/0.94  res_backward_subsumption_resolution:    0
% 3.14/0.94  res_clause_to_clause_subsumption:       1865
% 3.14/0.94  res_orphan_elimination:                 0
% 3.14/0.94  res_tautology_del:                      36
% 3.14/0.94  res_num_eq_res_simplified:              0
% 3.14/0.94  res_num_sel_changes:                    0
% 3.14/0.94  res_moves_from_active_to_pass:          0
% 3.14/0.94  
% 3.14/0.94  ------ Superposition
% 3.14/0.94  
% 3.14/0.94  sup_time_total:                         0.
% 3.14/0.94  sup_time_generating:                    0.
% 3.14/0.94  sup_time_sim_full:                      0.
% 3.14/0.94  sup_time_sim_immed:                     0.
% 3.14/0.94  
% 3.14/0.94  sup_num_of_clauses:                     121
% 3.14/0.94  sup_num_in_active:                      54
% 3.14/0.94  sup_num_in_passive:                     67
% 3.14/0.94  sup_num_of_loops:                       54
% 3.14/0.94  sup_fw_superposition:                   86
% 3.14/0.94  sup_bw_superposition:                   23
% 3.14/0.94  sup_immediate_simplified:               1
% 3.14/0.94  sup_given_eliminated:                   0
% 3.14/0.94  comparisons_done:                       0
% 3.14/0.94  comparisons_avoided:                    1
% 3.14/0.94  
% 3.14/0.94  ------ Simplifications
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  sim_fw_subset_subsumed:                 4
% 3.14/0.94  sim_bw_subset_subsumed:                 0
% 3.14/0.94  sim_fw_subsumed:                        1
% 3.14/0.94  sim_bw_subsumed:                        0
% 3.14/0.94  sim_fw_subsumption_res:                 0
% 3.14/0.94  sim_bw_subsumption_res:                 0
% 3.14/0.94  sim_tautology_del:                      11
% 3.14/0.94  sim_eq_tautology_del:                   3
% 3.14/0.94  sim_eq_res_simp:                        6
% 3.14/0.94  sim_fw_demodulated:                     0
% 3.14/0.94  sim_bw_demodulated:                     0
% 3.14/0.94  sim_light_normalised:                   0
% 3.14/0.94  sim_joinable_taut:                      0
% 3.14/0.94  sim_joinable_simp:                      0
% 3.14/0.94  sim_ac_normalised:                      0
% 3.14/0.94  sim_smt_subsumption:                    0
% 3.14/0.94  
%------------------------------------------------------------------------------
