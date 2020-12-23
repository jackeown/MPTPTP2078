%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0078+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:25 EST 2020

% Result     : Theorem 35.28s
% Output     : CNFRefutation 35.28s
% Verified   : 
% Statistics : Number of formulae       :  145 (5500 expanded)
%              Number of clauses        :  101 (1946 expanded)
%              Number of leaves         :   12 (1142 expanded)
%              Depth                    :   31
%              Number of atoms          :  478 (30950 expanded)
%              Number of equality atoms :  282 (8233 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK2 != sK4
      & r1_xboole_0(sK4,sK3)
      & r1_xboole_0(sK2,sK3)
      & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( sK2 != sK4
    & r1_xboole_0(sK4,sK3)
    & r1_xboole_0(sK2,sK3)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f23])).

fof(f41,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f43,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f42,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_393,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_391,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_390,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1677,plain,
    ( r2_hidden(X0,k2_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_390])).

cnf(c_1798,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_391,c_1677])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_382,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_383,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_783,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_382,c_383])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_384,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1367,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_783,c_384])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_381,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_784,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_381,c_383])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_386,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1646,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_386])).

cnf(c_2530,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1798,c_1367,c_1646])).

cnf(c_3306,plain,
    ( k2_xboole_0(sK2,X0) = X1
    | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_393,c_2530])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_608,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_15,c_0])).

cnf(c_882,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_608,c_391])).

cnf(c_3325,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X1
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_393,c_882])).

cnf(c_3400,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X1) = iProver_top
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3325,c_15])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_392,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_394,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2210,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)
    | r2_hidden(sK0(X2,X3,k2_xboole_0(X0,X1)),X1) != iProver_top
    | r2_hidden(sK0(X2,X3,k2_xboole_0(X0,X1)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_392,c_394])).

cnf(c_27747,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X2,k1_xboole_0)
    | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top
    | r2_hidden(sK0(X0,X1,k2_xboole_0(X2,k1_xboole_0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_2210])).

cnf(c_27765,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27747,c_15])).

cnf(c_28486,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27765,c_882])).

cnf(c_28501,plain,
    ( X0 = X1
    | k2_xboole_0(X0,k1_xboole_0) = X1
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3400,c_28486])).

cnf(c_28509,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28501,c_15])).

cnf(c_2212,plain,
    ( k3_xboole_0(X0,X1) = k2_xboole_0(X2,X3)
    | r2_hidden(sK0(X2,X3,k3_xboole_0(X0,X1)),X1) != iProver_top
    | r2_hidden(sK0(X2,X3,k3_xboole_0(X0,X1)),X0) != iProver_top
    | r2_hidden(sK0(X2,X3,k3_xboole_0(X0,X1)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_386,c_394])).

cnf(c_34994,plain,
    ( k3_xboole_0(X0,X1) = k2_xboole_0(X2,X3)
    | r2_hidden(sK0(X2,X3,k3_xboole_0(X1,X0)),X1) != iProver_top
    | r2_hidden(sK0(X2,X3,k3_xboole_0(X0,X1)),X0) != iProver_top
    | r2_hidden(sK0(X2,X3,k3_xboole_0(X0,X1)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_2212])).

cnf(c_86082,plain,
    ( k3_xboole_0(X0,X1) = X0
    | k3_xboole_0(X0,X1) = k2_xboole_0(X0,k1_xboole_0)
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X1,X0)),X1) != iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X0,X1)),X0) != iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_28509,c_34994])).

cnf(c_86129,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X1,X0)),X1) != iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X0,X1)),X0) != iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_86082,c_15])).

cnf(c_86632,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X1,X0)),X1) != iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_86129,c_28509])).

cnf(c_86642,plain,
    ( k3_xboole_0(X0,X1) = X0
    | k3_xboole_0(X0,X1) = k2_xboole_0(X0,k1_xboole_0)
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X1,X0)),X1) != iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X0,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_86632,c_394])).

cnf(c_86644,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X1,X0)),X1) != iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_86632,c_384])).

cnf(c_86670,plain,
    ( k3_xboole_0(X0,X1) = X0
    | k3_xboole_0(X0,X1) = k2_xboole_0(X0,k1_xboole_0)
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X1,X0)),X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_86642,c_86644])).

cnf(c_86671,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X1,X0)),X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_86670,c_15])).

cnf(c_86690,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k3_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_86671])).

cnf(c_118631,plain,
    ( k3_xboole_0(sK2,sK4) = k2_xboole_0(sK2,k1_xboole_0)
    | k3_xboole_0(sK2,sK4) = sK2
    | r2_hidden(sK0(sK2,k1_xboole_0,k3_xboole_0(sK2,sK4)),k3_xboole_0(sK2,sK4)) = iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0,k3_xboole_0(sK2,sK4)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3306,c_86690])).

cnf(c_119066,plain,
    ( k3_xboole_0(sK2,sK4) = sK2
    | r2_hidden(sK0(sK2,k1_xboole_0,k3_xboole_0(sK2,sK4)),k3_xboole_0(sK2,sK4)) = iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0,k3_xboole_0(sK2,sK4)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_118631,c_15])).

cnf(c_16,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_143,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_561,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_601,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_144,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_538,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_3868,plain,
    ( sK4 != k3_xboole_0(X0,X1)
    | sK2 != k3_xboole_0(X0,X1)
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_16741,plain,
    ( sK4 != k3_xboole_0(sK2,X0)
    | sK2 != k3_xboole_0(sK2,X0)
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_3868])).

cnf(c_30128,plain,
    ( sK4 != k3_xboole_0(sK2,sK4)
    | sK2 != k3_xboole_0(sK2,sK4)
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_16741])).

cnf(c_707,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_842,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_1455,plain,
    ( k3_xboole_0(X0,sK4) != sK4
    | sK4 = k3_xboole_0(X0,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_30129,plain,
    ( k3_xboole_0(sK2,sK4) != sK4
    | sK4 = k3_xboole_0(sK2,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1455])).

cnf(c_562,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_704,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_837,plain,
    ( k3_xboole_0(X0,X1) != sK2
    | sK2 = k3_xboole_0(X0,X1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_2715,plain,
    ( k3_xboole_0(sK2,X0) != sK2
    | sK2 = k3_xboole_0(sK2,X0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_39242,plain,
    ( k3_xboole_0(sK2,sK4) != sK2
    | sK2 = k3_xboole_0(sK2,sK4)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2715])).

cnf(c_10198,plain,
    ( k3_xboole_0(X0,sK4) = k3_xboole_0(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_39353,plain,
    ( k3_xboole_0(sK2,sK4) = k3_xboole_0(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_10198])).

cnf(c_1446,plain,
    ( k3_xboole_0(sK4,X0) != sK4
    | sK4 = k3_xboole_0(sK4,X0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_64351,plain,
    ( k3_xboole_0(sK4,sK2) != sK4
    | sK4 = k3_xboole_0(sK4,sK2)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_604,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_7046,plain,
    ( X0 != k3_xboole_0(sK4,X1)
    | X0 = sK4
    | sK4 != k3_xboole_0(sK4,X1) ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_10197,plain,
    ( k3_xboole_0(X0,sK4) != k3_xboole_0(sK4,X0)
    | k3_xboole_0(X0,sK4) = sK4
    | sK4 != k3_xboole_0(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_7046])).

cnf(c_65627,plain,
    ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK4,sK2)
    | k3_xboole_0(sK2,sK4) = sK4
    | sK4 != k3_xboole_0(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_10197])).

cnf(c_881,plain,
    ( r2_hidden(X0,k2_xboole_0(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_391])).

cnf(c_1673,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_881,c_390])).

cnf(c_1382,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_384])).

cnf(c_1645,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_783,c_386])).

cnf(c_2331,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1673,c_1382,c_1645])).

cnf(c_3301,plain,
    ( k2_xboole_0(sK4,X0) = X1
    | r2_hidden(sK0(sK4,X0,X1),X0) = iProver_top
    | r2_hidden(sK0(sK4,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK4,X0,X1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_393,c_2331])).

cnf(c_111389,plain,
    ( k3_xboole_0(sK4,sK2) = k2_xboole_0(sK4,k1_xboole_0)
    | k3_xboole_0(sK4,sK2) = sK4
    | r2_hidden(sK0(sK4,k1_xboole_0,k3_xboole_0(sK4,sK2)),k3_xboole_0(sK4,sK2)) = iProver_top
    | r2_hidden(sK0(sK4,k1_xboole_0,k3_xboole_0(sK4,sK2)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3301,c_86690])).

cnf(c_111814,plain,
    ( k3_xboole_0(sK4,sK2) = sK4
    | r2_hidden(sK0(sK4,k1_xboole_0,k3_xboole_0(sK4,sK2)),k3_xboole_0(sK4,sK2)) = iProver_top
    | r2_hidden(sK0(sK4,k1_xboole_0,k3_xboole_0(sK4,sK2)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_111389,c_15])).

cnf(c_114917,plain,
    ( k3_xboole_0(sK4,sK2) = sK4
    | r2_hidden(sK0(sK4,k1_xboole_0,k3_xboole_0(sK4,sK2)),k3_xboole_0(sK4,sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_111814,c_882])).

cnf(c_114923,plain,
    ( k3_xboole_0(sK4,sK2) = k2_xboole_0(sK4,k1_xboole_0)
    | k3_xboole_0(sK4,sK2) = sK4
    | r2_hidden(sK0(sK4,k1_xboole_0,k3_xboole_0(sK4,sK2)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_114917,c_394])).

cnf(c_114925,plain,
    ( k3_xboole_0(sK4,sK2) = sK4
    | r2_hidden(sK0(sK4,k1_xboole_0,k3_xboole_0(sK4,sK2)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_114917,c_384])).

cnf(c_114937,plain,
    ( k3_xboole_0(sK4,sK2) = k2_xboole_0(sK4,k1_xboole_0)
    | k3_xboole_0(sK4,sK2) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_114923,c_114925])).

cnf(c_114938,plain,
    ( k3_xboole_0(sK4,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_114937,c_15])).

cnf(c_121586,plain,
    ( r2_hidden(sK0(sK2,k1_xboole_0,k3_xboole_0(sK2,sK4)),k3_xboole_0(sK2,sK4)) = iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0,k3_xboole_0(sK2,sK4)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_119066,c_16,c_561,c_601,c_30128,c_30129,c_39242,c_39353,c_64351,c_65627,c_114938])).

cnf(c_120163,plain,
    ( k3_xboole_0(sK2,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_114938,c_1])).

cnf(c_121590,plain,
    ( r2_hidden(sK0(sK2,k1_xboole_0,sK4),sK4) = iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0,sK4),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_121586,c_120163])).

cnf(c_121593,plain,
    ( r2_hidden(sK0(sK2,k1_xboole_0,sK4),sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_121590,c_882])).

cnf(c_120162,plain,
    ( k3_xboole_0(sK2,sK4) = sK2
    | r2_hidden(sK0(sK2,k1_xboole_0,sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_114938,c_86671])).

cnf(c_120222,plain,
    ( sK4 = sK2
    | r2_hidden(sK0(sK2,k1_xboole_0,sK4),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_120162,c_120163])).

cnf(c_560,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_121593,c_120222,c_561,c_560,c_16])).


%------------------------------------------------------------------------------
