%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:48 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 279 expanded)
%              Number of clauses        :   66 ( 105 expanded)
%              Number of leaves         :   21 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  333 ( 848 expanded)
%              Number of equality atoms :  141 ( 255 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f50,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK5(X4),sK6(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK4(X0)
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK4(X0)
          & r2_hidden(sK4(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK5(X4),sK6(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f48,f50,f49])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f52])).

fof(f56,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f53,f56,f55,f54])).

fof(f78,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f44])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f19,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f35,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f20])).

fof(f87,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,plain,
    ( r2_hidden(sK4(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1406,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1582,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_11])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1409,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1986,plain,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_1409])).

cnf(c_2049,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1986])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1415,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3283,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_1415])).

cnf(c_3303,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1406,c_3283])).

cnf(c_25,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1396,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3417,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3303,c_1396])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1417,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK9(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1401,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK9(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1416,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2825,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1416])).

cnf(c_4313,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1417,c_2825])).

cnf(c_4823,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_4313])).

cnf(c_18,plain,
    ( r2_hidden(sK7(X0,X1),X1)
    | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1403,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK7(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3640,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK7(X0,X1),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1416])).

cnf(c_3678,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3640])).

cnf(c_24,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1397,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3416,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3303,c_1397])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1398,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3633,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3416,c_1398])).

cnf(c_3299,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1417,c_3283])).

cnf(c_2016,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK7(X2,X0),X0)
    | ~ r2_hidden(sK7(X2,X0),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2017,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK7(X2,X0),X0) != iProver_top
    | r2_hidden(sK7(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2016])).

cnf(c_2019,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_1875,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ r2_hidden(k4_tarski(sK3(k1_relat_1(k1_xboole_0)),sK9(k1_xboole_0,sK3(k1_relat_1(k1_xboole_0)))),X0)
    | ~ r2_hidden(k4_tarski(sK3(k1_relat_1(k1_xboole_0)),sK9(k1_xboole_0,sK3(k1_relat_1(k1_xboole_0)))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1877,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(k4_tarski(sK3(k1_relat_1(k1_xboole_0)),sK9(k1_xboole_0,sK3(k1_relat_1(k1_xboole_0)))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1875])).

cnf(c_1804,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK4(X0),X0)
    | ~ r2_hidden(sK4(X0),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1805,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK4(X0),X0) != iProver_top
    | r2_hidden(sK4(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1804])).

cnf(c_1807,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(sK4(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1805])).

cnf(c_862,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1784,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(k1_xboole_0))
    | k1_relat_1(k1_xboole_0) != X0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1785,plain,
    ( k1_relat_1(k1_xboole_0) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1784])).

cnf(c_1787,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_1644,plain,
    ( r2_hidden(k4_tarski(sK3(k1_relat_1(k1_xboole_0)),sK9(k1_xboole_0,sK3(k1_relat_1(k1_xboole_0)))),k1_xboole_0)
    | ~ r2_hidden(sK3(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1623,plain,
    ( r2_hidden(sK3(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1597,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1606,plain,
    ( r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_1583,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1582])).

cnf(c_1575,plain,
    ( r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1576,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1575])).

cnf(c_66,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_68,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_67,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_57,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_59,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_38,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4823,c_3678,c_3633,c_3299,c_2019,c_1877,c_1807,c_1787,c_1644,c_1623,c_1606,c_1583,c_1576,c_68,c_67,c_59,c_38,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.04/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.02  
% 2.04/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.04/1.02  
% 2.04/1.02  ------  iProver source info
% 2.04/1.02  
% 2.04/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.04/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.04/1.02  git: non_committed_changes: false
% 2.04/1.02  git: last_make_outside_of_git: false
% 2.04/1.02  
% 2.04/1.02  ------ 
% 2.04/1.02  
% 2.04/1.02  ------ Input Options
% 2.04/1.02  
% 2.04/1.02  --out_options                           all
% 2.04/1.02  --tptp_safe_out                         true
% 2.04/1.02  --problem_path                          ""
% 2.04/1.02  --include_path                          ""
% 2.04/1.02  --clausifier                            res/vclausify_rel
% 2.04/1.02  --clausifier_options                    --mode clausify
% 2.04/1.02  --stdin                                 false
% 2.04/1.02  --stats_out                             all
% 2.04/1.02  
% 2.04/1.02  ------ General Options
% 2.04/1.02  
% 2.04/1.02  --fof                                   false
% 2.04/1.02  --time_out_real                         305.
% 2.04/1.02  --time_out_virtual                      -1.
% 2.04/1.02  --symbol_type_check                     false
% 2.04/1.02  --clausify_out                          false
% 2.04/1.02  --sig_cnt_out                           false
% 2.04/1.02  --trig_cnt_out                          false
% 2.04/1.02  --trig_cnt_out_tolerance                1.
% 2.04/1.02  --trig_cnt_out_sk_spl                   false
% 2.04/1.02  --abstr_cl_out                          false
% 2.04/1.02  
% 2.04/1.02  ------ Global Options
% 2.04/1.02  
% 2.04/1.02  --schedule                              default
% 2.04/1.02  --add_important_lit                     false
% 2.04/1.02  --prop_solver_per_cl                    1000
% 2.04/1.02  --min_unsat_core                        false
% 2.04/1.02  --soft_assumptions                      false
% 2.04/1.02  --soft_lemma_size                       3
% 2.04/1.02  --prop_impl_unit_size                   0
% 2.04/1.02  --prop_impl_unit                        []
% 2.04/1.02  --share_sel_clauses                     true
% 2.04/1.02  --reset_solvers                         false
% 2.04/1.02  --bc_imp_inh                            [conj_cone]
% 2.04/1.02  --conj_cone_tolerance                   3.
% 2.04/1.02  --extra_neg_conj                        none
% 2.04/1.02  --large_theory_mode                     true
% 2.04/1.02  --prolific_symb_bound                   200
% 2.04/1.02  --lt_threshold                          2000
% 2.04/1.02  --clause_weak_htbl                      true
% 2.04/1.02  --gc_record_bc_elim                     false
% 2.04/1.02  
% 2.04/1.02  ------ Preprocessing Options
% 2.04/1.02  
% 2.04/1.02  --preprocessing_flag                    true
% 2.04/1.02  --time_out_prep_mult                    0.1
% 2.04/1.02  --splitting_mode                        input
% 2.04/1.02  --splitting_grd                         true
% 2.04/1.02  --splitting_cvd                         false
% 2.04/1.02  --splitting_cvd_svl                     false
% 2.04/1.02  --splitting_nvd                         32
% 2.04/1.02  --sub_typing                            true
% 2.04/1.02  --prep_gs_sim                           true
% 2.04/1.02  --prep_unflatten                        true
% 2.04/1.02  --prep_res_sim                          true
% 2.04/1.02  --prep_upred                            true
% 2.04/1.02  --prep_sem_filter                       exhaustive
% 2.04/1.02  --prep_sem_filter_out                   false
% 2.04/1.02  --pred_elim                             true
% 2.04/1.02  --res_sim_input                         true
% 2.04/1.02  --eq_ax_congr_red                       true
% 2.04/1.02  --pure_diseq_elim                       true
% 2.04/1.02  --brand_transform                       false
% 2.04/1.02  --non_eq_to_eq                          false
% 2.04/1.02  --prep_def_merge                        true
% 2.04/1.02  --prep_def_merge_prop_impl              false
% 2.04/1.02  --prep_def_merge_mbd                    true
% 2.04/1.02  --prep_def_merge_tr_red                 false
% 2.04/1.02  --prep_def_merge_tr_cl                  false
% 2.04/1.02  --smt_preprocessing                     true
% 2.04/1.02  --smt_ac_axioms                         fast
% 2.04/1.02  --preprocessed_out                      false
% 2.04/1.02  --preprocessed_stats                    false
% 2.04/1.02  
% 2.04/1.02  ------ Abstraction refinement Options
% 2.04/1.02  
% 2.04/1.02  --abstr_ref                             []
% 2.04/1.02  --abstr_ref_prep                        false
% 2.04/1.02  --abstr_ref_until_sat                   false
% 2.04/1.02  --abstr_ref_sig_restrict                funpre
% 2.04/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/1.02  --abstr_ref_under                       []
% 2.04/1.02  
% 2.04/1.02  ------ SAT Options
% 2.04/1.02  
% 2.04/1.02  --sat_mode                              false
% 2.04/1.02  --sat_fm_restart_options                ""
% 2.04/1.02  --sat_gr_def                            false
% 2.04/1.02  --sat_epr_types                         true
% 2.04/1.02  --sat_non_cyclic_types                  false
% 2.04/1.02  --sat_finite_models                     false
% 2.04/1.02  --sat_fm_lemmas                         false
% 2.04/1.02  --sat_fm_prep                           false
% 2.04/1.02  --sat_fm_uc_incr                        true
% 2.04/1.02  --sat_out_model                         small
% 2.04/1.02  --sat_out_clauses                       false
% 2.04/1.02  
% 2.04/1.02  ------ QBF Options
% 2.04/1.02  
% 2.04/1.02  --qbf_mode                              false
% 2.04/1.02  --qbf_elim_univ                         false
% 2.04/1.02  --qbf_dom_inst                          none
% 2.04/1.02  --qbf_dom_pre_inst                      false
% 2.04/1.02  --qbf_sk_in                             false
% 2.04/1.02  --qbf_pred_elim                         true
% 2.04/1.02  --qbf_split                             512
% 2.04/1.02  
% 2.04/1.02  ------ BMC1 Options
% 2.04/1.02  
% 2.04/1.02  --bmc1_incremental                      false
% 2.04/1.02  --bmc1_axioms                           reachable_all
% 2.04/1.02  --bmc1_min_bound                        0
% 2.04/1.02  --bmc1_max_bound                        -1
% 2.04/1.02  --bmc1_max_bound_default                -1
% 2.04/1.02  --bmc1_symbol_reachability              true
% 2.04/1.02  --bmc1_property_lemmas                  false
% 2.04/1.02  --bmc1_k_induction                      false
% 2.04/1.02  --bmc1_non_equiv_states                 false
% 2.04/1.02  --bmc1_deadlock                         false
% 2.04/1.02  --bmc1_ucm                              false
% 2.04/1.02  --bmc1_add_unsat_core                   none
% 2.04/1.02  --bmc1_unsat_core_children              false
% 2.04/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/1.02  --bmc1_out_stat                         full
% 2.04/1.02  --bmc1_ground_init                      false
% 2.04/1.02  --bmc1_pre_inst_next_state              false
% 2.04/1.02  --bmc1_pre_inst_state                   false
% 2.04/1.02  --bmc1_pre_inst_reach_state             false
% 2.04/1.02  --bmc1_out_unsat_core                   false
% 2.04/1.02  --bmc1_aig_witness_out                  false
% 2.04/1.02  --bmc1_verbose                          false
% 2.04/1.02  --bmc1_dump_clauses_tptp                false
% 2.04/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.04/1.02  --bmc1_dump_file                        -
% 2.04/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.04/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.04/1.02  --bmc1_ucm_extend_mode                  1
% 2.04/1.02  --bmc1_ucm_init_mode                    2
% 2.04/1.02  --bmc1_ucm_cone_mode                    none
% 2.04/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.04/1.02  --bmc1_ucm_relax_model                  4
% 2.04/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.04/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/1.02  --bmc1_ucm_layered_model                none
% 2.04/1.02  --bmc1_ucm_max_lemma_size               10
% 2.04/1.02  
% 2.04/1.02  ------ AIG Options
% 2.04/1.02  
% 2.04/1.02  --aig_mode                              false
% 2.04/1.02  
% 2.04/1.02  ------ Instantiation Options
% 2.04/1.02  
% 2.04/1.02  --instantiation_flag                    true
% 2.04/1.02  --inst_sos_flag                         false
% 2.04/1.02  --inst_sos_phase                        true
% 2.04/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/1.02  --inst_lit_sel_side                     num_symb
% 2.04/1.02  --inst_solver_per_active                1400
% 2.04/1.02  --inst_solver_calls_frac                1.
% 2.04/1.02  --inst_passive_queue_type               priority_queues
% 2.04/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/1.02  --inst_passive_queues_freq              [25;2]
% 2.04/1.02  --inst_dismatching                      true
% 2.04/1.02  --inst_eager_unprocessed_to_passive     true
% 2.04/1.02  --inst_prop_sim_given                   true
% 2.04/1.02  --inst_prop_sim_new                     false
% 2.04/1.02  --inst_subs_new                         false
% 2.04/1.02  --inst_eq_res_simp                      false
% 2.04/1.02  --inst_subs_given                       false
% 2.04/1.02  --inst_orphan_elimination               true
% 2.04/1.02  --inst_learning_loop_flag               true
% 2.04/1.02  --inst_learning_start                   3000
% 2.04/1.02  --inst_learning_factor                  2
% 2.04/1.02  --inst_start_prop_sim_after_learn       3
% 2.04/1.02  --inst_sel_renew                        solver
% 2.04/1.02  --inst_lit_activity_flag                true
% 2.04/1.02  --inst_restr_to_given                   false
% 2.04/1.02  --inst_activity_threshold               500
% 2.04/1.02  --inst_out_proof                        true
% 2.04/1.02  
% 2.04/1.02  ------ Resolution Options
% 2.04/1.02  
% 2.04/1.02  --resolution_flag                       true
% 2.04/1.02  --res_lit_sel                           adaptive
% 2.04/1.02  --res_lit_sel_side                      none
% 2.04/1.02  --res_ordering                          kbo
% 2.04/1.02  --res_to_prop_solver                    active
% 2.04/1.02  --res_prop_simpl_new                    false
% 2.04/1.02  --res_prop_simpl_given                  true
% 2.04/1.02  --res_passive_queue_type                priority_queues
% 2.04/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/1.02  --res_passive_queues_freq               [15;5]
% 2.04/1.02  --res_forward_subs                      full
% 2.04/1.02  --res_backward_subs                     full
% 2.04/1.02  --res_forward_subs_resolution           true
% 2.04/1.02  --res_backward_subs_resolution          true
% 2.04/1.02  --res_orphan_elimination                true
% 2.04/1.02  --res_time_limit                        2.
% 2.04/1.02  --res_out_proof                         true
% 2.04/1.02  
% 2.04/1.02  ------ Superposition Options
% 2.04/1.02  
% 2.04/1.02  --superposition_flag                    true
% 2.04/1.02  --sup_passive_queue_type                priority_queues
% 2.04/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.04/1.02  --demod_completeness_check              fast
% 2.04/1.02  --demod_use_ground                      true
% 2.04/1.02  --sup_to_prop_solver                    passive
% 2.04/1.02  --sup_prop_simpl_new                    true
% 2.04/1.02  --sup_prop_simpl_given                  true
% 2.04/1.02  --sup_fun_splitting                     false
% 2.04/1.02  --sup_smt_interval                      50000
% 2.04/1.02  
% 2.04/1.02  ------ Superposition Simplification Setup
% 2.04/1.02  
% 2.04/1.02  --sup_indices_passive                   []
% 2.04/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_full_bw                           [BwDemod]
% 2.04/1.02  --sup_immed_triv                        [TrivRules]
% 2.04/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_immed_bw_main                     []
% 2.04/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.02  
% 2.04/1.02  ------ Combination Options
% 2.04/1.02  
% 2.04/1.02  --comb_res_mult                         3
% 2.04/1.02  --comb_sup_mult                         2
% 2.04/1.02  --comb_inst_mult                        10
% 2.04/1.02  
% 2.04/1.02  ------ Debug Options
% 2.04/1.02  
% 2.04/1.02  --dbg_backtrace                         false
% 2.04/1.02  --dbg_dump_prop_clauses                 false
% 2.04/1.02  --dbg_dump_prop_clauses_file            -
% 2.04/1.02  --dbg_out_stat                          false
% 2.04/1.02  ------ Parsing...
% 2.04/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.04/1.02  
% 2.04/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.04/1.02  
% 2.04/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.04/1.02  
% 2.04/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.04/1.02  ------ Proving...
% 2.04/1.02  ------ Problem Properties 
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  clauses                                 26
% 2.04/1.02  conjectures                             1
% 2.04/1.02  EPR                                     2
% 2.04/1.02  Horn                                    19
% 2.04/1.02  unary                                   2
% 2.04/1.02  binary                                  19
% 2.04/1.02  lits                                    55
% 2.04/1.02  lits eq                                 16
% 2.04/1.02  fd_pure                                 0
% 2.04/1.02  fd_pseudo                               0
% 2.04/1.02  fd_cond                                 1
% 2.04/1.02  fd_pseudo_cond                          2
% 2.04/1.02  AC symbols                              0
% 2.04/1.02  
% 2.04/1.02  ------ Schedule dynamic 5 is on 
% 2.04/1.02  
% 2.04/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  ------ 
% 2.04/1.02  Current options:
% 2.04/1.02  ------ 
% 2.04/1.02  
% 2.04/1.02  ------ Input Options
% 2.04/1.02  
% 2.04/1.02  --out_options                           all
% 2.04/1.02  --tptp_safe_out                         true
% 2.04/1.02  --problem_path                          ""
% 2.04/1.02  --include_path                          ""
% 2.04/1.02  --clausifier                            res/vclausify_rel
% 2.04/1.02  --clausifier_options                    --mode clausify
% 2.04/1.02  --stdin                                 false
% 2.04/1.02  --stats_out                             all
% 2.04/1.02  
% 2.04/1.02  ------ General Options
% 2.04/1.02  
% 2.04/1.02  --fof                                   false
% 2.04/1.02  --time_out_real                         305.
% 2.04/1.02  --time_out_virtual                      -1.
% 2.04/1.02  --symbol_type_check                     false
% 2.04/1.02  --clausify_out                          false
% 2.04/1.02  --sig_cnt_out                           false
% 2.04/1.02  --trig_cnt_out                          false
% 2.04/1.02  --trig_cnt_out_tolerance                1.
% 2.04/1.02  --trig_cnt_out_sk_spl                   false
% 2.04/1.02  --abstr_cl_out                          false
% 2.04/1.02  
% 2.04/1.02  ------ Global Options
% 2.04/1.02  
% 2.04/1.02  --schedule                              default
% 2.04/1.02  --add_important_lit                     false
% 2.04/1.02  --prop_solver_per_cl                    1000
% 2.04/1.02  --min_unsat_core                        false
% 2.04/1.02  --soft_assumptions                      false
% 2.04/1.02  --soft_lemma_size                       3
% 2.04/1.02  --prop_impl_unit_size                   0
% 2.04/1.02  --prop_impl_unit                        []
% 2.04/1.02  --share_sel_clauses                     true
% 2.04/1.02  --reset_solvers                         false
% 2.04/1.02  --bc_imp_inh                            [conj_cone]
% 2.04/1.02  --conj_cone_tolerance                   3.
% 2.04/1.02  --extra_neg_conj                        none
% 2.04/1.02  --large_theory_mode                     true
% 2.04/1.02  --prolific_symb_bound                   200
% 2.04/1.02  --lt_threshold                          2000
% 2.04/1.02  --clause_weak_htbl                      true
% 2.04/1.02  --gc_record_bc_elim                     false
% 2.04/1.02  
% 2.04/1.02  ------ Preprocessing Options
% 2.04/1.02  
% 2.04/1.02  --preprocessing_flag                    true
% 2.04/1.02  --time_out_prep_mult                    0.1
% 2.04/1.02  --splitting_mode                        input
% 2.04/1.02  --splitting_grd                         true
% 2.04/1.02  --splitting_cvd                         false
% 2.04/1.02  --splitting_cvd_svl                     false
% 2.04/1.02  --splitting_nvd                         32
% 2.04/1.02  --sub_typing                            true
% 2.04/1.02  --prep_gs_sim                           true
% 2.04/1.02  --prep_unflatten                        true
% 2.04/1.02  --prep_res_sim                          true
% 2.04/1.02  --prep_upred                            true
% 2.04/1.02  --prep_sem_filter                       exhaustive
% 2.04/1.02  --prep_sem_filter_out                   false
% 2.04/1.02  --pred_elim                             true
% 2.04/1.02  --res_sim_input                         true
% 2.04/1.02  --eq_ax_congr_red                       true
% 2.04/1.02  --pure_diseq_elim                       true
% 2.04/1.02  --brand_transform                       false
% 2.04/1.02  --non_eq_to_eq                          false
% 2.04/1.02  --prep_def_merge                        true
% 2.04/1.02  --prep_def_merge_prop_impl              false
% 2.04/1.02  --prep_def_merge_mbd                    true
% 2.04/1.02  --prep_def_merge_tr_red                 false
% 2.04/1.02  --prep_def_merge_tr_cl                  false
% 2.04/1.02  --smt_preprocessing                     true
% 2.04/1.02  --smt_ac_axioms                         fast
% 2.04/1.02  --preprocessed_out                      false
% 2.04/1.02  --preprocessed_stats                    false
% 2.04/1.02  
% 2.04/1.02  ------ Abstraction refinement Options
% 2.04/1.02  
% 2.04/1.02  --abstr_ref                             []
% 2.04/1.02  --abstr_ref_prep                        false
% 2.04/1.02  --abstr_ref_until_sat                   false
% 2.04/1.02  --abstr_ref_sig_restrict                funpre
% 2.04/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/1.02  --abstr_ref_under                       []
% 2.04/1.02  
% 2.04/1.02  ------ SAT Options
% 2.04/1.02  
% 2.04/1.02  --sat_mode                              false
% 2.04/1.02  --sat_fm_restart_options                ""
% 2.04/1.02  --sat_gr_def                            false
% 2.04/1.02  --sat_epr_types                         true
% 2.04/1.02  --sat_non_cyclic_types                  false
% 2.04/1.02  --sat_finite_models                     false
% 2.04/1.02  --sat_fm_lemmas                         false
% 2.04/1.02  --sat_fm_prep                           false
% 2.04/1.02  --sat_fm_uc_incr                        true
% 2.04/1.02  --sat_out_model                         small
% 2.04/1.02  --sat_out_clauses                       false
% 2.04/1.02  
% 2.04/1.02  ------ QBF Options
% 2.04/1.02  
% 2.04/1.02  --qbf_mode                              false
% 2.04/1.02  --qbf_elim_univ                         false
% 2.04/1.02  --qbf_dom_inst                          none
% 2.04/1.02  --qbf_dom_pre_inst                      false
% 2.04/1.02  --qbf_sk_in                             false
% 2.04/1.02  --qbf_pred_elim                         true
% 2.04/1.02  --qbf_split                             512
% 2.04/1.02  
% 2.04/1.02  ------ BMC1 Options
% 2.04/1.02  
% 2.04/1.02  --bmc1_incremental                      false
% 2.04/1.02  --bmc1_axioms                           reachable_all
% 2.04/1.02  --bmc1_min_bound                        0
% 2.04/1.02  --bmc1_max_bound                        -1
% 2.04/1.02  --bmc1_max_bound_default                -1
% 2.04/1.02  --bmc1_symbol_reachability              true
% 2.04/1.02  --bmc1_property_lemmas                  false
% 2.04/1.02  --bmc1_k_induction                      false
% 2.04/1.02  --bmc1_non_equiv_states                 false
% 2.04/1.02  --bmc1_deadlock                         false
% 2.04/1.02  --bmc1_ucm                              false
% 2.04/1.02  --bmc1_add_unsat_core                   none
% 2.04/1.02  --bmc1_unsat_core_children              false
% 2.04/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/1.02  --bmc1_out_stat                         full
% 2.04/1.02  --bmc1_ground_init                      false
% 2.04/1.02  --bmc1_pre_inst_next_state              false
% 2.04/1.02  --bmc1_pre_inst_state                   false
% 2.04/1.02  --bmc1_pre_inst_reach_state             false
% 2.04/1.02  --bmc1_out_unsat_core                   false
% 2.04/1.02  --bmc1_aig_witness_out                  false
% 2.04/1.02  --bmc1_verbose                          false
% 2.04/1.02  --bmc1_dump_clauses_tptp                false
% 2.04/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.04/1.02  --bmc1_dump_file                        -
% 2.04/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.04/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.04/1.02  --bmc1_ucm_extend_mode                  1
% 2.04/1.02  --bmc1_ucm_init_mode                    2
% 2.04/1.02  --bmc1_ucm_cone_mode                    none
% 2.04/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.04/1.02  --bmc1_ucm_relax_model                  4
% 2.04/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.04/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/1.02  --bmc1_ucm_layered_model                none
% 2.04/1.02  --bmc1_ucm_max_lemma_size               10
% 2.04/1.02  
% 2.04/1.02  ------ AIG Options
% 2.04/1.02  
% 2.04/1.02  --aig_mode                              false
% 2.04/1.02  
% 2.04/1.02  ------ Instantiation Options
% 2.04/1.02  
% 2.04/1.02  --instantiation_flag                    true
% 2.04/1.02  --inst_sos_flag                         false
% 2.04/1.02  --inst_sos_phase                        true
% 2.04/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/1.02  --inst_lit_sel_side                     none
% 2.04/1.02  --inst_solver_per_active                1400
% 2.04/1.02  --inst_solver_calls_frac                1.
% 2.04/1.02  --inst_passive_queue_type               priority_queues
% 2.04/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/1.02  --inst_passive_queues_freq              [25;2]
% 2.04/1.02  --inst_dismatching                      true
% 2.04/1.02  --inst_eager_unprocessed_to_passive     true
% 2.04/1.02  --inst_prop_sim_given                   true
% 2.04/1.02  --inst_prop_sim_new                     false
% 2.04/1.02  --inst_subs_new                         false
% 2.04/1.02  --inst_eq_res_simp                      false
% 2.04/1.02  --inst_subs_given                       false
% 2.04/1.02  --inst_orphan_elimination               true
% 2.04/1.02  --inst_learning_loop_flag               true
% 2.04/1.02  --inst_learning_start                   3000
% 2.04/1.02  --inst_learning_factor                  2
% 2.04/1.02  --inst_start_prop_sim_after_learn       3
% 2.04/1.02  --inst_sel_renew                        solver
% 2.04/1.02  --inst_lit_activity_flag                true
% 2.04/1.02  --inst_restr_to_given                   false
% 2.04/1.02  --inst_activity_threshold               500
% 2.04/1.02  --inst_out_proof                        true
% 2.04/1.02  
% 2.04/1.02  ------ Resolution Options
% 2.04/1.02  
% 2.04/1.02  --resolution_flag                       false
% 2.04/1.02  --res_lit_sel                           adaptive
% 2.04/1.02  --res_lit_sel_side                      none
% 2.04/1.02  --res_ordering                          kbo
% 2.04/1.02  --res_to_prop_solver                    active
% 2.04/1.02  --res_prop_simpl_new                    false
% 2.04/1.02  --res_prop_simpl_given                  true
% 2.04/1.02  --res_passive_queue_type                priority_queues
% 2.04/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/1.02  --res_passive_queues_freq               [15;5]
% 2.04/1.02  --res_forward_subs                      full
% 2.04/1.02  --res_backward_subs                     full
% 2.04/1.02  --res_forward_subs_resolution           true
% 2.04/1.02  --res_backward_subs_resolution          true
% 2.04/1.02  --res_orphan_elimination                true
% 2.04/1.02  --res_time_limit                        2.
% 2.04/1.02  --res_out_proof                         true
% 2.04/1.02  
% 2.04/1.02  ------ Superposition Options
% 2.04/1.02  
% 2.04/1.02  --superposition_flag                    true
% 2.04/1.02  --sup_passive_queue_type                priority_queues
% 2.04/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.04/1.02  --demod_completeness_check              fast
% 2.04/1.02  --demod_use_ground                      true
% 2.04/1.02  --sup_to_prop_solver                    passive
% 2.04/1.02  --sup_prop_simpl_new                    true
% 2.04/1.02  --sup_prop_simpl_given                  true
% 2.04/1.02  --sup_fun_splitting                     false
% 2.04/1.02  --sup_smt_interval                      50000
% 2.04/1.02  
% 2.04/1.02  ------ Superposition Simplification Setup
% 2.04/1.02  
% 2.04/1.02  --sup_indices_passive                   []
% 2.04/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_full_bw                           [BwDemod]
% 2.04/1.02  --sup_immed_triv                        [TrivRules]
% 2.04/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_immed_bw_main                     []
% 2.04/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.02  
% 2.04/1.02  ------ Combination Options
% 2.04/1.02  
% 2.04/1.02  --comb_res_mult                         3
% 2.04/1.02  --comb_sup_mult                         2
% 2.04/1.02  --comb_inst_mult                        10
% 2.04/1.02  
% 2.04/1.02  ------ Debug Options
% 2.04/1.02  
% 2.04/1.02  --dbg_backtrace                         false
% 2.04/1.02  --dbg_dump_prop_clauses                 false
% 2.04/1.02  --dbg_dump_prop_clauses_file            -
% 2.04/1.02  --dbg_out_stat                          false
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  ------ Proving...
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  % SZS status Theorem for theBenchmark.p
% 2.04/1.02  
% 2.04/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.04/1.02  
% 2.04/1.02  fof(f13,axiom,(
% 2.04/1.02    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f29,plain,(
% 2.04/1.02    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 2.04/1.02    inference(ennf_transformation,[],[f13])).
% 2.04/1.02  
% 2.04/1.02  fof(f47,plain,(
% 2.04/1.02    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 2.04/1.02    inference(nnf_transformation,[],[f29])).
% 2.04/1.02  
% 2.04/1.02  fof(f48,plain,(
% 2.04/1.02    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 2.04/1.02    inference(rectify,[],[f47])).
% 2.04/1.02  
% 2.04/1.02  fof(f50,plain,(
% 2.04/1.02    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK5(X4),sK6(X4)) = X4)),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f49,plain,(
% 2.04/1.02    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK4(X0) & r2_hidden(sK4(X0),X0)))),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f51,plain,(
% 2.04/1.02    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK4(X0) & r2_hidden(sK4(X0),X0))) & (! [X4] : (k4_tarski(sK5(X4),sK6(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 2.04/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f48,f50,f49])).
% 2.04/1.02  
% 2.04/1.02  fof(f76,plain,(
% 2.04/1.02    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK4(X0),X0)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f51])).
% 2.04/1.02  
% 2.04/1.02  fof(f6,axiom,(
% 2.04/1.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f67,plain,(
% 2.04/1.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.04/1.02    inference(cnf_transformation,[],[f6])).
% 2.04/1.02  
% 2.04/1.02  fof(f8,axiom,(
% 2.04/1.02    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f69,plain,(
% 2.04/1.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.04/1.02    inference(cnf_transformation,[],[f8])).
% 2.04/1.02  
% 2.04/1.02  fof(f9,axiom,(
% 2.04/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f46,plain,(
% 2.04/1.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.04/1.02    inference(nnf_transformation,[],[f9])).
% 2.04/1.02  
% 2.04/1.02  fof(f71,plain,(
% 2.04/1.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.04/1.02    inference(cnf_transformation,[],[f46])).
% 2.04/1.02  
% 2.04/1.02  fof(f2,axiom,(
% 2.04/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f21,plain,(
% 2.04/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.04/1.02    inference(rectify,[],[f2])).
% 2.04/1.02  
% 2.04/1.02  fof(f24,plain,(
% 2.04/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.04/1.02    inference(ennf_transformation,[],[f21])).
% 2.04/1.02  
% 2.04/1.02  fof(f40,plain,(
% 2.04/1.02    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f41,plain,(
% 2.04/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.04/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f40])).
% 2.04/1.02  
% 2.04/1.02  fof(f62,plain,(
% 2.04/1.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f41])).
% 2.04/1.02  
% 2.04/1.02  fof(f18,axiom,(
% 2.04/1.02    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f34,plain,(
% 2.04/1.02    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.04/1.02    inference(ennf_transformation,[],[f18])).
% 2.04/1.02  
% 2.04/1.02  fof(f85,plain,(
% 2.04/1.02    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f34])).
% 2.04/1.02  
% 2.04/1.02  fof(f1,axiom,(
% 2.04/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f36,plain,(
% 2.04/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.04/1.02    inference(nnf_transformation,[],[f1])).
% 2.04/1.02  
% 2.04/1.02  fof(f37,plain,(
% 2.04/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.04/1.02    inference(rectify,[],[f36])).
% 2.04/1.02  
% 2.04/1.02  fof(f38,plain,(
% 2.04/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f39,plain,(
% 2.04/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.04/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.04/1.02  
% 2.04/1.02  fof(f59,plain,(
% 2.04/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f39])).
% 2.04/1.02  
% 2.04/1.02  fof(f14,axiom,(
% 2.04/1.02    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f52,plain,(
% 2.04/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.04/1.02    inference(nnf_transformation,[],[f14])).
% 2.04/1.02  
% 2.04/1.02  fof(f53,plain,(
% 2.04/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.04/1.02    inference(rectify,[],[f52])).
% 2.04/1.02  
% 2.04/1.02  fof(f56,plain,(
% 2.04/1.02    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0))),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f55,plain,(
% 2.04/1.02    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK8(X0,X1)),X0))) )),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f54,plain,(
% 2.04/1.02    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f57,plain,(
% 2.04/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.04/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f53,f56,f55,f54])).
% 2.04/1.02  
% 2.04/1.02  fof(f78,plain,(
% 2.04/1.02    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.04/1.02    inference(cnf_transformation,[],[f57])).
% 2.04/1.02  
% 2.04/1.02  fof(f94,plain,(
% 2.04/1.02    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.04/1.02    inference(equality_resolution,[],[f78])).
% 2.04/1.02  
% 2.04/1.02  fof(f58,plain,(
% 2.04/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f39])).
% 2.04/1.02  
% 2.04/1.02  fof(f80,plain,(
% 2.04/1.02    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f57])).
% 2.04/1.02  
% 2.04/1.02  fof(f86,plain,(
% 2.04/1.02    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f34])).
% 2.04/1.02  
% 2.04/1.02  fof(f17,axiom,(
% 2.04/1.02    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f32,plain,(
% 2.04/1.02    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 2.04/1.02    inference(ennf_transformation,[],[f17])).
% 2.04/1.02  
% 2.04/1.02  fof(f33,plain,(
% 2.04/1.02    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 2.04/1.02    inference(flattening,[],[f32])).
% 2.04/1.02  
% 2.04/1.02  fof(f84,plain,(
% 2.04/1.02    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f33])).
% 2.04/1.02  
% 2.04/1.02  fof(f4,axiom,(
% 2.04/1.02    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f26,plain,(
% 2.04/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.04/1.02    inference(ennf_transformation,[],[f4])).
% 2.04/1.02  
% 2.04/1.02  fof(f44,plain,(
% 2.04/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f45,plain,(
% 2.04/1.02    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.04/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f44])).
% 2.04/1.02  
% 2.04/1.02  fof(f65,plain,(
% 2.04/1.02    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.04/1.02    inference(cnf_transformation,[],[f45])).
% 2.04/1.02  
% 2.04/1.02  fof(f16,axiom,(
% 2.04/1.02    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f31,plain,(
% 2.04/1.02    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.04/1.02    inference(ennf_transformation,[],[f16])).
% 2.04/1.02  
% 2.04/1.02  fof(f83,plain,(
% 2.04/1.02    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f31])).
% 2.04/1.02  
% 2.04/1.02  fof(f19,conjecture,(
% 2.04/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f20,negated_conjecture,(
% 2.04/1.02    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 2.04/1.02    inference(negated_conjecture,[],[f19])).
% 2.04/1.02  
% 2.04/1.02  fof(f35,plain,(
% 2.04/1.02    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.04/1.02    inference(ennf_transformation,[],[f20])).
% 2.04/1.02  
% 2.04/1.02  fof(f87,plain,(
% 2.04/1.02    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.04/1.02    inference(cnf_transformation,[],[f35])).
% 2.04/1.02  
% 2.04/1.02  cnf(c_15,plain,
% 2.04/1.02      ( r2_hidden(sK4(X0),X0) | v1_relat_1(X0) ),
% 2.04/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1406,plain,
% 2.04/1.02      ( r2_hidden(sK4(X0),X0) = iProver_top
% 2.04/1.02      | v1_relat_1(X0) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_9,plain,
% 2.04/1.02      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.04/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_11,plain,
% 2.04/1.02      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.04/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1582,plain,
% 2.04/1.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_9,c_11]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_12,plain,
% 2.04/1.02      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.04/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1409,plain,
% 2.04/1.02      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1986,plain,
% 2.04/1.02      ( k1_xboole_0 != X0 | r1_xboole_0(X0,X0) = iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1582,c_1409]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2049,plain,
% 2.04/1.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.04/1.02      inference(equality_resolution,[status(thm)],[c_1986]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2,plain,
% 2.04/1.02      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 2.04/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1415,plain,
% 2.04/1.02      ( r1_xboole_0(X0,X1) != iProver_top
% 2.04/1.02      | r2_hidden(X2,X0) != iProver_top
% 2.04/1.02      | r2_hidden(X2,X1) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3283,plain,
% 2.04/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_2049,c_1415]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3303,plain,
% 2.04/1.02      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1406,c_3283]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_25,plain,
% 2.04/1.02      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.04/1.02      inference(cnf_transformation,[],[f85]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1396,plain,
% 2.04/1.02      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 2.04/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3417,plain,
% 2.04/1.02      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_3303,c_1396]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_0,plain,
% 2.04/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.04/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1417,plain,
% 2.04/1.02      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.04/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_20,plain,
% 2.04/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.04/1.02      | r2_hidden(k4_tarski(X0,sK9(X1,X0)),X1) ),
% 2.04/1.02      inference(cnf_transformation,[],[f94]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1401,plain,
% 2.04/1.02      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(X0,sK9(X1,X0)),X1) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1,plain,
% 2.04/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.04/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1416,plain,
% 2.04/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.04/1.02      | v1_xboole_0(X1) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2825,plain,
% 2.04/1.02      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.04/1.02      | v1_xboole_0(X1) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1401,c_1416]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_4313,plain,
% 2.04/1.02      ( v1_xboole_0(X0) != iProver_top
% 2.04/1.02      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1417,c_2825]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_4823,plain,
% 2.04/1.02      ( v1_xboole_0(k4_relat_1(k1_xboole_0)) != iProver_top
% 2.04/1.02      | v1_xboole_0(k2_relat_1(k1_xboole_0)) = iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_3417,c_4313]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_18,plain,
% 2.04/1.02      ( r2_hidden(sK7(X0,X1),X1)
% 2.04/1.02      | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
% 2.04/1.02      | k1_relat_1(X0) = X1 ),
% 2.04/1.02      inference(cnf_transformation,[],[f80]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1403,plain,
% 2.04/1.02      ( k1_relat_1(X0) = X1
% 2.04/1.02      | r2_hidden(sK7(X0,X1),X1) = iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3640,plain,
% 2.04/1.02      ( k1_relat_1(X0) = X1
% 2.04/1.02      | r2_hidden(sK7(X0,X1),X1) = iProver_top
% 2.04/1.02      | v1_xboole_0(X0) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1403,c_1416]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3678,plain,
% 2.04/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 2.04/1.02      | r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
% 2.04/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_3640]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_24,plain,
% 2.04/1.02      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.04/1.02      inference(cnf_transformation,[],[f86]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1397,plain,
% 2.04/1.02      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 2.04/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3416,plain,
% 2.04/1.02      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_3303,c_1397]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_23,plain,
% 2.04/1.02      ( ~ v1_relat_1(X0)
% 2.04/1.02      | v1_xboole_0(X0)
% 2.04/1.02      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 2.04/1.02      inference(cnf_transformation,[],[f84]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1398,plain,
% 2.04/1.02      ( v1_relat_1(X0) != iProver_top
% 2.04/1.02      | v1_xboole_0(X0) = iProver_top
% 2.04/1.02      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3633,plain,
% 2.04/1.02      ( v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
% 2.04/1.02      | v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top
% 2.04/1.02      | v1_xboole_0(k1_relat_1(k1_xboole_0)) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_3416,c_1398]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3299,plain,
% 2.04/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1417,c_3283]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2016,plain,
% 2.04/1.02      ( ~ r1_xboole_0(X0,X1)
% 2.04/1.02      | ~ r2_hidden(sK7(X2,X0),X0)
% 2.04/1.02      | ~ r2_hidden(sK7(X2,X0),X1) ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2017,plain,
% 2.04/1.02      ( r1_xboole_0(X0,X1) != iProver_top
% 2.04/1.02      | r2_hidden(sK7(X2,X0),X0) != iProver_top
% 2.04/1.02      | r2_hidden(sK7(X2,X0),X1) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_2016]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2019,plain,
% 2.04/1.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.04/1.02      | r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_2017]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1875,plain,
% 2.04/1.02      ( ~ r1_xboole_0(k1_xboole_0,X0)
% 2.04/1.02      | ~ r2_hidden(k4_tarski(sK3(k1_relat_1(k1_xboole_0)),sK9(k1_xboole_0,sK3(k1_relat_1(k1_xboole_0)))),X0)
% 2.04/1.02      | ~ r2_hidden(k4_tarski(sK3(k1_relat_1(k1_xboole_0)),sK9(k1_xboole_0,sK3(k1_relat_1(k1_xboole_0)))),k1_xboole_0) ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1877,plain,
% 2.04/1.02      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.04/1.02      | ~ r2_hidden(k4_tarski(sK3(k1_relat_1(k1_xboole_0)),sK9(k1_xboole_0,sK3(k1_relat_1(k1_xboole_0)))),k1_xboole_0) ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_1875]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1804,plain,
% 2.04/1.02      ( ~ r1_xboole_0(X0,X1)
% 2.04/1.02      | ~ r2_hidden(sK4(X0),X0)
% 2.04/1.02      | ~ r2_hidden(sK4(X0),X1) ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1805,plain,
% 2.04/1.02      ( r1_xboole_0(X0,X1) != iProver_top
% 2.04/1.02      | r2_hidden(sK4(X0),X0) != iProver_top
% 2.04/1.02      | r2_hidden(sK4(X0),X1) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_1804]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1807,plain,
% 2.04/1.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.04/1.02      | r2_hidden(sK4(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_1805]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_862,plain,
% 2.04/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.04/1.02      theory(equality) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1784,plain,
% 2.04/1.02      ( ~ v1_xboole_0(X0)
% 2.04/1.02      | v1_xboole_0(k1_relat_1(k1_xboole_0))
% 2.04/1.02      | k1_relat_1(k1_xboole_0) != X0 ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_862]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1785,plain,
% 2.04/1.02      ( k1_relat_1(k1_xboole_0) != X0
% 2.04/1.02      | v1_xboole_0(X0) != iProver_top
% 2.04/1.02      | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_1784]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1787,plain,
% 2.04/1.02      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.04/1.02      | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top
% 2.04/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.04/1.03      inference(instantiation,[status(thm)],[c_1785]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_1644,plain,
% 2.04/1.03      ( r2_hidden(k4_tarski(sK3(k1_relat_1(k1_xboole_0)),sK9(k1_xboole_0,sK3(k1_relat_1(k1_xboole_0)))),k1_xboole_0)
% 2.04/1.03      | ~ r2_hidden(sK3(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
% 2.04/1.03      inference(instantiation,[status(thm)],[c_20]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_7,plain,
% 2.04/1.03      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 2.04/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_1623,plain,
% 2.04/1.03      ( r2_hidden(sK3(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))
% 2.04/1.03      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 2.04/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_1597,plain,
% 2.04/1.03      ( ~ r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
% 2.04/1.03      | ~ v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
% 2.04/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_1606,plain,
% 2.04/1.03      ( r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) != iProver_top
% 2.04/1.03      | v1_xboole_0(k2_relat_1(k1_xboole_0)) != iProver_top ),
% 2.04/1.03      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_1583,plain,
% 2.04/1.03      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.04/1.03      inference(instantiation,[status(thm)],[c_1582]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_1575,plain,
% 2.04/1.03      ( r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
% 2.04/1.03      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 2.04/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_1576,plain,
% 2.04/1.03      ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 2.04/1.03      | r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) = iProver_top ),
% 2.04/1.03      inference(predicate_to_equality,[status(thm)],[c_1575]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_66,plain,
% 2.04/1.03      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.04/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_68,plain,
% 2.04/1.03      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.04/1.03      | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.04/1.03      inference(instantiation,[status(thm)],[c_66]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_67,plain,
% 2.04/1.03      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.04/1.03      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.04/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_57,plain,
% 2.04/1.03      ( r2_hidden(sK4(X0),X0) = iProver_top
% 2.04/1.03      | v1_relat_1(X0) = iProver_top ),
% 2.04/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_59,plain,
% 2.04/1.03      ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0) = iProver_top
% 2.04/1.03      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.04/1.03      inference(instantiation,[status(thm)],[c_57]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_22,plain,
% 2.04/1.03      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 2.04/1.03      inference(cnf_transformation,[],[f83]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_36,plain,
% 2.04/1.03      ( v1_relat_1(X0) != iProver_top
% 2.04/1.03      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 2.04/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_38,plain,
% 2.04/1.03      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 2.04/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.04/1.03      inference(instantiation,[status(thm)],[c_36]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(c_26,negated_conjecture,
% 2.04/1.03      ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
% 2.04/1.03      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.04/1.03      inference(cnf_transformation,[],[f87]) ).
% 2.04/1.03  
% 2.04/1.03  cnf(contradiction,plain,
% 2.04/1.03      ( $false ),
% 2.04/1.03      inference(minisat,
% 2.04/1.03                [status(thm)],
% 2.04/1.03                [c_4823,c_3678,c_3633,c_3299,c_2019,c_1877,c_1807,c_1787,
% 2.04/1.03                 c_1644,c_1623,c_1606,c_1583,c_1576,c_68,c_67,c_59,c_38,
% 2.04/1.03                 c_26]) ).
% 2.04/1.03  
% 2.04/1.03  
% 2.04/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.04/1.03  
% 2.04/1.03  ------                               Statistics
% 2.04/1.03  
% 2.04/1.03  ------ General
% 2.04/1.03  
% 2.04/1.03  abstr_ref_over_cycles:                  0
% 2.04/1.03  abstr_ref_under_cycles:                 0
% 2.04/1.03  gc_basic_clause_elim:                   0
% 2.04/1.03  forced_gc_time:                         0
% 2.04/1.03  parsing_time:                           0.008
% 2.04/1.03  unif_index_cands_time:                  0.
% 2.04/1.03  unif_index_add_time:                    0.
% 2.04/1.03  orderings_time:                         0.
% 2.04/1.03  out_proof_time:                         0.01
% 2.04/1.03  total_time:                             0.132
% 2.04/1.03  num_of_symbols:                         56
% 2.04/1.03  num_of_terms:                           3845
% 2.04/1.03  
% 2.04/1.03  ------ Preprocessing
% 2.04/1.03  
% 2.04/1.03  num_of_splits:                          0
% 2.04/1.03  num_of_split_atoms:                     0
% 2.04/1.03  num_of_reused_defs:                     0
% 2.04/1.03  num_eq_ax_congr_red:                    74
% 2.04/1.03  num_of_sem_filtered_clauses:            1
% 2.04/1.03  num_of_subtypes:                        0
% 2.04/1.03  monotx_restored_types:                  0
% 2.04/1.03  sat_num_of_epr_types:                   0
% 2.04/1.03  sat_num_of_non_cyclic_types:            0
% 2.04/1.03  sat_guarded_non_collapsed_types:        0
% 2.04/1.03  num_pure_diseq_elim:                    0
% 2.04/1.03  simp_replaced_by:                       0
% 2.04/1.03  res_preprocessed:                       128
% 2.04/1.03  prep_upred:                             0
% 2.04/1.03  prep_unflattend:                        0
% 2.04/1.03  smt_new_axioms:                         0
% 2.04/1.03  pred_elim_cands:                        4
% 2.04/1.03  pred_elim:                              1
% 2.04/1.03  pred_elim_cl:                           1
% 2.04/1.03  pred_elim_cycles:                       3
% 2.04/1.03  merged_defs:                            8
% 2.04/1.03  merged_defs_ncl:                        0
% 2.04/1.03  bin_hyper_res:                          8
% 2.04/1.03  prep_cycles:                            4
% 2.04/1.03  pred_elim_time:                         0.003
% 2.04/1.03  splitting_time:                         0.
% 2.04/1.03  sem_filter_time:                        0.
% 2.04/1.03  monotx_time:                            0.
% 2.04/1.03  subtype_inf_time:                       0.
% 2.04/1.03  
% 2.04/1.03  ------ Problem properties
% 2.04/1.03  
% 2.04/1.03  clauses:                                26
% 2.04/1.03  conjectures:                            1
% 2.04/1.03  epr:                                    2
% 2.04/1.03  horn:                                   19
% 2.04/1.03  ground:                                 1
% 2.04/1.03  unary:                                  2
% 2.04/1.03  binary:                                 19
% 2.04/1.03  lits:                                   55
% 2.04/1.03  lits_eq:                                16
% 2.04/1.03  fd_pure:                                0
% 2.04/1.03  fd_pseudo:                              0
% 2.04/1.03  fd_cond:                                1
% 2.04/1.03  fd_pseudo_cond:                         2
% 2.04/1.03  ac_symbols:                             0
% 2.04/1.03  
% 2.04/1.03  ------ Propositional Solver
% 2.04/1.03  
% 2.04/1.03  prop_solver_calls:                      28
% 2.04/1.03  prop_fast_solver_calls:                 721
% 2.04/1.03  smt_solver_calls:                       0
% 2.04/1.03  smt_fast_solver_calls:                  0
% 2.04/1.03  prop_num_of_clauses:                    1735
% 2.04/1.03  prop_preprocess_simplified:             6347
% 2.04/1.03  prop_fo_subsumed:                       0
% 2.04/1.03  prop_solver_time:                       0.
% 2.04/1.03  smt_solver_time:                        0.
% 2.04/1.03  smt_fast_solver_time:                   0.
% 2.04/1.03  prop_fast_solver_time:                  0.
% 2.04/1.03  prop_unsat_core_time:                   0.
% 2.04/1.03  
% 2.04/1.03  ------ QBF
% 2.04/1.03  
% 2.04/1.03  qbf_q_res:                              0
% 2.04/1.03  qbf_num_tautologies:                    0
% 2.04/1.03  qbf_prep_cycles:                        0
% 2.04/1.03  
% 2.04/1.03  ------ BMC1
% 2.04/1.03  
% 2.04/1.03  bmc1_current_bound:                     -1
% 2.04/1.03  bmc1_last_solved_bound:                 -1
% 2.04/1.03  bmc1_unsat_core_size:                   -1
% 2.04/1.03  bmc1_unsat_core_parents_size:           -1
% 2.04/1.03  bmc1_merge_next_fun:                    0
% 2.04/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.04/1.03  
% 2.04/1.03  ------ Instantiation
% 2.04/1.03  
% 2.04/1.03  inst_num_of_clauses:                    544
% 2.04/1.03  inst_num_in_passive:                    74
% 2.04/1.03  inst_num_in_active:                     250
% 2.04/1.03  inst_num_in_unprocessed:                220
% 2.04/1.03  inst_num_of_loops:                      320
% 2.04/1.03  inst_num_of_learning_restarts:          0
% 2.04/1.03  inst_num_moves_active_passive:          67
% 2.04/1.03  inst_lit_activity:                      0
% 2.04/1.03  inst_lit_activity_moves:                0
% 2.04/1.03  inst_num_tautologies:                   0
% 2.04/1.03  inst_num_prop_implied:                  0
% 2.04/1.03  inst_num_existing_simplified:           0
% 2.04/1.03  inst_num_eq_res_simplified:             0
% 2.04/1.03  inst_num_child_elim:                    0
% 2.04/1.03  inst_num_of_dismatching_blockings:      128
% 2.04/1.03  inst_num_of_non_proper_insts:           368
% 2.04/1.03  inst_num_of_duplicates:                 0
% 2.04/1.03  inst_inst_num_from_inst_to_res:         0
% 2.04/1.03  inst_dismatching_checking_time:         0.
% 2.04/1.03  
% 2.04/1.03  ------ Resolution
% 2.04/1.03  
% 2.04/1.03  res_num_of_clauses:                     0
% 2.04/1.03  res_num_in_passive:                     0
% 2.04/1.03  res_num_in_active:                      0
% 2.04/1.03  res_num_of_loops:                       132
% 2.04/1.03  res_forward_subset_subsumed:            17
% 2.04/1.03  res_backward_subset_subsumed:           0
% 2.04/1.03  res_forward_subsumed:                   0
% 2.04/1.03  res_backward_subsumed:                  0
% 2.04/1.03  res_forward_subsumption_resolution:     0
% 2.04/1.03  res_backward_subsumption_resolution:    0
% 2.04/1.03  res_clause_to_clause_subsumption:       216
% 2.04/1.03  res_orphan_elimination:                 0
% 2.04/1.03  res_tautology_del:                      63
% 2.04/1.03  res_num_eq_res_simplified:              0
% 2.04/1.03  res_num_sel_changes:                    0
% 2.04/1.03  res_moves_from_active_to_pass:          0
% 2.04/1.03  
% 2.04/1.03  ------ Superposition
% 2.04/1.03  
% 2.04/1.03  sup_time_total:                         0.
% 2.04/1.03  sup_time_generating:                    0.
% 2.04/1.03  sup_time_sim_full:                      0.
% 2.04/1.03  sup_time_sim_immed:                     0.
% 2.04/1.03  
% 2.04/1.03  sup_num_of_clauses:                     99
% 2.04/1.03  sup_num_in_active:                      60
% 2.04/1.03  sup_num_in_passive:                     39
% 2.04/1.03  sup_num_of_loops:                       62
% 2.04/1.03  sup_fw_superposition:                   68
% 2.04/1.03  sup_bw_superposition:                   44
% 2.04/1.03  sup_immediate_simplified:               20
% 2.04/1.03  sup_given_eliminated:                   1
% 2.04/1.03  comparisons_done:                       0
% 2.04/1.03  comparisons_avoided:                    0
% 2.04/1.03  
% 2.04/1.03  ------ Simplifications
% 2.04/1.03  
% 2.04/1.03  
% 2.04/1.03  sim_fw_subset_subsumed:                 5
% 2.04/1.03  sim_bw_subset_subsumed:                 0
% 2.04/1.03  sim_fw_subsumed:                        7
% 2.04/1.03  sim_bw_subsumed:                        1
% 2.04/1.03  sim_fw_subsumption_res:                 0
% 2.04/1.03  sim_bw_subsumption_res:                 0
% 2.04/1.03  sim_tautology_del:                      6
% 2.04/1.03  sim_eq_tautology_del:                   2
% 2.04/1.03  sim_eq_res_simp:                        1
% 2.04/1.03  sim_fw_demodulated:                     1
% 2.04/1.03  sim_bw_demodulated:                     6
% 2.04/1.03  sim_light_normalised:                   11
% 2.04/1.03  sim_joinable_taut:                      0
% 2.04/1.03  sim_joinable_simp:                      0
% 2.04/1.03  sim_ac_normalised:                      0
% 2.04/1.03  sim_smt_subsumption:                    0
% 2.04/1.03  
%------------------------------------------------------------------------------
