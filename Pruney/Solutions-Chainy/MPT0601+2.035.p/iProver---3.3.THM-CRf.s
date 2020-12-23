%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:25 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 411 expanded)
%              Number of clauses        :   54 ( 131 expanded)
%              Number of leaves         :   18 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  296 (1414 expanded)
%              Number of equality atoms :  126 ( 481 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f16])).

fof(f19,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f41,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK9,sK8)
        | ~ r2_hidden(sK8,k1_relat_1(sK9)) )
      & ( k1_xboole_0 != k11_relat_1(sK9,sK8)
        | r2_hidden(sK8,k1_relat_1(sK9)) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK9,sK8)
      | ~ r2_hidden(sK8,k1_relat_1(sK9)) )
    & ( k1_xboole_0 != k11_relat_1(sK9,sK8)
      | r2_hidden(sK8,k1_relat_1(sK9)) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f31,f32])).

fof(f49,plain,
    ( k1_xboole_0 = k11_relat_1(sK9,sK8)
    | ~ r2_hidden(sK8,k1_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f14,f28])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK1(X4),sK2(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,
    ( k1_xboole_0 != k11_relat_1(sK9,sK8)
    | r2_hidden(sK8,k1_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1075,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1069,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1505,plain,
    ( r2_hidden(k4_tarski(X0,sK0(k11_relat_1(X1,X0))),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k11_relat_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_1069])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1071,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2088,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k11_relat_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_1071])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK8,k1_relat_1(sK9))
    | k1_xboole_0 = k11_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1066,plain,
    ( k1_xboole_0 = k11_relat_1(sK9,sK8)
    | r2_hidden(sK8,k1_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3026,plain,
    ( k11_relat_1(sK9,sK8) = k1_xboole_0
    | v1_relat_1(k11_relat_1(sK9,sK8)) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2088,c_1066])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_enumset1(X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_206,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_enumset1(X0,X0,X2) != X3
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_207,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_1063,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_1326,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_1063])).

cnf(c_723,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1217,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k11_relat_1(sK9,sK8))
    | k11_relat_1(sK9,sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_2166,plain,
    ( v1_relat_1(k11_relat_1(sK9,sK8))
    | ~ v1_relat_1(k1_xboole_0)
    | k11_relat_1(sK9,sK8) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1217])).

cnf(c_2168,plain,
    ( k11_relat_1(sK9,sK8) != k1_xboole_0
    | v1_relat_1(k11_relat_1(sK9,sK8)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2166])).

cnf(c_3158,plain,
    ( v1_relat_1(k11_relat_1(sK9,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3026,c_15,c_1326,c_2168])).

cnf(c_11,plain,
    ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1067,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1074,plain,
    ( k4_tarski(sK1(X0),sK2(X0)) = X0
    | r2_hidden(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1418,plain,
    ( k4_tarski(sK1(k4_tarski(sK6(X0),sK7(X0))),sK2(k4_tarski(sK6(X0),sK7(X0)))) = k4_tarski(sK6(X0),sK7(X0))
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1067,c_1074])).

cnf(c_4589,plain,
    ( k11_relat_1(sK9,sK8) = k1_xboole_0
    | k4_tarski(sK1(k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8)))),sK2(k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8))))) = k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8))) ),
    inference(superposition,[status(thm)],[c_3158,c_1418])).

cnf(c_1176,plain,
    ( r2_hidden(k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8))),k11_relat_1(sK9,sK8))
    | ~ v1_relat_1(k11_relat_1(sK9,sK8))
    | k1_xboole_0 = k11_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1197,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8))),k11_relat_1(sK9,sK8))
    | r2_hidden(k4_tarski(sK8,k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8)))),sK9)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_720,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1226,plain,
    ( k11_relat_1(sK9,sK8) = k11_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1353,plain,
    ( ~ r2_hidden(k4_tarski(sK8,k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8)))),sK9)
    | r2_hidden(sK8,k1_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_721,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1204,plain,
    ( X0 != X1
    | k11_relat_1(sK9,sK8) != X1
    | k11_relat_1(sK9,sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1225,plain,
    ( X0 != k11_relat_1(sK9,sK8)
    | k11_relat_1(sK9,sK8) = X0
    | k11_relat_1(sK9,sK8) != k11_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_1204])).

cnf(c_1742,plain,
    ( k11_relat_1(sK9,sK8) != k11_relat_1(sK9,sK8)
    | k11_relat_1(sK9,sK8) = k1_xboole_0
    | k1_xboole_0 != k11_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_3160,plain,
    ( v1_relat_1(k11_relat_1(sK9,sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3158])).

cnf(c_5377,plain,
    ( k11_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4589,c_14,c_12,c_1176,c_1197,c_1226,c_1353,c_1742,c_3160])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1070,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1068,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1441,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1,X0),k11_relat_1(X1,X0)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1070,c_1068])).

cnf(c_5404,plain,
    ( r2_hidden(sK5(sK9,sK8),k1_xboole_0) = iProver_top
    | r2_hidden(sK8,k1_relat_1(sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5377,c_1441])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK8,k1_relat_1(sK9))
    | k1_xboole_0 != k11_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,plain,
    ( k1_xboole_0 != k11_relat_1(sK9,sK8)
    | r2_hidden(sK8,k1_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1179,plain,
    ( k11_relat_1(sK9,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k11_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_2167,plain,
    ( k11_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k11_relat_1(sK9,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_3385,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_5499,plain,
    ( r2_hidden(sK5(sK9,sK8),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5404,c_14,c_15,c_16,c_12,c_1176,c_1197,c_1353,c_3160])).

cnf(c_5504,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5499,c_1063])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:33:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.47/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/0.96  
% 2.47/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.47/0.96  
% 2.47/0.96  ------  iProver source info
% 2.47/0.96  
% 2.47/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.47/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.47/0.96  git: non_committed_changes: false
% 2.47/0.96  git: last_make_outside_of_git: false
% 2.47/0.96  
% 2.47/0.96  ------ 
% 2.47/0.96  
% 2.47/0.96  ------ Input Options
% 2.47/0.96  
% 2.47/0.96  --out_options                           all
% 2.47/0.96  --tptp_safe_out                         true
% 2.47/0.96  --problem_path                          ""
% 2.47/0.96  --include_path                          ""
% 2.47/0.96  --clausifier                            res/vclausify_rel
% 2.47/0.96  --clausifier_options                    --mode clausify
% 2.47/0.96  --stdin                                 false
% 2.47/0.96  --stats_out                             all
% 2.47/0.96  
% 2.47/0.96  ------ General Options
% 2.47/0.96  
% 2.47/0.96  --fof                                   false
% 2.47/0.96  --time_out_real                         305.
% 2.47/0.96  --time_out_virtual                      -1.
% 2.47/0.96  --symbol_type_check                     false
% 2.47/0.96  --clausify_out                          false
% 2.47/0.96  --sig_cnt_out                           false
% 2.47/0.96  --trig_cnt_out                          false
% 2.47/0.96  --trig_cnt_out_tolerance                1.
% 2.47/0.96  --trig_cnt_out_sk_spl                   false
% 2.47/0.96  --abstr_cl_out                          false
% 2.47/0.96  
% 2.47/0.96  ------ Global Options
% 2.47/0.96  
% 2.47/0.96  --schedule                              default
% 2.47/0.96  --add_important_lit                     false
% 2.47/0.96  --prop_solver_per_cl                    1000
% 2.47/0.96  --min_unsat_core                        false
% 2.47/0.96  --soft_assumptions                      false
% 2.47/0.96  --soft_lemma_size                       3
% 2.47/0.96  --prop_impl_unit_size                   0
% 2.47/0.96  --prop_impl_unit                        []
% 2.47/0.96  --share_sel_clauses                     true
% 2.47/0.96  --reset_solvers                         false
% 2.47/0.96  --bc_imp_inh                            [conj_cone]
% 2.47/0.96  --conj_cone_tolerance                   3.
% 2.47/0.96  --extra_neg_conj                        none
% 2.47/0.96  --large_theory_mode                     true
% 2.47/0.96  --prolific_symb_bound                   200
% 2.47/0.96  --lt_threshold                          2000
% 2.47/0.96  --clause_weak_htbl                      true
% 2.47/0.96  --gc_record_bc_elim                     false
% 2.47/0.96  
% 2.47/0.96  ------ Preprocessing Options
% 2.47/0.96  
% 2.47/0.96  --preprocessing_flag                    true
% 2.47/0.96  --time_out_prep_mult                    0.1
% 2.47/0.96  --splitting_mode                        input
% 2.47/0.96  --splitting_grd                         true
% 2.47/0.96  --splitting_cvd                         false
% 2.47/0.96  --splitting_cvd_svl                     false
% 2.47/0.96  --splitting_nvd                         32
% 2.47/0.96  --sub_typing                            true
% 2.47/0.96  --prep_gs_sim                           true
% 2.47/0.96  --prep_unflatten                        true
% 2.47/0.96  --prep_res_sim                          true
% 2.47/0.96  --prep_upred                            true
% 2.47/0.96  --prep_sem_filter                       exhaustive
% 2.47/0.96  --prep_sem_filter_out                   false
% 2.47/0.96  --pred_elim                             true
% 2.47/0.96  --res_sim_input                         true
% 2.47/0.96  --eq_ax_congr_red                       true
% 2.47/0.96  --pure_diseq_elim                       true
% 2.47/0.96  --brand_transform                       false
% 2.47/0.96  --non_eq_to_eq                          false
% 2.47/0.96  --prep_def_merge                        true
% 2.47/0.96  --prep_def_merge_prop_impl              false
% 2.47/0.96  --prep_def_merge_mbd                    true
% 2.47/0.96  --prep_def_merge_tr_red                 false
% 2.47/0.96  --prep_def_merge_tr_cl                  false
% 2.47/0.96  --smt_preprocessing                     true
% 2.47/0.96  --smt_ac_axioms                         fast
% 2.47/0.96  --preprocessed_out                      false
% 2.47/0.96  --preprocessed_stats                    false
% 2.47/0.96  
% 2.47/0.96  ------ Abstraction refinement Options
% 2.47/0.96  
% 2.47/0.96  --abstr_ref                             []
% 2.47/0.96  --abstr_ref_prep                        false
% 2.47/0.96  --abstr_ref_until_sat                   false
% 2.47/0.96  --abstr_ref_sig_restrict                funpre
% 2.47/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/0.96  --abstr_ref_under                       []
% 2.47/0.96  
% 2.47/0.96  ------ SAT Options
% 2.47/0.96  
% 2.47/0.96  --sat_mode                              false
% 2.47/0.96  --sat_fm_restart_options                ""
% 2.47/0.96  --sat_gr_def                            false
% 2.47/0.96  --sat_epr_types                         true
% 2.47/0.96  --sat_non_cyclic_types                  false
% 2.47/0.96  --sat_finite_models                     false
% 2.47/0.96  --sat_fm_lemmas                         false
% 2.47/0.96  --sat_fm_prep                           false
% 2.47/0.96  --sat_fm_uc_incr                        true
% 2.47/0.96  --sat_out_model                         small
% 2.47/0.96  --sat_out_clauses                       false
% 2.47/0.96  
% 2.47/0.96  ------ QBF Options
% 2.47/0.96  
% 2.47/0.96  --qbf_mode                              false
% 2.47/0.96  --qbf_elim_univ                         false
% 2.47/0.96  --qbf_dom_inst                          none
% 2.47/0.96  --qbf_dom_pre_inst                      false
% 2.47/0.96  --qbf_sk_in                             false
% 2.47/0.96  --qbf_pred_elim                         true
% 2.47/0.96  --qbf_split                             512
% 2.47/0.96  
% 2.47/0.96  ------ BMC1 Options
% 2.47/0.96  
% 2.47/0.96  --bmc1_incremental                      false
% 2.47/0.96  --bmc1_axioms                           reachable_all
% 2.47/0.96  --bmc1_min_bound                        0
% 2.47/0.96  --bmc1_max_bound                        -1
% 2.47/0.96  --bmc1_max_bound_default                -1
% 2.47/0.96  --bmc1_symbol_reachability              true
% 2.47/0.96  --bmc1_property_lemmas                  false
% 2.47/0.96  --bmc1_k_induction                      false
% 2.47/0.96  --bmc1_non_equiv_states                 false
% 2.47/0.96  --bmc1_deadlock                         false
% 2.47/0.96  --bmc1_ucm                              false
% 2.47/0.96  --bmc1_add_unsat_core                   none
% 2.47/0.96  --bmc1_unsat_core_children              false
% 2.47/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/0.96  --bmc1_out_stat                         full
% 2.47/0.96  --bmc1_ground_init                      false
% 2.47/0.96  --bmc1_pre_inst_next_state              false
% 2.47/0.96  --bmc1_pre_inst_state                   false
% 2.47/0.96  --bmc1_pre_inst_reach_state             false
% 2.47/0.96  --bmc1_out_unsat_core                   false
% 2.47/0.96  --bmc1_aig_witness_out                  false
% 2.47/0.96  --bmc1_verbose                          false
% 2.47/0.96  --bmc1_dump_clauses_tptp                false
% 2.47/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.47/0.96  --bmc1_dump_file                        -
% 2.47/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.47/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.47/0.96  --bmc1_ucm_extend_mode                  1
% 2.47/0.96  --bmc1_ucm_init_mode                    2
% 2.47/0.96  --bmc1_ucm_cone_mode                    none
% 2.47/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.47/0.96  --bmc1_ucm_relax_model                  4
% 2.47/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.47/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/0.96  --bmc1_ucm_layered_model                none
% 2.47/0.96  --bmc1_ucm_max_lemma_size               10
% 2.47/0.96  
% 2.47/0.96  ------ AIG Options
% 2.47/0.96  
% 2.47/0.96  --aig_mode                              false
% 2.47/0.96  
% 2.47/0.96  ------ Instantiation Options
% 2.47/0.96  
% 2.47/0.96  --instantiation_flag                    true
% 2.47/0.96  --inst_sos_flag                         false
% 2.47/0.96  --inst_sos_phase                        true
% 2.47/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/0.96  --inst_lit_sel_side                     num_symb
% 2.47/0.96  --inst_solver_per_active                1400
% 2.47/0.96  --inst_solver_calls_frac                1.
% 2.47/0.96  --inst_passive_queue_type               priority_queues
% 2.47/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/0.96  --inst_passive_queues_freq              [25;2]
% 2.47/0.96  --inst_dismatching                      true
% 2.47/0.96  --inst_eager_unprocessed_to_passive     true
% 2.47/0.96  --inst_prop_sim_given                   true
% 2.47/0.96  --inst_prop_sim_new                     false
% 2.47/0.96  --inst_subs_new                         false
% 2.47/0.96  --inst_eq_res_simp                      false
% 2.47/0.96  --inst_subs_given                       false
% 2.47/0.96  --inst_orphan_elimination               true
% 2.47/0.96  --inst_learning_loop_flag               true
% 2.47/0.96  --inst_learning_start                   3000
% 2.47/0.96  --inst_learning_factor                  2
% 2.47/0.96  --inst_start_prop_sim_after_learn       3
% 2.47/0.96  --inst_sel_renew                        solver
% 2.47/0.96  --inst_lit_activity_flag                true
% 2.47/0.96  --inst_restr_to_given                   false
% 2.47/0.96  --inst_activity_threshold               500
% 2.47/0.96  --inst_out_proof                        true
% 2.47/0.96  
% 2.47/0.96  ------ Resolution Options
% 2.47/0.96  
% 2.47/0.96  --resolution_flag                       true
% 2.47/0.96  --res_lit_sel                           adaptive
% 2.47/0.96  --res_lit_sel_side                      none
% 2.47/0.96  --res_ordering                          kbo
% 2.47/0.96  --res_to_prop_solver                    active
% 2.47/0.96  --res_prop_simpl_new                    false
% 2.47/0.96  --res_prop_simpl_given                  true
% 2.47/0.96  --res_passive_queue_type                priority_queues
% 2.47/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/0.96  --res_passive_queues_freq               [15;5]
% 2.47/0.96  --res_forward_subs                      full
% 2.47/0.96  --res_backward_subs                     full
% 2.47/0.96  --res_forward_subs_resolution           true
% 2.47/0.96  --res_backward_subs_resolution          true
% 2.47/0.96  --res_orphan_elimination                true
% 2.47/0.96  --res_time_limit                        2.
% 2.47/0.96  --res_out_proof                         true
% 2.47/0.96  
% 2.47/0.96  ------ Superposition Options
% 2.47/0.96  
% 2.47/0.96  --superposition_flag                    true
% 2.47/0.96  --sup_passive_queue_type                priority_queues
% 2.47/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.47/0.96  --demod_completeness_check              fast
% 2.47/0.96  --demod_use_ground                      true
% 2.47/0.96  --sup_to_prop_solver                    passive
% 2.47/0.96  --sup_prop_simpl_new                    true
% 2.47/0.96  --sup_prop_simpl_given                  true
% 2.47/0.96  --sup_fun_splitting                     false
% 2.47/0.96  --sup_smt_interval                      50000
% 2.47/0.96  
% 2.47/0.96  ------ Superposition Simplification Setup
% 2.47/0.96  
% 2.47/0.96  --sup_indices_passive                   []
% 2.47/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.96  --sup_full_bw                           [BwDemod]
% 2.47/0.96  --sup_immed_triv                        [TrivRules]
% 2.47/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.96  --sup_immed_bw_main                     []
% 2.47/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.96  
% 2.47/0.96  ------ Combination Options
% 2.47/0.96  
% 2.47/0.96  --comb_res_mult                         3
% 2.47/0.96  --comb_sup_mult                         2
% 2.47/0.96  --comb_inst_mult                        10
% 2.47/0.96  
% 2.47/0.96  ------ Debug Options
% 2.47/0.96  
% 2.47/0.96  --dbg_backtrace                         false
% 2.47/0.96  --dbg_dump_prop_clauses                 false
% 2.47/0.96  --dbg_dump_prop_clauses_file            -
% 2.47/0.96  --dbg_out_stat                          false
% 2.47/0.96  ------ Parsing...
% 2.47/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.47/0.96  
% 2.47/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.47/0.96  
% 2.47/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.47/0.96  
% 2.47/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.47/0.96  ------ Proving...
% 2.47/0.96  ------ Problem Properties 
% 2.47/0.96  
% 2.47/0.96  
% 2.47/0.96  clauses                                 14
% 2.47/0.96  conjectures                             3
% 2.47/0.96  EPR                                     2
% 2.47/0.96  Horn                                    11
% 2.47/0.96  unary                                   2
% 2.47/0.96  binary                                  6
% 2.47/0.96  lits                                    32
% 2.47/0.96  lits eq                                 7
% 2.47/0.96  fd_pure                                 0
% 2.47/0.96  fd_pseudo                               0
% 2.47/0.96  fd_cond                                 1
% 2.47/0.96  fd_pseudo_cond                          2
% 2.47/0.96  AC symbols                              0
% 2.47/0.96  
% 2.47/0.96  ------ Schedule dynamic 5 is on 
% 2.47/0.96  
% 2.47/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.47/0.96  
% 2.47/0.96  
% 2.47/0.96  ------ 
% 2.47/0.96  Current options:
% 2.47/0.96  ------ 
% 2.47/0.96  
% 2.47/0.96  ------ Input Options
% 2.47/0.96  
% 2.47/0.96  --out_options                           all
% 2.47/0.96  --tptp_safe_out                         true
% 2.47/0.96  --problem_path                          ""
% 2.47/0.96  --include_path                          ""
% 2.47/0.96  --clausifier                            res/vclausify_rel
% 2.47/0.96  --clausifier_options                    --mode clausify
% 2.47/0.96  --stdin                                 false
% 2.47/0.96  --stats_out                             all
% 2.47/0.96  
% 2.47/0.96  ------ General Options
% 2.47/0.96  
% 2.47/0.96  --fof                                   false
% 2.47/0.96  --time_out_real                         305.
% 2.47/0.96  --time_out_virtual                      -1.
% 2.47/0.96  --symbol_type_check                     false
% 2.47/0.96  --clausify_out                          false
% 2.47/0.96  --sig_cnt_out                           false
% 2.47/0.96  --trig_cnt_out                          false
% 2.47/0.96  --trig_cnt_out_tolerance                1.
% 2.47/0.96  --trig_cnt_out_sk_spl                   false
% 2.47/0.96  --abstr_cl_out                          false
% 2.47/0.96  
% 2.47/0.96  ------ Global Options
% 2.47/0.96  
% 2.47/0.96  --schedule                              default
% 2.47/0.96  --add_important_lit                     false
% 2.47/0.96  --prop_solver_per_cl                    1000
% 2.47/0.96  --min_unsat_core                        false
% 2.47/0.96  --soft_assumptions                      false
% 2.47/0.96  --soft_lemma_size                       3
% 2.47/0.96  --prop_impl_unit_size                   0
% 2.47/0.96  --prop_impl_unit                        []
% 2.47/0.96  --share_sel_clauses                     true
% 2.47/0.96  --reset_solvers                         false
% 2.47/0.96  --bc_imp_inh                            [conj_cone]
% 2.47/0.96  --conj_cone_tolerance                   3.
% 2.47/0.96  --extra_neg_conj                        none
% 2.47/0.96  --large_theory_mode                     true
% 2.47/0.96  --prolific_symb_bound                   200
% 2.47/0.96  --lt_threshold                          2000
% 2.47/0.96  --clause_weak_htbl                      true
% 2.47/0.96  --gc_record_bc_elim                     false
% 2.47/0.96  
% 2.47/0.96  ------ Preprocessing Options
% 2.47/0.96  
% 2.47/0.96  --preprocessing_flag                    true
% 2.47/0.96  --time_out_prep_mult                    0.1
% 2.47/0.96  --splitting_mode                        input
% 2.47/0.96  --splitting_grd                         true
% 2.47/0.96  --splitting_cvd                         false
% 2.47/0.96  --splitting_cvd_svl                     false
% 2.47/0.96  --splitting_nvd                         32
% 2.47/0.96  --sub_typing                            true
% 2.47/0.96  --prep_gs_sim                           true
% 2.47/0.96  --prep_unflatten                        true
% 2.47/0.96  --prep_res_sim                          true
% 2.47/0.96  --prep_upred                            true
% 2.47/0.96  --prep_sem_filter                       exhaustive
% 2.47/0.96  --prep_sem_filter_out                   false
% 2.47/0.96  --pred_elim                             true
% 2.47/0.96  --res_sim_input                         true
% 2.47/0.96  --eq_ax_congr_red                       true
% 2.47/0.96  --pure_diseq_elim                       true
% 2.47/0.96  --brand_transform                       false
% 2.47/0.96  --non_eq_to_eq                          false
% 2.47/0.96  --prep_def_merge                        true
% 2.47/0.96  --prep_def_merge_prop_impl              false
% 2.47/0.96  --prep_def_merge_mbd                    true
% 2.47/0.96  --prep_def_merge_tr_red                 false
% 2.47/0.96  --prep_def_merge_tr_cl                  false
% 2.47/0.96  --smt_preprocessing                     true
% 2.47/0.96  --smt_ac_axioms                         fast
% 2.47/0.96  --preprocessed_out                      false
% 2.47/0.96  --preprocessed_stats                    false
% 2.47/0.96  
% 2.47/0.96  ------ Abstraction refinement Options
% 2.47/0.96  
% 2.47/0.96  --abstr_ref                             []
% 2.47/0.96  --abstr_ref_prep                        false
% 2.47/0.96  --abstr_ref_until_sat                   false
% 2.47/0.96  --abstr_ref_sig_restrict                funpre
% 2.47/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/0.96  --abstr_ref_under                       []
% 2.47/0.96  
% 2.47/0.96  ------ SAT Options
% 2.47/0.96  
% 2.47/0.96  --sat_mode                              false
% 2.47/0.96  --sat_fm_restart_options                ""
% 2.47/0.96  --sat_gr_def                            false
% 2.47/0.96  --sat_epr_types                         true
% 2.47/0.96  --sat_non_cyclic_types                  false
% 2.47/0.96  --sat_finite_models                     false
% 2.47/0.96  --sat_fm_lemmas                         false
% 2.47/0.96  --sat_fm_prep                           false
% 2.47/0.96  --sat_fm_uc_incr                        true
% 2.47/0.96  --sat_out_model                         small
% 2.47/0.96  --sat_out_clauses                       false
% 2.47/0.96  
% 2.47/0.96  ------ QBF Options
% 2.47/0.96  
% 2.47/0.96  --qbf_mode                              false
% 2.47/0.96  --qbf_elim_univ                         false
% 2.47/0.96  --qbf_dom_inst                          none
% 2.47/0.96  --qbf_dom_pre_inst                      false
% 2.47/0.96  --qbf_sk_in                             false
% 2.47/0.96  --qbf_pred_elim                         true
% 2.47/0.96  --qbf_split                             512
% 2.47/0.96  
% 2.47/0.96  ------ BMC1 Options
% 2.47/0.96  
% 2.47/0.96  --bmc1_incremental                      false
% 2.47/0.96  --bmc1_axioms                           reachable_all
% 2.47/0.96  --bmc1_min_bound                        0
% 2.47/0.96  --bmc1_max_bound                        -1
% 2.47/0.96  --bmc1_max_bound_default                -1
% 2.47/0.96  --bmc1_symbol_reachability              true
% 2.47/0.96  --bmc1_property_lemmas                  false
% 2.47/0.96  --bmc1_k_induction                      false
% 2.47/0.96  --bmc1_non_equiv_states                 false
% 2.47/0.96  --bmc1_deadlock                         false
% 2.47/0.96  --bmc1_ucm                              false
% 2.47/0.96  --bmc1_add_unsat_core                   none
% 2.47/0.96  --bmc1_unsat_core_children              false
% 2.47/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/0.96  --bmc1_out_stat                         full
% 2.47/0.96  --bmc1_ground_init                      false
% 2.47/0.96  --bmc1_pre_inst_next_state              false
% 2.47/0.96  --bmc1_pre_inst_state                   false
% 2.47/0.96  --bmc1_pre_inst_reach_state             false
% 2.47/0.96  --bmc1_out_unsat_core                   false
% 2.47/0.96  --bmc1_aig_witness_out                  false
% 2.47/0.96  --bmc1_verbose                          false
% 2.47/0.96  --bmc1_dump_clauses_tptp                false
% 2.47/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.47/0.96  --bmc1_dump_file                        -
% 2.47/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.47/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.47/0.96  --bmc1_ucm_extend_mode                  1
% 2.47/0.96  --bmc1_ucm_init_mode                    2
% 2.47/0.96  --bmc1_ucm_cone_mode                    none
% 2.47/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.47/0.96  --bmc1_ucm_relax_model                  4
% 2.47/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.47/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/0.96  --bmc1_ucm_layered_model                none
% 2.47/0.96  --bmc1_ucm_max_lemma_size               10
% 2.47/0.96  
% 2.47/0.96  ------ AIG Options
% 2.47/0.96  
% 2.47/0.96  --aig_mode                              false
% 2.47/0.96  
% 2.47/0.96  ------ Instantiation Options
% 2.47/0.96  
% 2.47/0.96  --instantiation_flag                    true
% 2.47/0.96  --inst_sos_flag                         false
% 2.47/0.96  --inst_sos_phase                        true
% 2.47/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/0.96  --inst_lit_sel_side                     none
% 2.47/0.96  --inst_solver_per_active                1400
% 2.47/0.96  --inst_solver_calls_frac                1.
% 2.47/0.96  --inst_passive_queue_type               priority_queues
% 2.47/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/0.96  --inst_passive_queues_freq              [25;2]
% 2.47/0.96  --inst_dismatching                      true
% 2.47/0.96  --inst_eager_unprocessed_to_passive     true
% 2.47/0.96  --inst_prop_sim_given                   true
% 2.47/0.96  --inst_prop_sim_new                     false
% 2.47/0.96  --inst_subs_new                         false
% 2.47/0.96  --inst_eq_res_simp                      false
% 2.47/0.96  --inst_subs_given                       false
% 2.47/0.96  --inst_orphan_elimination               true
% 2.47/0.96  --inst_learning_loop_flag               true
% 2.47/0.96  --inst_learning_start                   3000
% 2.47/0.96  --inst_learning_factor                  2
% 2.47/0.96  --inst_start_prop_sim_after_learn       3
% 2.47/0.96  --inst_sel_renew                        solver
% 2.47/0.96  --inst_lit_activity_flag                true
% 2.47/0.96  --inst_restr_to_given                   false
% 2.47/0.96  --inst_activity_threshold               500
% 2.47/0.96  --inst_out_proof                        true
% 2.47/0.96  
% 2.47/0.96  ------ Resolution Options
% 2.47/0.96  
% 2.47/0.96  --resolution_flag                       false
% 2.47/0.96  --res_lit_sel                           adaptive
% 2.47/0.96  --res_lit_sel_side                      none
% 2.47/0.96  --res_ordering                          kbo
% 2.47/0.96  --res_to_prop_solver                    active
% 2.47/0.96  --res_prop_simpl_new                    false
% 2.47/0.96  --res_prop_simpl_given                  true
% 2.47/0.96  --res_passive_queue_type                priority_queues
% 2.47/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/0.96  --res_passive_queues_freq               [15;5]
% 2.47/0.96  --res_forward_subs                      full
% 2.47/0.96  --res_backward_subs                     full
% 2.47/0.96  --res_forward_subs_resolution           true
% 2.47/0.96  --res_backward_subs_resolution          true
% 2.47/0.96  --res_orphan_elimination                true
% 2.47/0.96  --res_time_limit                        2.
% 2.47/0.96  --res_out_proof                         true
% 2.47/0.96  
% 2.47/0.96  ------ Superposition Options
% 2.47/0.96  
% 2.47/0.96  --superposition_flag                    true
% 2.47/0.96  --sup_passive_queue_type                priority_queues
% 2.47/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.47/0.96  --demod_completeness_check              fast
% 2.47/0.96  --demod_use_ground                      true
% 2.47/0.96  --sup_to_prop_solver                    passive
% 2.47/0.96  --sup_prop_simpl_new                    true
% 2.47/0.96  --sup_prop_simpl_given                  true
% 2.47/0.96  --sup_fun_splitting                     false
% 2.47/0.96  --sup_smt_interval                      50000
% 2.47/0.96  
% 2.47/0.96  ------ Superposition Simplification Setup
% 2.47/0.96  
% 2.47/0.96  --sup_indices_passive                   []
% 2.47/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.96  --sup_full_bw                           [BwDemod]
% 2.47/0.96  --sup_immed_triv                        [TrivRules]
% 2.47/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.96  --sup_immed_bw_main                     []
% 2.47/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.96  
% 2.47/0.96  ------ Combination Options
% 2.47/0.96  
% 2.47/0.96  --comb_res_mult                         3
% 2.47/0.96  --comb_sup_mult                         2
% 2.47/0.96  --comb_inst_mult                        10
% 2.47/0.96  
% 2.47/0.96  ------ Debug Options
% 2.47/0.96  
% 2.47/0.96  --dbg_backtrace                         false
% 2.47/0.96  --dbg_dump_prop_clauses                 false
% 2.47/0.96  --dbg_dump_prop_clauses_file            -
% 2.47/0.96  --dbg_out_stat                          false
% 2.47/0.96  
% 2.47/0.96  
% 2.47/0.96  
% 2.47/0.96  
% 2.47/0.96  ------ Proving...
% 2.47/0.96  
% 2.47/0.96  
% 2.47/0.96  % SZS status Theorem for theBenchmark.p
% 2.47/0.96  
% 2.47/0.96   Resolution empty clause
% 2.47/0.96  
% 2.47/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.47/0.96  
% 2.47/0.96  fof(f4,axiom,(
% 2.47/0.96    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 2.47/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.96  
% 2.47/0.96  fof(f11,plain,(
% 2.47/0.96    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 2.47/0.96    inference(ennf_transformation,[],[f4])).
% 2.47/0.96  
% 2.47/0.96  fof(f16,plain,(
% 2.47/0.96    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 2.47/0.96    inference(nnf_transformation,[],[f11])).
% 2.47/0.96  
% 2.47/0.96  fof(f17,plain,(
% 2.47/0.96    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 2.47/0.96    inference(rectify,[],[f16])).
% 2.47/0.96  
% 2.47/0.96  fof(f19,plain,(
% 2.47/0.96    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 2.47/0.96    introduced(choice_axiom,[])).
% 2.47/0.96  
% 2.47/0.96  fof(f18,plain,(
% 2.47/0.96    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 2.47/0.96    introduced(choice_axiom,[])).
% 2.47/0.96  
% 2.47/0.96  fof(f20,plain,(
% 2.47/0.96    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 2.47/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).
% 2.47/0.96  
% 2.47/0.96  fof(f38,plain,(
% 2.47/0.96    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.47/0.96    inference(cnf_transformation,[],[f20])).
% 2.47/0.96  
% 2.47/0.96  fof(f6,axiom,(
% 2.47/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 2.47/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.96  
% 2.47/0.96  fof(f12,plain,(
% 2.47/0.96    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 2.47/0.96    inference(ennf_transformation,[],[f6])).
% 2.47/0.96  
% 2.47/0.96  fof(f27,plain,(
% 2.47/0.96    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 2.47/0.96    inference(nnf_transformation,[],[f12])).
% 2.47/0.96  
% 2.47/0.96  fof(f45,plain,(
% 2.47/0.96    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 2.47/0.96    inference(cnf_transformation,[],[f27])).
% 2.47/0.96  
% 2.47/0.96  fof(f5,axiom,(
% 2.47/0.96    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.47/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.96  
% 2.47/0.96  fof(f21,plain,(
% 2.47/0.96    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.47/0.96    inference(nnf_transformation,[],[f5])).
% 2.47/0.96  
% 2.47/0.96  fof(f22,plain,(
% 2.47/0.96    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.47/0.96    inference(rectify,[],[f21])).
% 2.47/0.96  
% 2.47/0.96  fof(f25,plain,(
% 2.47/0.96    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 2.47/0.96    introduced(choice_axiom,[])).
% 2.47/0.96  
% 2.47/0.96  fof(f24,plain,(
% 2.47/0.96    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0))) )),
% 2.47/0.96    introduced(choice_axiom,[])).
% 2.47/0.96  
% 2.47/0.96  fof(f23,plain,(
% 2.47/0.96    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.47/0.96    introduced(choice_axiom,[])).
% 2.47/0.96  
% 2.47/0.96  fof(f26,plain,(
% 2.47/0.96    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.47/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 2.47/0.96  
% 2.47/0.96  fof(f41,plain,(
% 2.47/0.96    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.47/0.96    inference(cnf_transformation,[],[f26])).
% 2.47/0.96  
% 2.47/0.96  fof(f51,plain,(
% 2.47/0.96    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.47/0.96    inference(equality_resolution,[],[f41])).
% 2.47/0.96  
% 2.47/0.96  fof(f8,conjecture,(
% 2.47/0.96    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.47/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.96  
% 2.47/0.96  fof(f9,negated_conjecture,(
% 2.47/0.96    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.47/0.96    inference(negated_conjecture,[],[f8])).
% 2.47/0.96  
% 2.47/0.96  fof(f15,plain,(
% 2.47/0.96    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 2.47/0.96    inference(ennf_transformation,[],[f9])).
% 2.47/0.96  
% 2.47/0.96  fof(f30,plain,(
% 2.47/0.96    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 2.47/0.96    inference(nnf_transformation,[],[f15])).
% 2.47/0.96  
% 2.47/0.96  fof(f31,plain,(
% 2.47/0.96    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.47/0.96    inference(flattening,[],[f30])).
% 2.47/0.96  
% 2.47/0.96  fof(f32,plain,(
% 2.47/0.96    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK9,sK8) | ~r2_hidden(sK8,k1_relat_1(sK9))) & (k1_xboole_0 != k11_relat_1(sK9,sK8) | r2_hidden(sK8,k1_relat_1(sK9))) & v1_relat_1(sK9))),
% 2.47/0.96    introduced(choice_axiom,[])).
% 2.47/0.96  
% 2.47/0.96  fof(f33,plain,(
% 2.47/0.96    (k1_xboole_0 = k11_relat_1(sK9,sK8) | ~r2_hidden(sK8,k1_relat_1(sK9))) & (k1_xboole_0 != k11_relat_1(sK9,sK8) | r2_hidden(sK8,k1_relat_1(sK9))) & v1_relat_1(sK9)),
% 2.47/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f31,f32])).
% 2.47/0.96  
% 2.47/0.96  fof(f49,plain,(
% 2.47/0.96    k1_xboole_0 = k11_relat_1(sK9,sK8) | ~r2_hidden(sK8,k1_relat_1(sK9))),
% 2.47/0.96    inference(cnf_transformation,[],[f33])).
% 2.47/0.96  
% 2.47/0.96  fof(f47,plain,(
% 2.47/0.96    v1_relat_1(sK9)),
% 2.47/0.96    inference(cnf_transformation,[],[f33])).
% 2.47/0.96  
% 2.47/0.96  fof(f1,axiom,(
% 2.47/0.96    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.47/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.96  
% 2.47/0.96  fof(f34,plain,(
% 2.47/0.96    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.47/0.96    inference(cnf_transformation,[],[f1])).
% 2.47/0.96  
% 2.47/0.96  fof(f3,axiom,(
% 2.47/0.96    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.47/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.96  
% 2.47/0.96  fof(f10,plain,(
% 2.47/0.96    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.47/0.96    inference(ennf_transformation,[],[f3])).
% 2.47/0.96  
% 2.47/0.96  fof(f36,plain,(
% 2.47/0.96    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 2.47/0.96    inference(cnf_transformation,[],[f10])).
% 2.47/0.96  
% 2.47/0.96  fof(f2,axiom,(
% 2.47/0.96    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.47/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.96  
% 2.47/0.96  fof(f35,plain,(
% 2.47/0.96    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.47/0.96    inference(cnf_transformation,[],[f2])).
% 2.47/0.96  
% 2.47/0.96  fof(f50,plain,(
% 2.47/0.96    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k1_enumset1(X0,X0,X1),X2)) )),
% 2.47/0.96    inference(definition_unfolding,[],[f36,f35])).
% 2.47/0.96  
% 2.47/0.96  fof(f7,axiom,(
% 2.47/0.96    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 2.47/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.96  
% 2.47/0.96  fof(f13,plain,(
% 2.47/0.96    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 2.47/0.96    inference(ennf_transformation,[],[f7])).
% 2.47/0.96  
% 2.47/0.96  fof(f14,plain,(
% 2.47/0.96    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 2.47/0.96    inference(flattening,[],[f13])).
% 2.47/0.96  
% 2.47/0.96  fof(f28,plain,(
% 2.47/0.96    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0))),
% 2.47/0.96    introduced(choice_axiom,[])).
% 2.47/0.96  
% 2.47/0.96  fof(f29,plain,(
% 2.47/0.96    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | ~v1_relat_1(X0))),
% 2.47/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f14,f28])).
% 2.47/0.96  
% 2.47/0.96  fof(f46,plain,(
% 2.47/0.96    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | ~v1_relat_1(X0)) )),
% 2.47/0.96    inference(cnf_transformation,[],[f29])).
% 2.47/0.96  
% 2.47/0.96  fof(f37,plain,(
% 2.47/0.96    ( ! [X4,X0] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 2.47/0.96    inference(cnf_transformation,[],[f20])).
% 2.47/0.96  
% 2.47/0.96  fof(f40,plain,(
% 2.47/0.96    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.47/0.96    inference(cnf_transformation,[],[f26])).
% 2.47/0.96  
% 2.47/0.96  fof(f52,plain,(
% 2.47/0.96    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.47/0.96    inference(equality_resolution,[],[f40])).
% 2.47/0.96  
% 2.47/0.96  fof(f44,plain,(
% 2.47/0.96    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.47/0.96    inference(cnf_transformation,[],[f27])).
% 2.47/0.96  
% 2.47/0.96  fof(f48,plain,(
% 2.47/0.96    k1_xboole_0 != k11_relat_1(sK9,sK8) | r2_hidden(sK8,k1_relat_1(sK9))),
% 2.47/0.96    inference(cnf_transformation,[],[f33])).
% 2.47/0.96  
% 2.47/0.96  cnf(c_3,plain,
% 2.47/0.96      ( r2_hidden(sK0(X0),X0) | v1_relat_1(X0) ),
% 2.47/0.96      inference(cnf_transformation,[],[f38]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1075,plain,
% 2.47/0.96      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_relat_1(X0) = iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_9,plain,
% 2.47/0.96      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.47/0.96      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.47/0.96      | ~ v1_relat_1(X1) ),
% 2.47/0.96      inference(cnf_transformation,[],[f45]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1069,plain,
% 2.47/0.96      ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
% 2.47/0.96      | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
% 2.47/0.96      | v1_relat_1(X1) != iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1505,plain,
% 2.47/0.96      ( r2_hidden(k4_tarski(X0,sK0(k11_relat_1(X1,X0))),X1) = iProver_top
% 2.47/0.96      | v1_relat_1(X1) != iProver_top
% 2.47/0.96      | v1_relat_1(k11_relat_1(X1,X0)) = iProver_top ),
% 2.47/0.96      inference(superposition,[status(thm)],[c_1075,c_1069]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_7,plain,
% 2.47/0.96      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.47/0.96      inference(cnf_transformation,[],[f51]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1071,plain,
% 2.47/0.96      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.47/0.96      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_2088,plain,
% 2.47/0.96      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.47/0.96      | v1_relat_1(X1) != iProver_top
% 2.47/0.96      | v1_relat_1(k11_relat_1(X1,X0)) = iProver_top ),
% 2.47/0.96      inference(superposition,[status(thm)],[c_1505,c_1071]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_12,negated_conjecture,
% 2.47/0.96      ( ~ r2_hidden(sK8,k1_relat_1(sK9)) | k1_xboole_0 = k11_relat_1(sK9,sK8) ),
% 2.47/0.96      inference(cnf_transformation,[],[f49]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1066,plain,
% 2.47/0.96      ( k1_xboole_0 = k11_relat_1(sK9,sK8)
% 2.47/0.96      | r2_hidden(sK8,k1_relat_1(sK9)) != iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_3026,plain,
% 2.47/0.96      ( k11_relat_1(sK9,sK8) = k1_xboole_0
% 2.47/0.96      | v1_relat_1(k11_relat_1(sK9,sK8)) = iProver_top
% 2.47/0.96      | v1_relat_1(sK9) != iProver_top ),
% 2.47/0.96      inference(superposition,[status(thm)],[c_2088,c_1066]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_14,negated_conjecture,
% 2.47/0.96      ( v1_relat_1(sK9) ),
% 2.47/0.96      inference(cnf_transformation,[],[f47]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_15,plain,
% 2.47/0.96      ( v1_relat_1(sK9) = iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_0,plain,
% 2.47/0.96      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.47/0.96      inference(cnf_transformation,[],[f34]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1,plain,
% 2.47/0.96      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k1_enumset1(X0,X0,X2),X1) ),
% 2.47/0.96      inference(cnf_transformation,[],[f50]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_206,plain,
% 2.47/0.96      ( ~ r2_hidden(X0,X1) | k1_enumset1(X0,X0,X2) != X3 | k1_xboole_0 != X1 ),
% 2.47/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_207,plain,
% 2.47/0.96      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.47/0.96      inference(unflattening,[status(thm)],[c_206]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1063,plain,
% 2.47/0.96      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1326,plain,
% 2.47/0.96      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.47/0.96      inference(superposition,[status(thm)],[c_1075,c_1063]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_723,plain,
% 2.47/0.96      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 2.47/0.96      theory(equality) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1217,plain,
% 2.47/0.96      ( ~ v1_relat_1(X0)
% 2.47/0.96      | v1_relat_1(k11_relat_1(sK9,sK8))
% 2.47/0.96      | k11_relat_1(sK9,sK8) != X0 ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_723]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_2166,plain,
% 2.47/0.96      ( v1_relat_1(k11_relat_1(sK9,sK8))
% 2.47/0.96      | ~ v1_relat_1(k1_xboole_0)
% 2.47/0.96      | k11_relat_1(sK9,sK8) != k1_xboole_0 ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_1217]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_2168,plain,
% 2.47/0.96      ( k11_relat_1(sK9,sK8) != k1_xboole_0
% 2.47/0.96      | v1_relat_1(k11_relat_1(sK9,sK8)) = iProver_top
% 2.47/0.96      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_2166]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_3158,plain,
% 2.47/0.96      ( v1_relat_1(k11_relat_1(sK9,sK8)) = iProver_top ),
% 2.47/0.96      inference(global_propositional_subsumption,
% 2.47/0.96                [status(thm)],
% 2.47/0.96                [c_3026,c_15,c_1326,c_2168]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_11,plain,
% 2.47/0.96      ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
% 2.47/0.96      | ~ v1_relat_1(X0)
% 2.47/0.96      | k1_xboole_0 = X0 ),
% 2.47/0.96      inference(cnf_transformation,[],[f46]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1067,plain,
% 2.47/0.96      ( k1_xboole_0 = X0
% 2.47/0.96      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) = iProver_top
% 2.47/0.96      | v1_relat_1(X0) != iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_4,plain,
% 2.47/0.96      ( ~ r2_hidden(X0,X1)
% 2.47/0.96      | ~ v1_relat_1(X1)
% 2.47/0.96      | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
% 2.47/0.96      inference(cnf_transformation,[],[f37]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1074,plain,
% 2.47/0.96      ( k4_tarski(sK1(X0),sK2(X0)) = X0
% 2.47/0.96      | r2_hidden(X0,X1) != iProver_top
% 2.47/0.96      | v1_relat_1(X1) != iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1418,plain,
% 2.47/0.96      ( k4_tarski(sK1(k4_tarski(sK6(X0),sK7(X0))),sK2(k4_tarski(sK6(X0),sK7(X0)))) = k4_tarski(sK6(X0),sK7(X0))
% 2.47/0.96      | k1_xboole_0 = X0
% 2.47/0.96      | v1_relat_1(X0) != iProver_top ),
% 2.47/0.96      inference(superposition,[status(thm)],[c_1067,c_1074]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_4589,plain,
% 2.47/0.96      ( k11_relat_1(sK9,sK8) = k1_xboole_0
% 2.47/0.96      | k4_tarski(sK1(k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8)))),sK2(k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8))))) = k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8))) ),
% 2.47/0.96      inference(superposition,[status(thm)],[c_3158,c_1418]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1176,plain,
% 2.47/0.96      ( r2_hidden(k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8))),k11_relat_1(sK9,sK8))
% 2.47/0.96      | ~ v1_relat_1(k11_relat_1(sK9,sK8))
% 2.47/0.96      | k1_xboole_0 = k11_relat_1(sK9,sK8) ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_11]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1197,plain,
% 2.47/0.96      ( ~ r2_hidden(k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8))),k11_relat_1(sK9,sK8))
% 2.47/0.96      | r2_hidden(k4_tarski(sK8,k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8)))),sK9)
% 2.47/0.96      | ~ v1_relat_1(sK9) ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_9]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_720,plain,( X0 = X0 ),theory(equality) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1226,plain,
% 2.47/0.96      ( k11_relat_1(sK9,sK8) = k11_relat_1(sK9,sK8) ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_720]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1353,plain,
% 2.47/0.96      ( ~ r2_hidden(k4_tarski(sK8,k4_tarski(sK6(k11_relat_1(sK9,sK8)),sK7(k11_relat_1(sK9,sK8)))),sK9)
% 2.47/0.96      | r2_hidden(sK8,k1_relat_1(sK9)) ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_7]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_721,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1204,plain,
% 2.47/0.96      ( X0 != X1 | k11_relat_1(sK9,sK8) != X1 | k11_relat_1(sK9,sK8) = X0 ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_721]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1225,plain,
% 2.47/0.96      ( X0 != k11_relat_1(sK9,sK8)
% 2.47/0.96      | k11_relat_1(sK9,sK8) = X0
% 2.47/0.96      | k11_relat_1(sK9,sK8) != k11_relat_1(sK9,sK8) ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_1204]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1742,plain,
% 2.47/0.96      ( k11_relat_1(sK9,sK8) != k11_relat_1(sK9,sK8)
% 2.47/0.96      | k11_relat_1(sK9,sK8) = k1_xboole_0
% 2.47/0.96      | k1_xboole_0 != k11_relat_1(sK9,sK8) ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_1225]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_3160,plain,
% 2.47/0.96      ( v1_relat_1(k11_relat_1(sK9,sK8)) ),
% 2.47/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_3158]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_5377,plain,
% 2.47/0.96      ( k11_relat_1(sK9,sK8) = k1_xboole_0 ),
% 2.47/0.96      inference(global_propositional_subsumption,
% 2.47/0.96                [status(thm)],
% 2.47/0.96                [c_4589,c_14,c_12,c_1176,c_1197,c_1226,c_1353,c_1742,c_3160]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_8,plain,
% 2.47/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.47/0.96      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
% 2.47/0.96      inference(cnf_transformation,[],[f52]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1070,plain,
% 2.47/0.96      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.47/0.96      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_10,plain,
% 2.47/0.96      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.47/0.96      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.47/0.96      | ~ v1_relat_1(X1) ),
% 2.47/0.96      inference(cnf_transformation,[],[f44]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1068,plain,
% 2.47/0.96      ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
% 2.47/0.96      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 2.47/0.96      | v1_relat_1(X1) != iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1441,plain,
% 2.47/0.96      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.47/0.96      | r2_hidden(sK5(X1,X0),k11_relat_1(X1,X0)) = iProver_top
% 2.47/0.96      | v1_relat_1(X1) != iProver_top ),
% 2.47/0.96      inference(superposition,[status(thm)],[c_1070,c_1068]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_5404,plain,
% 2.47/0.96      ( r2_hidden(sK5(sK9,sK8),k1_xboole_0) = iProver_top
% 2.47/0.96      | r2_hidden(sK8,k1_relat_1(sK9)) != iProver_top
% 2.47/0.96      | v1_relat_1(sK9) != iProver_top ),
% 2.47/0.96      inference(superposition,[status(thm)],[c_5377,c_1441]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_13,negated_conjecture,
% 2.47/0.96      ( r2_hidden(sK8,k1_relat_1(sK9)) | k1_xboole_0 != k11_relat_1(sK9,sK8) ),
% 2.47/0.96      inference(cnf_transformation,[],[f48]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_16,plain,
% 2.47/0.96      ( k1_xboole_0 != k11_relat_1(sK9,sK8)
% 2.47/0.96      | r2_hidden(sK8,k1_relat_1(sK9)) = iProver_top ),
% 2.47/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_1179,plain,
% 2.47/0.96      ( k11_relat_1(sK9,sK8) != X0
% 2.47/0.96      | k1_xboole_0 != X0
% 2.47/0.96      | k1_xboole_0 = k11_relat_1(sK9,sK8) ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_721]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_2167,plain,
% 2.47/0.96      ( k11_relat_1(sK9,sK8) != k1_xboole_0
% 2.47/0.96      | k1_xboole_0 = k11_relat_1(sK9,sK8)
% 2.47/0.96      | k1_xboole_0 != k1_xboole_0 ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_1179]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_3385,plain,
% 2.47/0.96      ( k1_xboole_0 = k1_xboole_0 ),
% 2.47/0.96      inference(instantiation,[status(thm)],[c_720]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_5499,plain,
% 2.47/0.96      ( r2_hidden(sK5(sK9,sK8),k1_xboole_0) = iProver_top ),
% 2.47/0.96      inference(global_propositional_subsumption,
% 2.47/0.96                [status(thm)],
% 2.47/0.96                [c_5404,c_14,c_15,c_16,c_12,c_1176,c_1197,c_1353,c_3160]) ).
% 2.47/0.96  
% 2.47/0.96  cnf(c_5504,plain,
% 2.47/0.96      ( $false ),
% 2.47/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_5499,c_1063]) ).
% 2.47/0.96  
% 2.47/0.96  
% 2.47/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.47/0.96  
% 2.47/0.96  ------                               Statistics
% 2.47/0.96  
% 2.47/0.96  ------ General
% 2.47/0.96  
% 2.47/0.96  abstr_ref_over_cycles:                  0
% 2.47/0.96  abstr_ref_under_cycles:                 0
% 2.47/0.96  gc_basic_clause_elim:                   0
% 2.47/0.96  forced_gc_time:                         0
% 2.47/0.96  parsing_time:                           0.008
% 2.47/0.96  unif_index_cands_time:                  0.
% 2.47/0.96  unif_index_add_time:                    0.
% 2.47/0.96  orderings_time:                         0.
% 2.47/0.96  out_proof_time:                         0.013
% 2.47/0.96  total_time:                             0.172
% 2.47/0.96  num_of_symbols:                         49
% 2.47/0.96  num_of_terms:                           5245
% 2.47/0.96  
% 2.47/0.96  ------ Preprocessing
% 2.47/0.96  
% 2.47/0.96  num_of_splits:                          0
% 2.47/0.96  num_of_split_atoms:                     0
% 2.47/0.96  num_of_reused_defs:                     0
% 2.47/0.96  num_eq_ax_congr_red:                    36
% 2.47/0.96  num_of_sem_filtered_clauses:            1
% 2.47/0.96  num_of_subtypes:                        0
% 2.47/0.96  monotx_restored_types:                  0
% 2.47/0.96  sat_num_of_epr_types:                   0
% 2.47/0.96  sat_num_of_non_cyclic_types:            0
% 2.47/0.96  sat_guarded_non_collapsed_types:        0
% 2.47/0.96  num_pure_diseq_elim:                    0
% 2.47/0.96  simp_replaced_by:                       0
% 2.47/0.96  res_preprocessed:                       72
% 2.47/0.96  prep_upred:                             0
% 2.47/0.96  prep_unflattend:                        22
% 2.47/0.96  smt_new_axioms:                         0
% 2.47/0.96  pred_elim_cands:                        2
% 2.47/0.96  pred_elim:                              1
% 2.47/0.96  pred_elim_cl:                           1
% 2.47/0.96  pred_elim_cycles:                       3
% 2.47/0.96  merged_defs:                            8
% 2.47/0.96  merged_defs_ncl:                        0
% 2.47/0.96  bin_hyper_res:                          8
% 2.47/0.96  prep_cycles:                            4
% 2.47/0.96  pred_elim_time:                         0.005
% 2.47/0.96  splitting_time:                         0.
% 2.47/0.96  sem_filter_time:                        0.
% 2.47/0.96  monotx_time:                            0.
% 2.47/0.96  subtype_inf_time:                       0.
% 2.47/0.96  
% 2.47/0.96  ------ Problem properties
% 2.47/0.96  
% 2.47/0.96  clauses:                                14
% 2.47/0.96  conjectures:                            3
% 2.47/0.96  epr:                                    2
% 2.47/0.96  horn:                                   11
% 2.47/0.96  ground:                                 3
% 2.47/0.96  unary:                                  2
% 2.47/0.96  binary:                                 6
% 2.47/0.96  lits:                                   32
% 2.47/0.96  lits_eq:                                7
% 2.47/0.96  fd_pure:                                0
% 2.47/0.96  fd_pseudo:                              0
% 2.47/0.96  fd_cond:                                1
% 2.47/0.96  fd_pseudo_cond:                         2
% 2.47/0.96  ac_symbols:                             0
% 2.47/0.96  
% 2.47/0.96  ------ Propositional Solver
% 2.47/0.96  
% 2.47/0.96  prop_solver_calls:                      29
% 2.47/0.96  prop_fast_solver_calls:                 559
% 2.47/0.96  smt_solver_calls:                       0
% 2.47/0.96  smt_fast_solver_calls:                  0
% 2.47/0.96  prop_num_of_clauses:                    1648
% 2.47/0.96  prop_preprocess_simplified:             3402
% 2.47/0.96  prop_fo_subsumed:                       10
% 2.47/0.96  prop_solver_time:                       0.
% 2.47/0.96  smt_solver_time:                        0.
% 2.47/0.96  smt_fast_solver_time:                   0.
% 2.47/0.96  prop_fast_solver_time:                  0.
% 2.47/0.96  prop_unsat_core_time:                   0.
% 2.47/0.96  
% 2.47/0.96  ------ QBF
% 2.47/0.96  
% 2.47/0.96  qbf_q_res:                              0
% 2.47/0.96  qbf_num_tautologies:                    0
% 2.47/0.96  qbf_prep_cycles:                        0
% 2.47/0.96  
% 2.47/0.96  ------ BMC1
% 2.47/0.96  
% 2.47/0.96  bmc1_current_bound:                     -1
% 2.47/0.96  bmc1_last_solved_bound:                 -1
% 2.47/0.96  bmc1_unsat_core_size:                   -1
% 2.47/0.96  bmc1_unsat_core_parents_size:           -1
% 2.47/0.96  bmc1_merge_next_fun:                    0
% 2.47/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.47/0.96  
% 2.47/0.96  ------ Instantiation
% 2.47/0.96  
% 2.47/0.96  inst_num_of_clauses:                    356
% 2.47/0.96  inst_num_in_passive:                    145
% 2.47/0.96  inst_num_in_active:                     199
% 2.47/0.96  inst_num_in_unprocessed:                12
% 2.47/0.96  inst_num_of_loops:                      300
% 2.47/0.96  inst_num_of_learning_restarts:          0
% 2.47/0.96  inst_num_moves_active_passive:          94
% 2.47/0.96  inst_lit_activity:                      0
% 2.47/0.96  inst_lit_activity_moves:                0
% 2.47/0.96  inst_num_tautologies:                   0
% 2.47/0.96  inst_num_prop_implied:                  0
% 2.47/0.96  inst_num_existing_simplified:           0
% 2.47/0.96  inst_num_eq_res_simplified:             0
% 2.47/0.96  inst_num_child_elim:                    0
% 2.47/0.96  inst_num_of_dismatching_blockings:      79
% 2.47/0.96  inst_num_of_non_proper_insts:           419
% 2.47/0.96  inst_num_of_duplicates:                 0
% 2.47/0.96  inst_inst_num_from_inst_to_res:         0
% 2.47/0.96  inst_dismatching_checking_time:         0.
% 2.47/0.96  
% 2.47/0.96  ------ Resolution
% 2.47/0.96  
% 2.47/0.96  res_num_of_clauses:                     0
% 2.47/0.96  res_num_in_passive:                     0
% 2.47/0.96  res_num_in_active:                      0
% 2.47/0.96  res_num_of_loops:                       76
% 2.47/0.96  res_forward_subset_subsumed:            32
% 2.47/0.96  res_backward_subset_subsumed:           0
% 2.47/0.96  res_forward_subsumed:                   0
% 2.47/0.96  res_backward_subsumed:                  0
% 2.47/0.96  res_forward_subsumption_resolution:     0
% 2.47/0.96  res_backward_subsumption_resolution:    0
% 2.47/0.96  res_clause_to_clause_subsumption:       509
% 2.47/0.96  res_orphan_elimination:                 0
% 2.47/0.96  res_tautology_del:                      79
% 2.47/0.96  res_num_eq_res_simplified:              0
% 2.47/0.96  res_num_sel_changes:                    0
% 2.47/0.96  res_moves_from_active_to_pass:          0
% 2.47/0.96  
% 2.47/0.96  ------ Superposition
% 2.47/0.96  
% 2.47/0.96  sup_time_total:                         0.
% 2.47/0.96  sup_time_generating:                    0.
% 2.47/0.96  sup_time_sim_full:                      0.
% 2.47/0.96  sup_time_sim_immed:                     0.
% 2.47/0.96  
% 2.47/0.96  sup_num_of_clauses:                     173
% 2.47/0.96  sup_num_in_active:                      49
% 2.47/0.96  sup_num_in_passive:                     124
% 2.47/0.96  sup_num_of_loops:                       59
% 2.47/0.96  sup_fw_superposition:                   168
% 2.47/0.96  sup_bw_superposition:                   108
% 2.47/0.96  sup_immediate_simplified:               122
% 2.47/0.96  sup_given_eliminated:                   2
% 2.47/0.96  comparisons_done:                       0
% 2.47/0.96  comparisons_avoided:                    2
% 2.47/0.96  
% 2.47/0.96  ------ Simplifications
% 2.47/0.96  
% 2.47/0.96  
% 2.47/0.96  sim_fw_subset_subsumed:                 28
% 2.47/0.96  sim_bw_subset_subsumed:                 1
% 2.47/0.96  sim_fw_subsumed:                        34
% 2.47/0.96  sim_bw_subsumed:                        1
% 2.47/0.96  sim_fw_subsumption_res:                 2
% 2.47/0.96  sim_bw_subsumption_res:                 37
% 2.47/0.96  sim_tautology_del:                      15
% 2.47/0.96  sim_eq_tautology_del:                   6
% 2.47/0.96  sim_eq_res_simp:                        1
% 2.47/0.96  sim_fw_demodulated:                     18
% 2.47/0.96  sim_bw_demodulated:                     17
% 2.47/0.96  sim_light_normalised:                   30
% 2.47/0.96  sim_joinable_taut:                      0
% 2.47/0.96  sim_joinable_simp:                      0
% 2.47/0.96  sim_ac_normalised:                      0
% 2.47/0.96  sim_smt_subsumption:                    0
% 2.47/0.96  
%------------------------------------------------------------------------------
