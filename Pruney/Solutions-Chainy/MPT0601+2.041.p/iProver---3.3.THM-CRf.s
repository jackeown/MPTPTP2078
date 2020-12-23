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
% DateTime   : Thu Dec  3 11:48:26 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 218 expanded)
%              Number of clauses        :   55 (  82 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  269 ( 733 expanded)
%              Number of equality atoms :   94 ( 218 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f16,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK6,sK5)
        | ~ r2_hidden(sK5,k1_relat_1(sK6)) )
      & ( k1_xboole_0 != k11_relat_1(sK6,sK5)
        | r2_hidden(sK5,k1_relat_1(sK6)) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK6,sK5)
      | ~ r2_hidden(sK5,k1_relat_1(sK6)) )
    & ( k1_xboole_0 != k11_relat_1(sK6,sK5)
      | r2_hidden(sK5,k1_relat_1(sK6)) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f29,f30])).

fof(f44,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

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
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f46,plain,
    ( k1_xboole_0 = k11_relat_1(sK6,sK5)
    | ~ r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,
    ( k1_xboole_0 != k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_201,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_676,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_253,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_315,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK6)
    | ~ r2_hidden(X0,k11_relat_1(sK6,X1)) ),
    inference(prop_impl,[status(thm)],[c_253])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(renaming,[status(thm)],[c_315])).

cnf(c_672,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1452,plain,
    ( k11_relat_1(sK6,X0) = k1_xboole_0
    | r2_hidden(k4_tarski(X0,sK0(k11_relat_1(sK6,X0))),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_672])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_680,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8753,plain,
    ( k11_relat_1(sK6,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_680])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK5,k1_relat_1(sK6))
    | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_678,plain,
    ( k1_xboole_0 = k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8875,plain,
    ( k11_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8753,c_678])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_679,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_240,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_241,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_317,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK6)
    | r2_hidden(X0,k11_relat_1(sK6,X1)) ),
    inference(prop_impl,[status(thm)],[c_241])).

cnf(c_318,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(renaming,[status(thm)],[c_317])).

cnf(c_673,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_861,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK4(sK6,X0),k11_relat_1(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_673])).

cnf(c_8921,plain,
    ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8875,c_861])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK5,k1_relat_1(sK6))
    | k1_xboole_0 != k11_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16,plain,
    ( k1_xboole_0 != k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_388,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_401,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_389,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_710,plain,
    ( k11_relat_1(sK6,sK5) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_711,plain,
    ( k11_relat_1(sK6,sK5) != k1_xboole_0
    | k1_xboole_0 = k11_relat_1(sK6,sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_736,plain,
    ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6)
    | ~ r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_737,plain,
    ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) = iProver_top
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_753,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK5,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_792,plain,
    ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_793,plain,
    ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) = iProver_top
    | r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_390,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1005,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
    | X1 != k11_relat_1(sK6,sK5)
    | X0 != sK4(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_2148,plain,
    ( r2_hidden(sK4(sK6,sK5),X0)
    | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
    | X0 != k11_relat_1(sK6,sK5)
    | sK4(sK6,sK5) != sK4(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_2149,plain,
    ( X0 != k11_relat_1(sK6,sK5)
    | sK4(sK6,sK5) != sK4(sK6,sK5)
    | r2_hidden(sK4(sK6,sK5),X0) = iProver_top
    | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2148])).

cnf(c_2151,plain,
    ( sK4(sK6,sK5) != sK4(sK6,sK5)
    | k1_xboole_0 != k11_relat_1(sK6,sK5)
    | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top
    | r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_4965,plain,
    ( sK4(sK6,sK5) = sK4(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_9201,plain,
    ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8921,c_16,c_401,c_711,c_737,c_793,c_2151,c_4965,c_8875])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_226,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_227,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_674,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_683,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_674,c_4])).

cnf(c_9205,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_9201,c_683])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:29 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.41/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.03  
% 2.41/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/1.03  
% 2.41/1.03  ------  iProver source info
% 2.41/1.03  
% 2.41/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.41/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/1.03  git: non_committed_changes: false
% 2.41/1.03  git: last_make_outside_of_git: false
% 2.41/1.03  
% 2.41/1.03  ------ 
% 2.41/1.03  
% 2.41/1.03  ------ Input Options
% 2.41/1.03  
% 2.41/1.03  --out_options                           all
% 2.41/1.03  --tptp_safe_out                         true
% 2.41/1.03  --problem_path                          ""
% 2.41/1.03  --include_path                          ""
% 2.41/1.03  --clausifier                            res/vclausify_rel
% 2.41/1.03  --clausifier_options                    ""
% 2.41/1.03  --stdin                                 false
% 2.41/1.03  --stats_out                             all
% 2.41/1.03  
% 2.41/1.03  ------ General Options
% 2.41/1.03  
% 2.41/1.03  --fof                                   false
% 2.41/1.03  --time_out_real                         305.
% 2.41/1.03  --time_out_virtual                      -1.
% 2.41/1.03  --symbol_type_check                     false
% 2.41/1.03  --clausify_out                          false
% 2.41/1.03  --sig_cnt_out                           false
% 2.41/1.03  --trig_cnt_out                          false
% 2.41/1.03  --trig_cnt_out_tolerance                1.
% 2.41/1.03  --trig_cnt_out_sk_spl                   false
% 2.41/1.03  --abstr_cl_out                          false
% 2.41/1.03  
% 2.41/1.03  ------ Global Options
% 2.41/1.03  
% 2.41/1.03  --schedule                              default
% 2.41/1.03  --add_important_lit                     false
% 2.41/1.03  --prop_solver_per_cl                    1000
% 2.41/1.03  --min_unsat_core                        false
% 2.41/1.03  --soft_assumptions                      false
% 2.41/1.03  --soft_lemma_size                       3
% 2.41/1.03  --prop_impl_unit_size                   0
% 2.41/1.03  --prop_impl_unit                        []
% 2.41/1.03  --share_sel_clauses                     true
% 2.41/1.03  --reset_solvers                         false
% 2.41/1.03  --bc_imp_inh                            [conj_cone]
% 2.41/1.03  --conj_cone_tolerance                   3.
% 2.41/1.03  --extra_neg_conj                        none
% 2.41/1.03  --large_theory_mode                     true
% 2.41/1.03  --prolific_symb_bound                   200
% 2.41/1.03  --lt_threshold                          2000
% 2.41/1.03  --clause_weak_htbl                      true
% 2.41/1.03  --gc_record_bc_elim                     false
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing Options
% 2.41/1.03  
% 2.41/1.03  --preprocessing_flag                    true
% 2.41/1.03  --time_out_prep_mult                    0.1
% 2.41/1.03  --splitting_mode                        input
% 2.41/1.03  --splitting_grd                         true
% 2.41/1.03  --splitting_cvd                         false
% 2.41/1.03  --splitting_cvd_svl                     false
% 2.41/1.03  --splitting_nvd                         32
% 2.41/1.03  --sub_typing                            true
% 2.41/1.03  --prep_gs_sim                           true
% 2.41/1.03  --prep_unflatten                        true
% 2.41/1.03  --prep_res_sim                          true
% 2.41/1.03  --prep_upred                            true
% 2.41/1.03  --prep_sem_filter                       exhaustive
% 2.41/1.03  --prep_sem_filter_out                   false
% 2.41/1.03  --pred_elim                             true
% 2.41/1.03  --res_sim_input                         true
% 2.41/1.03  --eq_ax_congr_red                       true
% 2.41/1.03  --pure_diseq_elim                       true
% 2.41/1.03  --brand_transform                       false
% 2.41/1.03  --non_eq_to_eq                          false
% 2.41/1.03  --prep_def_merge                        true
% 2.41/1.03  --prep_def_merge_prop_impl              false
% 2.41/1.03  --prep_def_merge_mbd                    true
% 2.41/1.03  --prep_def_merge_tr_red                 false
% 2.41/1.03  --prep_def_merge_tr_cl                  false
% 2.41/1.03  --smt_preprocessing                     true
% 2.41/1.03  --smt_ac_axioms                         fast
% 2.41/1.03  --preprocessed_out                      false
% 2.41/1.03  --preprocessed_stats                    false
% 2.41/1.03  
% 2.41/1.03  ------ Abstraction refinement Options
% 2.41/1.03  
% 2.41/1.03  --abstr_ref                             []
% 2.41/1.03  --abstr_ref_prep                        false
% 2.41/1.03  --abstr_ref_until_sat                   false
% 2.41/1.03  --abstr_ref_sig_restrict                funpre
% 2.41/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.03  --abstr_ref_under                       []
% 2.41/1.03  
% 2.41/1.03  ------ SAT Options
% 2.41/1.03  
% 2.41/1.03  --sat_mode                              false
% 2.41/1.03  --sat_fm_restart_options                ""
% 2.41/1.03  --sat_gr_def                            false
% 2.41/1.03  --sat_epr_types                         true
% 2.41/1.03  --sat_non_cyclic_types                  false
% 2.41/1.03  --sat_finite_models                     false
% 2.41/1.03  --sat_fm_lemmas                         false
% 2.41/1.03  --sat_fm_prep                           false
% 2.41/1.03  --sat_fm_uc_incr                        true
% 2.41/1.03  --sat_out_model                         small
% 2.41/1.03  --sat_out_clauses                       false
% 2.41/1.03  
% 2.41/1.03  ------ QBF Options
% 2.41/1.03  
% 2.41/1.03  --qbf_mode                              false
% 2.41/1.03  --qbf_elim_univ                         false
% 2.41/1.03  --qbf_dom_inst                          none
% 2.41/1.03  --qbf_dom_pre_inst                      false
% 2.41/1.03  --qbf_sk_in                             false
% 2.41/1.03  --qbf_pred_elim                         true
% 2.41/1.03  --qbf_split                             512
% 2.41/1.03  
% 2.41/1.03  ------ BMC1 Options
% 2.41/1.03  
% 2.41/1.03  --bmc1_incremental                      false
% 2.41/1.03  --bmc1_axioms                           reachable_all
% 2.41/1.03  --bmc1_min_bound                        0
% 2.41/1.03  --bmc1_max_bound                        -1
% 2.41/1.03  --bmc1_max_bound_default                -1
% 2.41/1.03  --bmc1_symbol_reachability              true
% 2.41/1.03  --bmc1_property_lemmas                  false
% 2.41/1.03  --bmc1_k_induction                      false
% 2.41/1.03  --bmc1_non_equiv_states                 false
% 2.41/1.03  --bmc1_deadlock                         false
% 2.41/1.03  --bmc1_ucm                              false
% 2.41/1.03  --bmc1_add_unsat_core                   none
% 2.41/1.03  --bmc1_unsat_core_children              false
% 2.41/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.03  --bmc1_out_stat                         full
% 2.41/1.03  --bmc1_ground_init                      false
% 2.41/1.03  --bmc1_pre_inst_next_state              false
% 2.41/1.03  --bmc1_pre_inst_state                   false
% 2.41/1.03  --bmc1_pre_inst_reach_state             false
% 2.41/1.03  --bmc1_out_unsat_core                   false
% 2.41/1.03  --bmc1_aig_witness_out                  false
% 2.41/1.03  --bmc1_verbose                          false
% 2.41/1.03  --bmc1_dump_clauses_tptp                false
% 2.41/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.03  --bmc1_dump_file                        -
% 2.41/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.03  --bmc1_ucm_extend_mode                  1
% 2.41/1.03  --bmc1_ucm_init_mode                    2
% 2.41/1.03  --bmc1_ucm_cone_mode                    none
% 2.41/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.03  --bmc1_ucm_relax_model                  4
% 2.41/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.03  --bmc1_ucm_layered_model                none
% 2.41/1.03  --bmc1_ucm_max_lemma_size               10
% 2.41/1.03  
% 2.41/1.03  ------ AIG Options
% 2.41/1.03  
% 2.41/1.03  --aig_mode                              false
% 2.41/1.03  
% 2.41/1.03  ------ Instantiation Options
% 2.41/1.03  
% 2.41/1.03  --instantiation_flag                    true
% 2.41/1.03  --inst_sos_flag                         true
% 2.41/1.03  --inst_sos_phase                        true
% 2.41/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.03  --inst_lit_sel_side                     num_symb
% 2.41/1.03  --inst_solver_per_active                1400
% 2.41/1.03  --inst_solver_calls_frac                1.
% 2.41/1.03  --inst_passive_queue_type               priority_queues
% 2.41/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.03  --inst_passive_queues_freq              [25;2]
% 2.41/1.03  --inst_dismatching                      true
% 2.41/1.03  --inst_eager_unprocessed_to_passive     true
% 2.41/1.03  --inst_prop_sim_given                   true
% 2.41/1.03  --inst_prop_sim_new                     false
% 2.41/1.03  --inst_subs_new                         false
% 2.41/1.03  --inst_eq_res_simp                      false
% 2.41/1.03  --inst_subs_given                       false
% 2.41/1.03  --inst_orphan_elimination               true
% 2.41/1.03  --inst_learning_loop_flag               true
% 2.41/1.03  --inst_learning_start                   3000
% 2.41/1.03  --inst_learning_factor                  2
% 2.41/1.03  --inst_start_prop_sim_after_learn       3
% 2.41/1.03  --inst_sel_renew                        solver
% 2.41/1.03  --inst_lit_activity_flag                true
% 2.41/1.03  --inst_restr_to_given                   false
% 2.41/1.03  --inst_activity_threshold               500
% 2.41/1.03  --inst_out_proof                        true
% 2.41/1.03  
% 2.41/1.03  ------ Resolution Options
% 2.41/1.03  
% 2.41/1.03  --resolution_flag                       true
% 2.41/1.03  --res_lit_sel                           adaptive
% 2.41/1.03  --res_lit_sel_side                      none
% 2.41/1.03  --res_ordering                          kbo
% 2.41/1.03  --res_to_prop_solver                    active
% 2.41/1.03  --res_prop_simpl_new                    false
% 2.41/1.03  --res_prop_simpl_given                  true
% 2.41/1.03  --res_passive_queue_type                priority_queues
% 2.41/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.03  --res_passive_queues_freq               [15;5]
% 2.41/1.03  --res_forward_subs                      full
% 2.41/1.03  --res_backward_subs                     full
% 2.41/1.03  --res_forward_subs_resolution           true
% 2.41/1.03  --res_backward_subs_resolution          true
% 2.41/1.03  --res_orphan_elimination                true
% 2.41/1.03  --res_time_limit                        2.
% 2.41/1.03  --res_out_proof                         true
% 2.41/1.03  
% 2.41/1.03  ------ Superposition Options
% 2.41/1.03  
% 2.41/1.03  --superposition_flag                    true
% 2.41/1.03  --sup_passive_queue_type                priority_queues
% 2.41/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.03  --demod_completeness_check              fast
% 2.41/1.03  --demod_use_ground                      true
% 2.41/1.03  --sup_to_prop_solver                    passive
% 2.41/1.03  --sup_prop_simpl_new                    true
% 2.41/1.03  --sup_prop_simpl_given                  true
% 2.41/1.03  --sup_fun_splitting                     true
% 2.41/1.03  --sup_smt_interval                      50000
% 2.41/1.03  
% 2.41/1.03  ------ Superposition Simplification Setup
% 2.41/1.03  
% 2.41/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.41/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.41/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.41/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.41/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.41/1.03  --sup_immed_triv                        [TrivRules]
% 2.41/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.03  --sup_immed_bw_main                     []
% 2.41/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.41/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.03  --sup_input_bw                          []
% 2.41/1.03  
% 2.41/1.03  ------ Combination Options
% 2.41/1.03  
% 2.41/1.03  --comb_res_mult                         3
% 2.41/1.03  --comb_sup_mult                         2
% 2.41/1.03  --comb_inst_mult                        10
% 2.41/1.03  
% 2.41/1.03  ------ Debug Options
% 2.41/1.03  
% 2.41/1.03  --dbg_backtrace                         false
% 2.41/1.03  --dbg_dump_prop_clauses                 false
% 2.41/1.03  --dbg_dump_prop_clauses_file            -
% 2.41/1.03  --dbg_out_stat                          false
% 2.41/1.03  ------ Parsing...
% 2.41/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/1.03  ------ Proving...
% 2.41/1.03  ------ Problem Properties 
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  clauses                                 12
% 2.41/1.03  conjectures                             2
% 2.41/1.03  EPR                                     0
% 2.41/1.03  Horn                                    10
% 2.41/1.03  unary                                   2
% 2.41/1.03  binary                                  8
% 2.41/1.03  lits                                    24
% 2.41/1.03  lits eq                                 6
% 2.41/1.03  fd_pure                                 0
% 2.41/1.03  fd_pseudo                               0
% 2.41/1.03  fd_cond                                 1
% 2.41/1.03  fd_pseudo_cond                          2
% 2.41/1.03  AC symbols                              0
% 2.41/1.03  
% 2.41/1.03  ------ Schedule dynamic 5 is on 
% 2.41/1.03  
% 2.41/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  ------ 
% 2.41/1.03  Current options:
% 2.41/1.03  ------ 
% 2.41/1.03  
% 2.41/1.03  ------ Input Options
% 2.41/1.03  
% 2.41/1.03  --out_options                           all
% 2.41/1.03  --tptp_safe_out                         true
% 2.41/1.03  --problem_path                          ""
% 2.41/1.03  --include_path                          ""
% 2.41/1.03  --clausifier                            res/vclausify_rel
% 2.41/1.03  --clausifier_options                    ""
% 2.41/1.03  --stdin                                 false
% 2.41/1.03  --stats_out                             all
% 2.41/1.03  
% 2.41/1.03  ------ General Options
% 2.41/1.03  
% 2.41/1.03  --fof                                   false
% 2.41/1.03  --time_out_real                         305.
% 2.41/1.03  --time_out_virtual                      -1.
% 2.41/1.03  --symbol_type_check                     false
% 2.41/1.03  --clausify_out                          false
% 2.41/1.03  --sig_cnt_out                           false
% 2.41/1.03  --trig_cnt_out                          false
% 2.41/1.03  --trig_cnt_out_tolerance                1.
% 2.41/1.03  --trig_cnt_out_sk_spl                   false
% 2.41/1.03  --abstr_cl_out                          false
% 2.41/1.03  
% 2.41/1.03  ------ Global Options
% 2.41/1.03  
% 2.41/1.03  --schedule                              default
% 2.41/1.03  --add_important_lit                     false
% 2.41/1.03  --prop_solver_per_cl                    1000
% 2.41/1.03  --min_unsat_core                        false
% 2.41/1.03  --soft_assumptions                      false
% 2.41/1.03  --soft_lemma_size                       3
% 2.41/1.03  --prop_impl_unit_size                   0
% 2.41/1.03  --prop_impl_unit                        []
% 2.41/1.03  --share_sel_clauses                     true
% 2.41/1.03  --reset_solvers                         false
% 2.41/1.03  --bc_imp_inh                            [conj_cone]
% 2.41/1.03  --conj_cone_tolerance                   3.
% 2.41/1.03  --extra_neg_conj                        none
% 2.41/1.03  --large_theory_mode                     true
% 2.41/1.03  --prolific_symb_bound                   200
% 2.41/1.03  --lt_threshold                          2000
% 2.41/1.03  --clause_weak_htbl                      true
% 2.41/1.03  --gc_record_bc_elim                     false
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing Options
% 2.41/1.03  
% 2.41/1.03  --preprocessing_flag                    true
% 2.41/1.03  --time_out_prep_mult                    0.1
% 2.41/1.03  --splitting_mode                        input
% 2.41/1.03  --splitting_grd                         true
% 2.41/1.03  --splitting_cvd                         false
% 2.41/1.03  --splitting_cvd_svl                     false
% 2.41/1.03  --splitting_nvd                         32
% 2.41/1.03  --sub_typing                            true
% 2.41/1.03  --prep_gs_sim                           true
% 2.41/1.03  --prep_unflatten                        true
% 2.41/1.03  --prep_res_sim                          true
% 2.41/1.03  --prep_upred                            true
% 2.41/1.03  --prep_sem_filter                       exhaustive
% 2.41/1.03  --prep_sem_filter_out                   false
% 2.41/1.03  --pred_elim                             true
% 2.41/1.03  --res_sim_input                         true
% 2.41/1.03  --eq_ax_congr_red                       true
% 2.41/1.03  --pure_diseq_elim                       true
% 2.41/1.03  --brand_transform                       false
% 2.41/1.03  --non_eq_to_eq                          false
% 2.41/1.03  --prep_def_merge                        true
% 2.41/1.03  --prep_def_merge_prop_impl              false
% 2.41/1.03  --prep_def_merge_mbd                    true
% 2.41/1.03  --prep_def_merge_tr_red                 false
% 2.41/1.03  --prep_def_merge_tr_cl                  false
% 2.41/1.03  --smt_preprocessing                     true
% 2.41/1.03  --smt_ac_axioms                         fast
% 2.41/1.03  --preprocessed_out                      false
% 2.41/1.03  --preprocessed_stats                    false
% 2.41/1.03  
% 2.41/1.03  ------ Abstraction refinement Options
% 2.41/1.03  
% 2.41/1.03  --abstr_ref                             []
% 2.41/1.03  --abstr_ref_prep                        false
% 2.41/1.03  --abstr_ref_until_sat                   false
% 2.41/1.03  --abstr_ref_sig_restrict                funpre
% 2.41/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.03  --abstr_ref_under                       []
% 2.41/1.03  
% 2.41/1.03  ------ SAT Options
% 2.41/1.03  
% 2.41/1.03  --sat_mode                              false
% 2.41/1.03  --sat_fm_restart_options                ""
% 2.41/1.03  --sat_gr_def                            false
% 2.41/1.03  --sat_epr_types                         true
% 2.41/1.03  --sat_non_cyclic_types                  false
% 2.41/1.03  --sat_finite_models                     false
% 2.41/1.03  --sat_fm_lemmas                         false
% 2.41/1.03  --sat_fm_prep                           false
% 2.41/1.03  --sat_fm_uc_incr                        true
% 2.41/1.03  --sat_out_model                         small
% 2.41/1.03  --sat_out_clauses                       false
% 2.41/1.03  
% 2.41/1.03  ------ QBF Options
% 2.41/1.03  
% 2.41/1.03  --qbf_mode                              false
% 2.41/1.03  --qbf_elim_univ                         false
% 2.41/1.03  --qbf_dom_inst                          none
% 2.41/1.03  --qbf_dom_pre_inst                      false
% 2.41/1.03  --qbf_sk_in                             false
% 2.41/1.03  --qbf_pred_elim                         true
% 2.41/1.03  --qbf_split                             512
% 2.41/1.03  
% 2.41/1.03  ------ BMC1 Options
% 2.41/1.03  
% 2.41/1.03  --bmc1_incremental                      false
% 2.41/1.03  --bmc1_axioms                           reachable_all
% 2.41/1.03  --bmc1_min_bound                        0
% 2.41/1.03  --bmc1_max_bound                        -1
% 2.41/1.03  --bmc1_max_bound_default                -1
% 2.41/1.03  --bmc1_symbol_reachability              true
% 2.41/1.03  --bmc1_property_lemmas                  false
% 2.41/1.03  --bmc1_k_induction                      false
% 2.41/1.03  --bmc1_non_equiv_states                 false
% 2.41/1.03  --bmc1_deadlock                         false
% 2.41/1.03  --bmc1_ucm                              false
% 2.41/1.03  --bmc1_add_unsat_core                   none
% 2.41/1.03  --bmc1_unsat_core_children              false
% 2.41/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.03  --bmc1_out_stat                         full
% 2.41/1.03  --bmc1_ground_init                      false
% 2.41/1.03  --bmc1_pre_inst_next_state              false
% 2.41/1.03  --bmc1_pre_inst_state                   false
% 2.41/1.03  --bmc1_pre_inst_reach_state             false
% 2.41/1.03  --bmc1_out_unsat_core                   false
% 2.41/1.03  --bmc1_aig_witness_out                  false
% 2.41/1.03  --bmc1_verbose                          false
% 2.41/1.03  --bmc1_dump_clauses_tptp                false
% 2.41/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.03  --bmc1_dump_file                        -
% 2.41/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.03  --bmc1_ucm_extend_mode                  1
% 2.41/1.03  --bmc1_ucm_init_mode                    2
% 2.41/1.03  --bmc1_ucm_cone_mode                    none
% 2.41/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.03  --bmc1_ucm_relax_model                  4
% 2.41/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.03  --bmc1_ucm_layered_model                none
% 2.41/1.03  --bmc1_ucm_max_lemma_size               10
% 2.41/1.03  
% 2.41/1.03  ------ AIG Options
% 2.41/1.03  
% 2.41/1.03  --aig_mode                              false
% 2.41/1.03  
% 2.41/1.03  ------ Instantiation Options
% 2.41/1.03  
% 2.41/1.03  --instantiation_flag                    true
% 2.41/1.03  --inst_sos_flag                         true
% 2.41/1.03  --inst_sos_phase                        true
% 2.41/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.03  --inst_lit_sel_side                     none
% 2.41/1.03  --inst_solver_per_active                1400
% 2.41/1.03  --inst_solver_calls_frac                1.
% 2.41/1.03  --inst_passive_queue_type               priority_queues
% 2.41/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.03  --inst_passive_queues_freq              [25;2]
% 2.41/1.03  --inst_dismatching                      true
% 2.41/1.03  --inst_eager_unprocessed_to_passive     true
% 2.41/1.03  --inst_prop_sim_given                   true
% 2.41/1.03  --inst_prop_sim_new                     false
% 2.41/1.03  --inst_subs_new                         false
% 2.41/1.03  --inst_eq_res_simp                      false
% 2.41/1.03  --inst_subs_given                       false
% 2.41/1.03  --inst_orphan_elimination               true
% 2.41/1.03  --inst_learning_loop_flag               true
% 2.41/1.03  --inst_learning_start                   3000
% 2.41/1.03  --inst_learning_factor                  2
% 2.41/1.03  --inst_start_prop_sim_after_learn       3
% 2.41/1.03  --inst_sel_renew                        solver
% 2.41/1.03  --inst_lit_activity_flag                true
% 2.41/1.03  --inst_restr_to_given                   false
% 2.41/1.03  --inst_activity_threshold               500
% 2.41/1.03  --inst_out_proof                        true
% 2.41/1.03  
% 2.41/1.03  ------ Resolution Options
% 2.41/1.03  
% 2.41/1.03  --resolution_flag                       false
% 2.41/1.03  --res_lit_sel                           adaptive
% 2.41/1.03  --res_lit_sel_side                      none
% 2.41/1.03  --res_ordering                          kbo
% 2.41/1.03  --res_to_prop_solver                    active
% 2.41/1.03  --res_prop_simpl_new                    false
% 2.41/1.03  --res_prop_simpl_given                  true
% 2.41/1.03  --res_passive_queue_type                priority_queues
% 2.41/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.03  --res_passive_queues_freq               [15;5]
% 2.41/1.03  --res_forward_subs                      full
% 2.41/1.03  --res_backward_subs                     full
% 2.41/1.03  --res_forward_subs_resolution           true
% 2.41/1.03  --res_backward_subs_resolution          true
% 2.41/1.03  --res_orphan_elimination                true
% 2.41/1.03  --res_time_limit                        2.
% 2.41/1.03  --res_out_proof                         true
% 2.41/1.03  
% 2.41/1.03  ------ Superposition Options
% 2.41/1.03  
% 2.41/1.03  --superposition_flag                    true
% 2.41/1.03  --sup_passive_queue_type                priority_queues
% 2.41/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.03  --demod_completeness_check              fast
% 2.41/1.03  --demod_use_ground                      true
% 2.41/1.03  --sup_to_prop_solver                    passive
% 2.41/1.03  --sup_prop_simpl_new                    true
% 2.41/1.03  --sup_prop_simpl_given                  true
% 2.41/1.03  --sup_fun_splitting                     true
% 2.41/1.03  --sup_smt_interval                      50000
% 2.41/1.03  
% 2.41/1.03  ------ Superposition Simplification Setup
% 2.41/1.03  
% 2.41/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.41/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.41/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.41/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.41/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.41/1.03  --sup_immed_triv                        [TrivRules]
% 2.41/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.03  --sup_immed_bw_main                     []
% 2.41/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.41/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.03  --sup_input_bw                          []
% 2.41/1.03  
% 2.41/1.03  ------ Combination Options
% 2.41/1.03  
% 2.41/1.03  --comb_res_mult                         3
% 2.41/1.03  --comb_sup_mult                         2
% 2.41/1.03  --comb_inst_mult                        10
% 2.41/1.03  
% 2.41/1.03  ------ Debug Options
% 2.41/1.03  
% 2.41/1.03  --dbg_backtrace                         false
% 2.41/1.03  --dbg_dump_prop_clauses                 false
% 2.41/1.03  --dbg_dump_prop_clauses_file            -
% 2.41/1.03  --dbg_out_stat                          false
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  ------ Proving...
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  % SZS status Theorem for theBenchmark.p
% 2.41/1.03  
% 2.41/1.03   Resolution empty clause
% 2.41/1.03  
% 2.41/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/1.03  
% 2.41/1.03  fof(f1,axiom,(
% 2.41/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.41/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f11,plain,(
% 2.41/1.03    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 2.41/1.03    inference(unused_predicate_definition_removal,[],[f1])).
% 2.41/1.03  
% 2.41/1.03  fof(f12,plain,(
% 2.41/1.03    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 2.41/1.03    inference(ennf_transformation,[],[f11])).
% 2.41/1.03  
% 2.41/1.03  fof(f17,plain,(
% 2.41/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.41/1.03    introduced(choice_axiom,[])).
% 2.41/1.03  
% 2.41/1.03  fof(f18,plain,(
% 2.41/1.03    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 2.41/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).
% 2.41/1.03  
% 2.41/1.03  fof(f32,plain,(
% 2.41/1.03    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f18])).
% 2.41/1.03  
% 2.41/1.03  fof(f2,axiom,(
% 2.41/1.03    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.41/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f13,plain,(
% 2.41/1.03    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.41/1.03    inference(ennf_transformation,[],[f2])).
% 2.41/1.03  
% 2.41/1.03  fof(f33,plain,(
% 2.41/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f13])).
% 2.41/1.03  
% 2.41/1.03  fof(f7,axiom,(
% 2.41/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 2.41/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f15,plain,(
% 2.41/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 2.41/1.03    inference(ennf_transformation,[],[f7])).
% 2.41/1.03  
% 2.41/1.03  fof(f27,plain,(
% 2.41/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 2.41/1.03    inference(nnf_transformation,[],[f15])).
% 2.41/1.03  
% 2.41/1.03  fof(f43,plain,(
% 2.41/1.03    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f27])).
% 2.41/1.03  
% 2.41/1.03  fof(f8,conjecture,(
% 2.41/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.41/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f9,negated_conjecture,(
% 2.41/1.03    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.41/1.03    inference(negated_conjecture,[],[f8])).
% 2.41/1.03  
% 2.41/1.03  fof(f16,plain,(
% 2.41/1.03    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 2.41/1.03    inference(ennf_transformation,[],[f9])).
% 2.41/1.03  
% 2.41/1.03  fof(f28,plain,(
% 2.41/1.03    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 2.41/1.03    inference(nnf_transformation,[],[f16])).
% 2.41/1.03  
% 2.41/1.03  fof(f29,plain,(
% 2.41/1.03    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.41/1.03    inference(flattening,[],[f28])).
% 2.41/1.03  
% 2.41/1.03  fof(f30,plain,(
% 2.41/1.03    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))) & (k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))) & v1_relat_1(sK6))),
% 2.41/1.03    introduced(choice_axiom,[])).
% 2.41/1.03  
% 2.41/1.03  fof(f31,plain,(
% 2.41/1.03    (k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))) & (k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))) & v1_relat_1(sK6)),
% 2.41/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f29,f30])).
% 2.41/1.03  
% 2.41/1.03  fof(f44,plain,(
% 2.41/1.03    v1_relat_1(sK6)),
% 2.41/1.03    inference(cnf_transformation,[],[f31])).
% 2.41/1.03  
% 2.41/1.03  fof(f6,axiom,(
% 2.41/1.03    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.41/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f21,plain,(
% 2.41/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.41/1.03    inference(nnf_transformation,[],[f6])).
% 2.41/1.03  
% 2.41/1.03  fof(f22,plain,(
% 2.41/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.41/1.03    inference(rectify,[],[f21])).
% 2.41/1.03  
% 2.41/1.03  fof(f25,plain,(
% 2.41/1.03    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 2.41/1.03    introduced(choice_axiom,[])).
% 2.41/1.03  
% 2.41/1.03  fof(f24,plain,(
% 2.41/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 2.41/1.03    introduced(choice_axiom,[])).
% 2.41/1.03  
% 2.41/1.03  fof(f23,plain,(
% 2.41/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.41/1.03    introduced(choice_axiom,[])).
% 2.41/1.03  
% 2.41/1.03  fof(f26,plain,(
% 2.41/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.41/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).
% 2.41/1.03  
% 2.41/1.03  fof(f39,plain,(
% 2.41/1.03    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.41/1.03    inference(cnf_transformation,[],[f26])).
% 2.41/1.03  
% 2.41/1.03  fof(f47,plain,(
% 2.41/1.03    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.41/1.03    inference(equality_resolution,[],[f39])).
% 2.41/1.03  
% 2.41/1.03  fof(f46,plain,(
% 2.41/1.03    k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))),
% 2.41/1.03    inference(cnf_transformation,[],[f31])).
% 2.41/1.03  
% 2.41/1.03  fof(f38,plain,(
% 2.41/1.03    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.41/1.03    inference(cnf_transformation,[],[f26])).
% 2.41/1.03  
% 2.41/1.03  fof(f48,plain,(
% 2.41/1.03    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.41/1.03    inference(equality_resolution,[],[f38])).
% 2.41/1.03  
% 2.41/1.03  fof(f42,plain,(
% 2.41/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f27])).
% 2.41/1.03  
% 2.41/1.03  fof(f45,plain,(
% 2.41/1.03    k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))),
% 2.41/1.03    inference(cnf_transformation,[],[f31])).
% 2.41/1.03  
% 2.41/1.03  fof(f3,axiom,(
% 2.41/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.41/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f10,plain,(
% 2.41/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.41/1.03    inference(rectify,[],[f3])).
% 2.41/1.03  
% 2.41/1.03  fof(f14,plain,(
% 2.41/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.41/1.03    inference(ennf_transformation,[],[f10])).
% 2.41/1.03  
% 2.41/1.03  fof(f19,plain,(
% 2.41/1.03    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.41/1.03    introduced(choice_axiom,[])).
% 2.41/1.03  
% 2.41/1.03  fof(f20,plain,(
% 2.41/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.41/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f19])).
% 2.41/1.03  
% 2.41/1.03  fof(f35,plain,(
% 2.41/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.41/1.03    inference(cnf_transformation,[],[f20])).
% 2.41/1.03  
% 2.41/1.03  fof(f5,axiom,(
% 2.41/1.03    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.41/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f37,plain,(
% 2.41/1.03    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f5])).
% 2.41/1.03  
% 2.41/1.03  fof(f4,axiom,(
% 2.41/1.03    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.41/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f36,plain,(
% 2.41/1.03    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f4])).
% 2.41/1.03  
% 2.41/1.03  cnf(c_0,plain,
% 2.41/1.03      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f32]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1,plain,
% 2.41/1.03      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.41/1.03      inference(cnf_transformation,[],[f33]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_201,plain,
% 2.41/1.03      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.41/1.03      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_676,plain,
% 2.41/1.03      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_10,plain,
% 2.41/1.03      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.41/1.03      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.41/1.03      | ~ v1_relat_1(X1) ),
% 2.41/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_14,negated_conjecture,
% 2.41/1.03      ( v1_relat_1(sK6) ),
% 2.41/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_252,plain,
% 2.41/1.03      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.41/1.03      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.41/1.03      | sK6 != X1 ),
% 2.41/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_253,plain,
% 2.41/1.03      ( ~ r2_hidden(X0,k11_relat_1(sK6,X1)) | r2_hidden(k4_tarski(X1,X0),sK6) ),
% 2.41/1.03      inference(unflattening,[status(thm)],[c_252]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_315,plain,
% 2.41/1.03      ( r2_hidden(k4_tarski(X1,X0),sK6) | ~ r2_hidden(X0,k11_relat_1(sK6,X1)) ),
% 2.41/1.03      inference(prop_impl,[status(thm)],[c_253]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_316,plain,
% 2.41/1.03      ( ~ r2_hidden(X0,k11_relat_1(sK6,X1)) | r2_hidden(k4_tarski(X1,X0),sK6) ),
% 2.41/1.03      inference(renaming,[status(thm)],[c_315]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_672,plain,
% 2.41/1.03      ( r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
% 2.41/1.03      | r2_hidden(k4_tarski(X1,X0),sK6) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1452,plain,
% 2.41/1.03      ( k11_relat_1(sK6,X0) = k1_xboole_0
% 2.41/1.03      | r2_hidden(k4_tarski(X0,sK0(k11_relat_1(sK6,X0))),sK6) = iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_676,c_672]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_8,plain,
% 2.41/1.03      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.41/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_680,plain,
% 2.41/1.03      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.41/1.03      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_8753,plain,
% 2.41/1.03      ( k11_relat_1(sK6,X0) = k1_xboole_0
% 2.41/1.03      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_1452,c_680]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_12,negated_conjecture,
% 2.41/1.03      ( ~ r2_hidden(sK5,k1_relat_1(sK6)) | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
% 2.41/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_678,plain,
% 2.41/1.03      ( k1_xboole_0 = k11_relat_1(sK6,sK5)
% 2.41/1.03      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_8875,plain,
% 2.41/1.03      ( k11_relat_1(sK6,sK5) = k1_xboole_0 ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_8753,c_678]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_9,plain,
% 2.41/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.41/1.03      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 2.41/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_679,plain,
% 2.41/1.03      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.41/1.03      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_11,plain,
% 2.41/1.03      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.41/1.03      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.41/1.03      | ~ v1_relat_1(X1) ),
% 2.41/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_240,plain,
% 2.41/1.03      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.41/1.03      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.41/1.03      | sK6 != X1 ),
% 2.41/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_241,plain,
% 2.41/1.03      ( r2_hidden(X0,k11_relat_1(sK6,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
% 2.41/1.03      inference(unflattening,[status(thm)],[c_240]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_317,plain,
% 2.41/1.03      ( ~ r2_hidden(k4_tarski(X1,X0),sK6) | r2_hidden(X0,k11_relat_1(sK6,X1)) ),
% 2.41/1.03      inference(prop_impl,[status(thm)],[c_241]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_318,plain,
% 2.41/1.03      ( r2_hidden(X0,k11_relat_1(sK6,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
% 2.41/1.03      inference(renaming,[status(thm)],[c_317]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_673,plain,
% 2.41/1.03      ( r2_hidden(X0,k11_relat_1(sK6,X1)) = iProver_top
% 2.41/1.03      | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_861,plain,
% 2.41/1.03      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.41/1.03      | r2_hidden(sK4(sK6,X0),k11_relat_1(sK6,X0)) = iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_679,c_673]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_8921,plain,
% 2.41/1.03      ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top
% 2.41/1.03      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_8875,c_861]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_13,negated_conjecture,
% 2.41/1.03      ( r2_hidden(sK5,k1_relat_1(sK6)) | k1_xboole_0 != k11_relat_1(sK6,sK5) ),
% 2.41/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_16,plain,
% 2.41/1.03      ( k1_xboole_0 != k11_relat_1(sK6,sK5)
% 2.41/1.03      | r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_388,plain,( X0 = X0 ),theory(equality) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_401,plain,
% 2.41/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_388]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_389,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_710,plain,
% 2.41/1.03      ( k11_relat_1(sK6,sK5) != X0
% 2.41/1.03      | k1_xboole_0 != X0
% 2.41/1.03      | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_389]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_711,plain,
% 2.41/1.03      ( k11_relat_1(sK6,sK5) != k1_xboole_0
% 2.41/1.03      | k1_xboole_0 = k11_relat_1(sK6,sK5)
% 2.41/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_710]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_736,plain,
% 2.41/1.03      ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6)
% 2.41/1.03      | ~ r2_hidden(sK5,k1_relat_1(sK6)) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_737,plain,
% 2.41/1.03      ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) = iProver_top
% 2.41/1.03      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_753,plain,
% 2.41/1.03      ( r2_hidden(X0,k11_relat_1(sK6,sK5))
% 2.41/1.03      | ~ r2_hidden(k4_tarski(sK5,X0),sK6) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_318]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_792,plain,
% 2.41/1.03      ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
% 2.41/1.03      | ~ r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_753]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_793,plain,
% 2.41/1.03      ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) = iProver_top
% 2.41/1.03      | r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_390,plain,
% 2.41/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.41/1.03      theory(equality) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1005,plain,
% 2.41/1.03      ( r2_hidden(X0,X1)
% 2.41/1.03      | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
% 2.41/1.03      | X1 != k11_relat_1(sK6,sK5)
% 2.41/1.03      | X0 != sK4(sK6,sK5) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_390]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2148,plain,
% 2.41/1.03      ( r2_hidden(sK4(sK6,sK5),X0)
% 2.41/1.03      | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
% 2.41/1.03      | X0 != k11_relat_1(sK6,sK5)
% 2.41/1.03      | sK4(sK6,sK5) != sK4(sK6,sK5) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_1005]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2149,plain,
% 2.41/1.03      ( X0 != k11_relat_1(sK6,sK5)
% 2.41/1.03      | sK4(sK6,sK5) != sK4(sK6,sK5)
% 2.41/1.03      | r2_hidden(sK4(sK6,sK5),X0) = iProver_top
% 2.41/1.03      | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_2148]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2151,plain,
% 2.41/1.03      ( sK4(sK6,sK5) != sK4(sK6,sK5)
% 2.41/1.03      | k1_xboole_0 != k11_relat_1(sK6,sK5)
% 2.41/1.03      | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top
% 2.41/1.03      | r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_2149]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_4965,plain,
% 2.41/1.03      ( sK4(sK6,sK5) = sK4(sK6,sK5) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_388]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_9201,plain,
% 2.41/1.03      ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
% 2.41/1.03      inference(global_propositional_subsumption,
% 2.41/1.03                [status(thm)],
% 2.41/1.03                [c_8921,c_16,c_401,c_711,c_737,c_793,c_2151,c_4965,c_8875]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2,plain,
% 2.41/1.03      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 2.41/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_5,plain,
% 2.41/1.03      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_226,plain,
% 2.41/1.03      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | X3 != X1 | k1_xboole_0 != X2 ),
% 2.41/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_5]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_227,plain,
% 2.41/1.03      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 2.41/1.03      inference(unflattening,[status(thm)],[c_226]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_674,plain,
% 2.41/1.03      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_4,plain,
% 2.41/1.03      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.41/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_683,plain,
% 2.41/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.41/1.03      inference(demodulation,[status(thm)],[c_674,c_4]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_9205,plain,
% 2.41/1.03      ( $false ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_9201,c_683]) ).
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/1.03  
% 2.41/1.03  ------                               Statistics
% 2.41/1.03  
% 2.41/1.03  ------ General
% 2.41/1.03  
% 2.41/1.03  abstr_ref_over_cycles:                  0
% 2.41/1.03  abstr_ref_under_cycles:                 0
% 2.41/1.03  gc_basic_clause_elim:                   0
% 2.41/1.03  forced_gc_time:                         0
% 2.41/1.03  parsing_time:                           0.01
% 2.41/1.03  unif_index_cands_time:                  0.
% 2.41/1.03  unif_index_add_time:                    0.
% 2.41/1.03  orderings_time:                         0.
% 2.41/1.03  out_proof_time:                         0.01
% 2.41/1.03  total_time:                             0.432
% 2.41/1.03  num_of_symbols:                         47
% 2.41/1.03  num_of_terms:                           11892
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing
% 2.41/1.03  
% 2.41/1.03  num_of_splits:                          0
% 2.41/1.03  num_of_split_atoms:                     0
% 2.41/1.03  num_of_reused_defs:                     0
% 2.41/1.03  num_eq_ax_congr_red:                    32
% 2.41/1.03  num_of_sem_filtered_clauses:            1
% 2.41/1.03  num_of_subtypes:                        0
% 2.41/1.03  monotx_restored_types:                  0
% 2.41/1.03  sat_num_of_epr_types:                   0
% 2.41/1.03  sat_num_of_non_cyclic_types:            0
% 2.41/1.03  sat_guarded_non_collapsed_types:        0
% 2.41/1.03  num_pure_diseq_elim:                    0
% 2.41/1.03  simp_replaced_by:                       0
% 2.41/1.03  res_preprocessed:                       66
% 2.41/1.03  prep_upred:                             0
% 2.41/1.03  prep_unflattend:                        4
% 2.41/1.03  smt_new_axioms:                         0
% 2.41/1.03  pred_elim_cands:                        1
% 2.41/1.03  pred_elim:                              3
% 2.41/1.03  pred_elim_cl:                           3
% 2.41/1.03  pred_elim_cycles:                       5
% 2.41/1.03  merged_defs:                            14
% 2.41/1.03  merged_defs_ncl:                        0
% 2.41/1.03  bin_hyper_res:                          14
% 2.41/1.03  prep_cycles:                            4
% 2.41/1.03  pred_elim_time:                         0.001
% 2.41/1.03  splitting_time:                         0.
% 2.41/1.03  sem_filter_time:                        0.
% 2.41/1.03  monotx_time:                            0.
% 2.41/1.03  subtype_inf_time:                       0.
% 2.41/1.03  
% 2.41/1.03  ------ Problem properties
% 2.41/1.03  
% 2.41/1.03  clauses:                                12
% 2.41/1.03  conjectures:                            2
% 2.41/1.03  epr:                                    0
% 2.41/1.03  horn:                                   10
% 2.41/1.03  ground:                                 2
% 2.41/1.03  unary:                                  2
% 2.41/1.03  binary:                                 8
% 2.41/1.03  lits:                                   24
% 2.41/1.03  lits_eq:                                6
% 2.41/1.03  fd_pure:                                0
% 2.41/1.03  fd_pseudo:                              0
% 2.41/1.03  fd_cond:                                1
% 2.41/1.03  fd_pseudo_cond:                         2
% 2.41/1.03  ac_symbols:                             0
% 2.41/1.03  
% 2.41/1.03  ------ Propositional Solver
% 2.41/1.03  
% 2.41/1.03  prop_solver_calls:                      35
% 2.41/1.03  prop_fast_solver_calls:                 548
% 2.41/1.03  smt_solver_calls:                       0
% 2.41/1.03  smt_fast_solver_calls:                  0
% 2.41/1.03  prop_num_of_clauses:                    5409
% 2.41/1.03  prop_preprocess_simplified:             4675
% 2.41/1.03  prop_fo_subsumed:                       1
% 2.41/1.03  prop_solver_time:                       0.
% 2.41/1.03  smt_solver_time:                        0.
% 2.41/1.03  smt_fast_solver_time:                   0.
% 2.41/1.03  prop_fast_solver_time:                  0.
% 2.41/1.03  prop_unsat_core_time:                   0.
% 2.41/1.03  
% 2.41/1.03  ------ QBF
% 2.41/1.03  
% 2.41/1.03  qbf_q_res:                              0
% 2.41/1.03  qbf_num_tautologies:                    0
% 2.41/1.03  qbf_prep_cycles:                        0
% 2.41/1.03  
% 2.41/1.03  ------ BMC1
% 2.41/1.03  
% 2.41/1.03  bmc1_current_bound:                     -1
% 2.41/1.03  bmc1_last_solved_bound:                 -1
% 2.41/1.03  bmc1_unsat_core_size:                   -1
% 2.41/1.03  bmc1_unsat_core_parents_size:           -1
% 2.41/1.03  bmc1_merge_next_fun:                    0
% 2.41/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.41/1.03  
% 2.41/1.03  ------ Instantiation
% 2.41/1.03  
% 2.41/1.03  inst_num_of_clauses:                    653
% 2.41/1.03  inst_num_in_passive:                    200
% 2.41/1.03  inst_num_in_active:                     374
% 2.41/1.03  inst_num_in_unprocessed:                79
% 2.41/1.03  inst_num_of_loops:                      540
% 2.41/1.03  inst_num_of_learning_restarts:          0
% 2.41/1.03  inst_num_moves_active_passive:          160
% 2.41/1.03  inst_lit_activity:                      0
% 2.41/1.03  inst_lit_activity_moves:                0
% 2.41/1.03  inst_num_tautologies:                   0
% 2.41/1.03  inst_num_prop_implied:                  0
% 2.41/1.03  inst_num_existing_simplified:           0
% 2.41/1.03  inst_num_eq_res_simplified:             0
% 2.41/1.03  inst_num_child_elim:                    0
% 2.41/1.03  inst_num_of_dismatching_blockings:      486
% 2.41/1.03  inst_num_of_non_proper_insts:           959
% 2.41/1.03  inst_num_of_duplicates:                 0
% 2.41/1.03  inst_inst_num_from_inst_to_res:         0
% 2.41/1.03  inst_dismatching_checking_time:         0.
% 2.41/1.03  
% 2.41/1.03  ------ Resolution
% 2.41/1.03  
% 2.41/1.03  res_num_of_clauses:                     0
% 2.41/1.03  res_num_in_passive:                     0
% 2.41/1.03  res_num_in_active:                      0
% 2.41/1.03  res_num_of_loops:                       70
% 2.41/1.03  res_forward_subset_subsumed:            68
% 2.41/1.03  res_backward_subset_subsumed:           0
% 2.41/1.03  res_forward_subsumed:                   0
% 2.41/1.03  res_backward_subsumed:                  0
% 2.41/1.03  res_forward_subsumption_resolution:     0
% 2.41/1.03  res_backward_subsumption_resolution:    0
% 2.41/1.03  res_clause_to_clause_subsumption:       1079
% 2.41/1.03  res_orphan_elimination:                 0
% 2.41/1.03  res_tautology_del:                      161
% 2.41/1.03  res_num_eq_res_simplified:              0
% 2.41/1.03  res_num_sel_changes:                    0
% 2.41/1.03  res_moves_from_active_to_pass:          0
% 2.41/1.03  
% 2.41/1.03  ------ Superposition
% 2.41/1.03  
% 2.41/1.03  sup_time_total:                         0.
% 2.41/1.03  sup_time_generating:                    0.
% 2.41/1.03  sup_time_sim_full:                      0.
% 2.41/1.03  sup_time_sim_immed:                     0.
% 2.41/1.03  
% 2.41/1.03  sup_num_of_clauses:                     939
% 2.41/1.03  sup_num_in_active:                      96
% 2.41/1.03  sup_num_in_passive:                     843
% 2.41/1.03  sup_num_of_loops:                       107
% 2.41/1.03  sup_fw_superposition:                   703
% 2.41/1.03  sup_bw_superposition:                   578
% 2.41/1.03  sup_immediate_simplified:               84
% 2.41/1.03  sup_given_eliminated:                   0
% 2.41/1.03  comparisons_done:                       0
% 2.41/1.03  comparisons_avoided:                    1
% 2.41/1.03  
% 2.41/1.03  ------ Simplifications
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  sim_fw_subset_subsumed:                 34
% 2.41/1.03  sim_bw_subset_subsumed:                 0
% 2.41/1.03  sim_fw_subsumed:                        22
% 2.41/1.03  sim_bw_subsumed:                        0
% 2.41/1.03  sim_fw_subsumption_res:                 0
% 2.41/1.03  sim_bw_subsumption_res:                 0
% 2.41/1.03  sim_tautology_del:                      4
% 2.41/1.03  sim_eq_tautology_del:                   26
% 2.41/1.03  sim_eq_res_simp:                        1
% 2.41/1.03  sim_fw_demodulated:                     11
% 2.41/1.03  sim_bw_demodulated:                     14
% 2.41/1.03  sim_light_normalised:                   44
% 2.41/1.03  sim_joinable_taut:                      0
% 2.41/1.03  sim_joinable_simp:                      0
% 2.41/1.03  sim_ac_normalised:                      0
% 2.41/1.03  sim_smt_subsumption:                    0
% 2.41/1.03  
%------------------------------------------------------------------------------
