%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:49 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 574 expanded)
%              Number of clauses        :   34 (  74 expanded)
%              Number of leaves         :   23 ( 177 expanded)
%              Depth                    :   15
%              Number of atoms          :  223 ( 825 expanded)
%              Number of equality atoms :  121 ( 617 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f26])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f62])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f63])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f64])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_setfam_1(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)))) != k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f51,f65,f66,f66,f66])).

fof(f72,plain,(
    ! [X1] : k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k1_setfam_1(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)))) != k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK5(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f25,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f17])).

fof(f61,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_setfam_1(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)))) = k3_enumset1(X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f52,f65,f66,f66,f66])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f30])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_485,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_476,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_483,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_484,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_913,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_484])).

cnf(c_7,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_setfam_1(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)))) != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_0,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_544,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7,c_0,c_3])).

cnf(c_1139,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_913,c_544])).

cnf(c_1149,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_476,c_1139])).

cnf(c_1208,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_485,c_1149])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(sK5(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_475,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_826,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | r2_hidden(sK5(X0),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_475])).

cnf(c_1497,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_826])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_37,plain,
    ( k5_xboole_0(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k3_enumset1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( X0 = X1
    | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k1_setfam_1(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0)))) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_38,plain,
    ( k5_xboole_0(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k3_enumset1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_164,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_610,plain,
    ( k2_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_611,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_673,plain,
    ( k1_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_674,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_480,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1147,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_480,c_1139])).

cnf(c_4224,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1497,c_15,c_37,c_38,c_611,c_674,c_1147,c_1208])).

cnf(c_4229,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4224,c_1139])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.44/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.01  
% 3.44/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/1.01  
% 3.44/1.01  ------  iProver source info
% 3.44/1.01  
% 3.44/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.44/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/1.01  git: non_committed_changes: false
% 3.44/1.01  git: last_make_outside_of_git: false
% 3.44/1.01  
% 3.44/1.01  ------ 
% 3.44/1.01  
% 3.44/1.01  ------ Input Options
% 3.44/1.01  
% 3.44/1.01  --out_options                           all
% 3.44/1.01  --tptp_safe_out                         true
% 3.44/1.01  --problem_path                          ""
% 3.44/1.01  --include_path                          ""
% 3.44/1.01  --clausifier                            res/vclausify_rel
% 3.44/1.01  --clausifier_options                    --mode clausify
% 3.44/1.01  --stdin                                 false
% 3.44/1.01  --stats_out                             sel
% 3.44/1.01  
% 3.44/1.01  ------ General Options
% 3.44/1.01  
% 3.44/1.01  --fof                                   false
% 3.44/1.01  --time_out_real                         604.99
% 3.44/1.01  --time_out_virtual                      -1.
% 3.44/1.01  --symbol_type_check                     false
% 3.44/1.01  --clausify_out                          false
% 3.44/1.01  --sig_cnt_out                           false
% 3.44/1.01  --trig_cnt_out                          false
% 3.44/1.01  --trig_cnt_out_tolerance                1.
% 3.44/1.01  --trig_cnt_out_sk_spl                   false
% 3.44/1.01  --abstr_cl_out                          false
% 3.44/1.01  
% 3.44/1.01  ------ Global Options
% 3.44/1.01  
% 3.44/1.01  --schedule                              none
% 3.44/1.01  --add_important_lit                     false
% 3.44/1.01  --prop_solver_per_cl                    1000
% 3.44/1.01  --min_unsat_core                        false
% 3.44/1.01  --soft_assumptions                      false
% 3.44/1.01  --soft_lemma_size                       3
% 3.44/1.01  --prop_impl_unit_size                   0
% 3.44/1.01  --prop_impl_unit                        []
% 3.44/1.01  --share_sel_clauses                     true
% 3.44/1.01  --reset_solvers                         false
% 3.44/1.01  --bc_imp_inh                            [conj_cone]
% 3.44/1.01  --conj_cone_tolerance                   3.
% 3.44/1.01  --extra_neg_conj                        none
% 3.44/1.01  --large_theory_mode                     true
% 3.44/1.01  --prolific_symb_bound                   200
% 3.44/1.01  --lt_threshold                          2000
% 3.44/1.01  --clause_weak_htbl                      true
% 3.44/1.01  --gc_record_bc_elim                     false
% 3.44/1.01  
% 3.44/1.01  ------ Preprocessing Options
% 3.44/1.01  
% 3.44/1.01  --preprocessing_flag                    true
% 3.44/1.01  --time_out_prep_mult                    0.1
% 3.44/1.01  --splitting_mode                        input
% 3.44/1.01  --splitting_grd                         true
% 3.44/1.01  --splitting_cvd                         false
% 3.44/1.01  --splitting_cvd_svl                     false
% 3.44/1.01  --splitting_nvd                         32
% 3.44/1.01  --sub_typing                            true
% 3.44/1.01  --prep_gs_sim                           false
% 3.44/1.01  --prep_unflatten                        true
% 3.44/1.01  --prep_res_sim                          true
% 3.44/1.01  --prep_upred                            true
% 3.44/1.01  --prep_sem_filter                       exhaustive
% 3.44/1.01  --prep_sem_filter_out                   false
% 3.44/1.01  --pred_elim                             false
% 3.44/1.01  --res_sim_input                         true
% 3.44/1.01  --eq_ax_congr_red                       true
% 3.44/1.01  --pure_diseq_elim                       true
% 3.44/1.01  --brand_transform                       false
% 3.44/1.01  --non_eq_to_eq                          false
% 3.44/1.01  --prep_def_merge                        true
% 3.44/1.01  --prep_def_merge_prop_impl              false
% 3.44/1.01  --prep_def_merge_mbd                    true
% 3.44/1.01  --prep_def_merge_tr_red                 false
% 3.44/1.01  --prep_def_merge_tr_cl                  false
% 3.44/1.01  --smt_preprocessing                     true
% 3.44/1.01  --smt_ac_axioms                         fast
% 3.44/1.01  --preprocessed_out                      false
% 3.44/1.01  --preprocessed_stats                    false
% 3.44/1.01  
% 3.44/1.01  ------ Abstraction refinement Options
% 3.44/1.01  
% 3.44/1.01  --abstr_ref                             []
% 3.44/1.01  --abstr_ref_prep                        false
% 3.44/1.01  --abstr_ref_until_sat                   false
% 3.44/1.01  --abstr_ref_sig_restrict                funpre
% 3.44/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/1.01  --abstr_ref_under                       []
% 3.44/1.01  
% 3.44/1.01  ------ SAT Options
% 3.44/1.01  
% 3.44/1.01  --sat_mode                              false
% 3.44/1.01  --sat_fm_restart_options                ""
% 3.44/1.01  --sat_gr_def                            false
% 3.44/1.01  --sat_epr_types                         true
% 3.44/1.01  --sat_non_cyclic_types                  false
% 3.44/1.01  --sat_finite_models                     false
% 3.44/1.01  --sat_fm_lemmas                         false
% 3.44/1.01  --sat_fm_prep                           false
% 3.44/1.01  --sat_fm_uc_incr                        true
% 3.44/1.01  --sat_out_model                         small
% 3.44/1.01  --sat_out_clauses                       false
% 3.44/1.01  
% 3.44/1.01  ------ QBF Options
% 3.44/1.01  
% 3.44/1.01  --qbf_mode                              false
% 3.44/1.01  --qbf_elim_univ                         false
% 3.44/1.01  --qbf_dom_inst                          none
% 3.44/1.01  --qbf_dom_pre_inst                      false
% 3.44/1.01  --qbf_sk_in                             false
% 3.44/1.01  --qbf_pred_elim                         true
% 3.44/1.01  --qbf_split                             512
% 3.44/1.01  
% 3.44/1.01  ------ BMC1 Options
% 3.44/1.01  
% 3.44/1.01  --bmc1_incremental                      false
% 3.44/1.01  --bmc1_axioms                           reachable_all
% 3.44/1.01  --bmc1_min_bound                        0
% 3.44/1.01  --bmc1_max_bound                        -1
% 3.44/1.01  --bmc1_max_bound_default                -1
% 3.44/1.01  --bmc1_symbol_reachability              true
% 3.44/1.01  --bmc1_property_lemmas                  false
% 3.44/1.01  --bmc1_k_induction                      false
% 3.44/1.01  --bmc1_non_equiv_states                 false
% 3.44/1.01  --bmc1_deadlock                         false
% 3.44/1.01  --bmc1_ucm                              false
% 3.44/1.01  --bmc1_add_unsat_core                   none
% 3.44/1.01  --bmc1_unsat_core_children              false
% 3.44/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/1.01  --bmc1_out_stat                         full
% 3.44/1.01  --bmc1_ground_init                      false
% 3.44/1.01  --bmc1_pre_inst_next_state              false
% 3.44/1.01  --bmc1_pre_inst_state                   false
% 3.44/1.01  --bmc1_pre_inst_reach_state             false
% 3.44/1.01  --bmc1_out_unsat_core                   false
% 3.44/1.01  --bmc1_aig_witness_out                  false
% 3.44/1.01  --bmc1_verbose                          false
% 3.44/1.01  --bmc1_dump_clauses_tptp                false
% 3.44/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.44/1.01  --bmc1_dump_file                        -
% 3.44/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.44/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.44/1.01  --bmc1_ucm_extend_mode                  1
% 3.44/1.01  --bmc1_ucm_init_mode                    2
% 3.44/1.01  --bmc1_ucm_cone_mode                    none
% 3.44/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.44/1.01  --bmc1_ucm_relax_model                  4
% 3.44/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.44/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/1.01  --bmc1_ucm_layered_model                none
% 3.44/1.01  --bmc1_ucm_max_lemma_size               10
% 3.44/1.01  
% 3.44/1.01  ------ AIG Options
% 3.44/1.01  
% 3.44/1.01  --aig_mode                              false
% 3.44/1.01  
% 3.44/1.01  ------ Instantiation Options
% 3.44/1.01  
% 3.44/1.01  --instantiation_flag                    true
% 3.44/1.01  --inst_sos_flag                         false
% 3.44/1.01  --inst_sos_phase                        true
% 3.44/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/1.01  --inst_lit_sel_side                     num_symb
% 3.44/1.01  --inst_solver_per_active                1400
% 3.44/1.01  --inst_solver_calls_frac                1.
% 3.44/1.01  --inst_passive_queue_type               priority_queues
% 3.44/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/1.01  --inst_passive_queues_freq              [25;2]
% 3.44/1.01  --inst_dismatching                      true
% 3.44/1.01  --inst_eager_unprocessed_to_passive     true
% 3.44/1.01  --inst_prop_sim_given                   true
% 3.44/1.01  --inst_prop_sim_new                     false
% 3.44/1.01  --inst_subs_new                         false
% 3.44/1.01  --inst_eq_res_simp                      false
% 3.44/1.01  --inst_subs_given                       false
% 3.44/1.01  --inst_orphan_elimination               true
% 3.44/1.01  --inst_learning_loop_flag               true
% 3.44/1.01  --inst_learning_start                   3000
% 3.44/1.01  --inst_learning_factor                  2
% 3.44/1.01  --inst_start_prop_sim_after_learn       3
% 3.44/1.01  --inst_sel_renew                        solver
% 3.44/1.01  --inst_lit_activity_flag                true
% 3.44/1.01  --inst_restr_to_given                   false
% 3.44/1.01  --inst_activity_threshold               500
% 3.44/1.01  --inst_out_proof                        true
% 3.44/1.01  
% 3.44/1.01  ------ Resolution Options
% 3.44/1.01  
% 3.44/1.01  --resolution_flag                       true
% 3.44/1.01  --res_lit_sel                           adaptive
% 3.44/1.01  --res_lit_sel_side                      none
% 3.44/1.01  --res_ordering                          kbo
% 3.44/1.01  --res_to_prop_solver                    active
% 3.44/1.01  --res_prop_simpl_new                    false
% 3.44/1.01  --res_prop_simpl_given                  true
% 3.44/1.01  --res_passive_queue_type                priority_queues
% 3.44/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/1.01  --res_passive_queues_freq               [15;5]
% 3.44/1.01  --res_forward_subs                      full
% 3.44/1.01  --res_backward_subs                     full
% 3.44/1.01  --res_forward_subs_resolution           true
% 3.44/1.01  --res_backward_subs_resolution          true
% 3.44/1.01  --res_orphan_elimination                true
% 3.44/1.01  --res_time_limit                        2.
% 3.44/1.01  --res_out_proof                         true
% 3.44/1.01  
% 3.44/1.01  ------ Superposition Options
% 3.44/1.01  
% 3.44/1.01  --superposition_flag                    true
% 3.44/1.01  --sup_passive_queue_type                priority_queues
% 3.44/1.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/1.01  --sup_passive_queues_freq               [1;4]
% 3.44/1.01  --demod_completeness_check              fast
% 3.44/1.01  --demod_use_ground                      true
% 3.44/1.01  --sup_to_prop_solver                    passive
% 3.44/1.01  --sup_prop_simpl_new                    true
% 3.44/1.01  --sup_prop_simpl_given                  true
% 3.44/1.01  --sup_fun_splitting                     false
% 3.44/1.01  --sup_smt_interval                      50000
% 3.44/1.01  
% 3.44/1.01  ------ Superposition Simplification Setup
% 3.44/1.01  
% 3.44/1.01  --sup_indices_passive                   []
% 3.44/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.01  --sup_full_bw                           [BwDemod]
% 3.44/1.01  --sup_immed_triv                        [TrivRules]
% 3.44/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.01  --sup_immed_bw_main                     []
% 3.44/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.01  
% 3.44/1.01  ------ Combination Options
% 3.44/1.01  
% 3.44/1.01  --comb_res_mult                         3
% 3.44/1.01  --comb_sup_mult                         2
% 3.44/1.01  --comb_inst_mult                        10
% 3.44/1.01  
% 3.44/1.01  ------ Debug Options
% 3.44/1.01  
% 3.44/1.01  --dbg_backtrace                         false
% 3.44/1.01  --dbg_dump_prop_clauses                 false
% 3.44/1.01  --dbg_dump_prop_clauses_file            -
% 3.44/1.01  --dbg_out_stat                          false
% 3.44/1.01  ------ Parsing...
% 3.44/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/1.01  
% 3.44/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.44/1.01  
% 3.44/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/1.01  
% 3.44/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/1.01  ------ Proving...
% 3.44/1.01  ------ Problem Properties 
% 3.44/1.01  
% 3.44/1.01  
% 3.44/1.01  clauses                                 16
% 3.44/1.01  conjectures                             1
% 3.44/1.01  EPR                                     1
% 3.44/1.01  Horn                                    12
% 3.44/1.01  unary                                   3
% 3.44/1.01  binary                                  10
% 3.44/1.01  lits                                    32
% 3.44/1.01  lits eq                                 12
% 3.44/1.01  fd_pure                                 0
% 3.44/1.01  fd_pseudo                               0
% 3.44/1.01  fd_cond                                 2
% 3.44/1.01  fd_pseudo_cond                          3
% 3.44/1.01  AC symbols                              0
% 3.44/1.01  
% 3.44/1.01  ------ Input Options Time Limit: Unbounded
% 3.44/1.01  
% 3.44/1.01  
% 3.44/1.01  ------ 
% 3.44/1.01  Current options:
% 3.44/1.01  ------ 
% 3.44/1.01  
% 3.44/1.01  ------ Input Options
% 3.44/1.01  
% 3.44/1.01  --out_options                           all
% 3.44/1.01  --tptp_safe_out                         true
% 3.44/1.01  --problem_path                          ""
% 3.44/1.01  --include_path                          ""
% 3.44/1.01  --clausifier                            res/vclausify_rel
% 3.44/1.01  --clausifier_options                    --mode clausify
% 3.44/1.01  --stdin                                 false
% 3.44/1.01  --stats_out                             sel
% 3.44/1.01  
% 3.44/1.01  ------ General Options
% 3.44/1.01  
% 3.44/1.01  --fof                                   false
% 3.44/1.01  --time_out_real                         604.99
% 3.44/1.01  --time_out_virtual                      -1.
% 3.44/1.01  --symbol_type_check                     false
% 3.44/1.01  --clausify_out                          false
% 3.44/1.01  --sig_cnt_out                           false
% 3.44/1.01  --trig_cnt_out                          false
% 3.44/1.01  --trig_cnt_out_tolerance                1.
% 3.44/1.01  --trig_cnt_out_sk_spl                   false
% 3.44/1.01  --abstr_cl_out                          false
% 3.44/1.01  
% 3.44/1.01  ------ Global Options
% 3.44/1.01  
% 3.44/1.01  --schedule                              none
% 3.44/1.01  --add_important_lit                     false
% 3.44/1.01  --prop_solver_per_cl                    1000
% 3.44/1.01  --min_unsat_core                        false
% 3.44/1.01  --soft_assumptions                      false
% 3.44/1.01  --soft_lemma_size                       3
% 3.44/1.01  --prop_impl_unit_size                   0
% 3.44/1.01  --prop_impl_unit                        []
% 3.44/1.01  --share_sel_clauses                     true
% 3.44/1.01  --reset_solvers                         false
% 3.44/1.01  --bc_imp_inh                            [conj_cone]
% 3.44/1.01  --conj_cone_tolerance                   3.
% 3.44/1.01  --extra_neg_conj                        none
% 3.44/1.01  --large_theory_mode                     true
% 3.44/1.01  --prolific_symb_bound                   200
% 3.44/1.01  --lt_threshold                          2000
% 3.44/1.01  --clause_weak_htbl                      true
% 3.44/1.01  --gc_record_bc_elim                     false
% 3.44/1.01  
% 3.44/1.01  ------ Preprocessing Options
% 3.44/1.01  
% 3.44/1.01  --preprocessing_flag                    true
% 3.44/1.01  --time_out_prep_mult                    0.1
% 3.44/1.01  --splitting_mode                        input
% 3.44/1.01  --splitting_grd                         true
% 3.44/1.01  --splitting_cvd                         false
% 3.44/1.01  --splitting_cvd_svl                     false
% 3.44/1.01  --splitting_nvd                         32
% 3.44/1.01  --sub_typing                            true
% 3.44/1.01  --prep_gs_sim                           false
% 3.44/1.01  --prep_unflatten                        true
% 3.44/1.01  --prep_res_sim                          true
% 3.44/1.01  --prep_upred                            true
% 3.44/1.01  --prep_sem_filter                       exhaustive
% 3.44/1.01  --prep_sem_filter_out                   false
% 3.44/1.01  --pred_elim                             false
% 3.44/1.01  --res_sim_input                         true
% 3.44/1.01  --eq_ax_congr_red                       true
% 3.44/1.01  --pure_diseq_elim                       true
% 3.44/1.01  --brand_transform                       false
% 3.44/1.01  --non_eq_to_eq                          false
% 3.44/1.01  --prep_def_merge                        true
% 3.44/1.01  --prep_def_merge_prop_impl              false
% 3.44/1.01  --prep_def_merge_mbd                    true
% 3.44/1.01  --prep_def_merge_tr_red                 false
% 3.44/1.01  --prep_def_merge_tr_cl                  false
% 3.44/1.01  --smt_preprocessing                     true
% 3.44/1.01  --smt_ac_axioms                         fast
% 3.44/1.01  --preprocessed_out                      false
% 3.44/1.01  --preprocessed_stats                    false
% 3.44/1.01  
% 3.44/1.01  ------ Abstraction refinement Options
% 3.44/1.01  
% 3.44/1.01  --abstr_ref                             []
% 3.44/1.01  --abstr_ref_prep                        false
% 3.44/1.01  --abstr_ref_until_sat                   false
% 3.44/1.01  --abstr_ref_sig_restrict                funpre
% 3.44/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/1.01  --abstr_ref_under                       []
% 3.44/1.01  
% 3.44/1.01  ------ SAT Options
% 3.44/1.01  
% 3.44/1.01  --sat_mode                              false
% 3.44/1.01  --sat_fm_restart_options                ""
% 3.44/1.01  --sat_gr_def                            false
% 3.44/1.01  --sat_epr_types                         true
% 3.44/1.01  --sat_non_cyclic_types                  false
% 3.44/1.01  --sat_finite_models                     false
% 3.44/1.01  --sat_fm_lemmas                         false
% 3.44/1.01  --sat_fm_prep                           false
% 3.44/1.01  --sat_fm_uc_incr                        true
% 3.44/1.01  --sat_out_model                         small
% 3.44/1.01  --sat_out_clauses                       false
% 3.44/1.01  
% 3.44/1.01  ------ QBF Options
% 3.44/1.01  
% 3.44/1.01  --qbf_mode                              false
% 3.44/1.01  --qbf_elim_univ                         false
% 3.44/1.01  --qbf_dom_inst                          none
% 3.44/1.01  --qbf_dom_pre_inst                      false
% 3.44/1.01  --qbf_sk_in                             false
% 3.44/1.01  --qbf_pred_elim                         true
% 3.44/1.01  --qbf_split                             512
% 3.44/1.01  
% 3.44/1.01  ------ BMC1 Options
% 3.44/1.01  
% 3.44/1.01  --bmc1_incremental                      false
% 3.44/1.01  --bmc1_axioms                           reachable_all
% 3.44/1.01  --bmc1_min_bound                        0
% 3.44/1.01  --bmc1_max_bound                        -1
% 3.44/1.01  --bmc1_max_bound_default                -1
% 3.44/1.01  --bmc1_symbol_reachability              true
% 3.44/1.01  --bmc1_property_lemmas                  false
% 3.44/1.01  --bmc1_k_induction                      false
% 3.44/1.01  --bmc1_non_equiv_states                 false
% 3.44/1.01  --bmc1_deadlock                         false
% 3.44/1.01  --bmc1_ucm                              false
% 3.44/1.01  --bmc1_add_unsat_core                   none
% 3.44/1.01  --bmc1_unsat_core_children              false
% 3.44/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/1.01  --bmc1_out_stat                         full
% 3.44/1.01  --bmc1_ground_init                      false
% 3.44/1.01  --bmc1_pre_inst_next_state              false
% 3.44/1.01  --bmc1_pre_inst_state                   false
% 3.44/1.01  --bmc1_pre_inst_reach_state             false
% 3.44/1.01  --bmc1_out_unsat_core                   false
% 3.44/1.01  --bmc1_aig_witness_out                  false
% 3.44/1.01  --bmc1_verbose                          false
% 3.44/1.01  --bmc1_dump_clauses_tptp                false
% 3.44/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.44/1.01  --bmc1_dump_file                        -
% 3.44/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.44/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.44/1.01  --bmc1_ucm_extend_mode                  1
% 3.44/1.01  --bmc1_ucm_init_mode                    2
% 3.44/1.01  --bmc1_ucm_cone_mode                    none
% 3.44/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.44/1.01  --bmc1_ucm_relax_model                  4
% 3.44/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.44/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/1.01  --bmc1_ucm_layered_model                none
% 3.44/1.01  --bmc1_ucm_max_lemma_size               10
% 3.44/1.01  
% 3.44/1.01  ------ AIG Options
% 3.44/1.01  
% 3.44/1.01  --aig_mode                              false
% 3.44/1.01  
% 3.44/1.01  ------ Instantiation Options
% 3.44/1.01  
% 3.44/1.01  --instantiation_flag                    true
% 3.44/1.01  --inst_sos_flag                         false
% 3.44/1.01  --inst_sos_phase                        true
% 3.44/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/1.01  --inst_lit_sel_side                     num_symb
% 3.44/1.01  --inst_solver_per_active                1400
% 3.44/1.01  --inst_solver_calls_frac                1.
% 3.44/1.01  --inst_passive_queue_type               priority_queues
% 3.44/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/1.01  --inst_passive_queues_freq              [25;2]
% 3.44/1.01  --inst_dismatching                      true
% 3.44/1.01  --inst_eager_unprocessed_to_passive     true
% 3.44/1.01  --inst_prop_sim_given                   true
% 3.44/1.01  --inst_prop_sim_new                     false
% 3.44/1.01  --inst_subs_new                         false
% 3.44/1.01  --inst_eq_res_simp                      false
% 3.44/1.01  --inst_subs_given                       false
% 3.44/1.01  --inst_orphan_elimination               true
% 3.44/1.01  --inst_learning_loop_flag               true
% 3.44/1.01  --inst_learning_start                   3000
% 3.44/1.01  --inst_learning_factor                  2
% 3.44/1.01  --inst_start_prop_sim_after_learn       3
% 3.44/1.01  --inst_sel_renew                        solver
% 3.44/1.01  --inst_lit_activity_flag                true
% 3.44/1.01  --inst_restr_to_given                   false
% 3.44/1.01  --inst_activity_threshold               500
% 3.44/1.01  --inst_out_proof                        true
% 3.44/1.01  
% 3.44/1.01  ------ Resolution Options
% 3.44/1.01  
% 3.44/1.01  --resolution_flag                       true
% 3.44/1.01  --res_lit_sel                           adaptive
% 3.44/1.01  --res_lit_sel_side                      none
% 3.44/1.01  --res_ordering                          kbo
% 3.44/1.01  --res_to_prop_solver                    active
% 3.44/1.01  --res_prop_simpl_new                    false
% 3.44/1.01  --res_prop_simpl_given                  true
% 3.44/1.01  --res_passive_queue_type                priority_queues
% 3.44/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/1.01  --res_passive_queues_freq               [15;5]
% 3.44/1.01  --res_forward_subs                      full
% 3.44/1.01  --res_backward_subs                     full
% 3.44/1.01  --res_forward_subs_resolution           true
% 3.44/1.01  --res_backward_subs_resolution          true
% 3.44/1.01  --res_orphan_elimination                true
% 3.44/1.01  --res_time_limit                        2.
% 3.44/1.01  --res_out_proof                         true
% 3.44/1.01  
% 3.44/1.01  ------ Superposition Options
% 3.44/1.01  
% 3.44/1.01  --superposition_flag                    true
% 3.44/1.01  --sup_passive_queue_type                priority_queues
% 3.44/1.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/1.01  --sup_passive_queues_freq               [1;4]
% 3.44/1.01  --demod_completeness_check              fast
% 3.44/1.01  --demod_use_ground                      true
% 3.44/1.01  --sup_to_prop_solver                    passive
% 3.44/1.01  --sup_prop_simpl_new                    true
% 3.44/1.01  --sup_prop_simpl_given                  true
% 3.44/1.01  --sup_fun_splitting                     false
% 3.44/1.01  --sup_smt_interval                      50000
% 3.44/1.01  
% 3.44/1.01  ------ Superposition Simplification Setup
% 3.44/1.01  
% 3.44/1.01  --sup_indices_passive                   []
% 3.44/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.01  --sup_full_bw                           [BwDemod]
% 3.44/1.01  --sup_immed_triv                        [TrivRules]
% 3.44/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.01  --sup_immed_bw_main                     []
% 3.44/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.01  
% 3.44/1.01  ------ Combination Options
% 3.44/1.01  
% 3.44/1.01  --comb_res_mult                         3
% 3.44/1.01  --comb_sup_mult                         2
% 3.44/1.01  --comb_inst_mult                        10
% 3.44/1.01  
% 3.44/1.01  ------ Debug Options
% 3.44/1.01  
% 3.44/1.01  --dbg_backtrace                         false
% 3.44/1.01  --dbg_dump_prop_clauses                 false
% 3.44/1.01  --dbg_dump_prop_clauses_file            -
% 3.44/1.01  --dbg_out_stat                          false
% 3.44/1.01  
% 3.44/1.01  
% 3.44/1.01  
% 3.44/1.01  
% 3.44/1.01  ------ Proving...
% 3.44/1.01  
% 3.44/1.01  
% 3.44/1.01  % SZS status Theorem for theBenchmark.p
% 3.44/1.01  
% 3.44/1.01   Resolution empty clause
% 3.44/1.01  
% 3.44/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/1.01  
% 3.44/1.01  fof(f2,axiom,(
% 3.44/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f20,plain,(
% 3.44/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.44/1.01    inference(ennf_transformation,[],[f2])).
% 3.44/1.01  
% 3.44/1.01  fof(f26,plain,(
% 3.44/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.44/1.01    introduced(choice_axiom,[])).
% 3.44/1.01  
% 3.44/1.01  fof(f27,plain,(
% 3.44/1.01    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 3.44/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f26])).
% 3.44/1.01  
% 3.44/1.01  fof(f41,plain,(
% 3.44/1.01    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.44/1.01    inference(cnf_transformation,[],[f27])).
% 3.44/1.01  
% 3.44/1.01  fof(f14,axiom,(
% 3.44/1.01    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f32,plain,(
% 3.44/1.01    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.44/1.01    inference(nnf_transformation,[],[f14])).
% 3.44/1.01  
% 3.44/1.01  fof(f33,plain,(
% 3.44/1.01    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.44/1.01    inference(rectify,[],[f32])).
% 3.44/1.01  
% 3.44/1.01  fof(f36,plain,(
% 3.44/1.01    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 3.44/1.01    introduced(choice_axiom,[])).
% 3.44/1.01  
% 3.44/1.01  fof(f35,plain,(
% 3.44/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0))) )),
% 3.44/1.01    introduced(choice_axiom,[])).
% 3.44/1.01  
% 3.44/1.01  fof(f34,plain,(
% 3.44/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.44/1.01    introduced(choice_axiom,[])).
% 3.44/1.01  
% 3.44/1.01  fof(f37,plain,(
% 3.44/1.01    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.44/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).
% 3.44/1.01  
% 3.44/1.01  fof(f56,plain,(
% 3.44/1.01    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.44/1.01    inference(cnf_transformation,[],[f37])).
% 3.44/1.01  
% 3.44/1.01  fof(f74,plain,(
% 3.44/1.01    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.44/1.01    inference(equality_resolution,[],[f56])).
% 3.44/1.01  
% 3.44/1.01  fof(f10,axiom,(
% 3.44/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f28,plain,(
% 3.44/1.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.44/1.01    inference(nnf_transformation,[],[f10])).
% 3.44/1.01  
% 3.44/1.01  fof(f50,plain,(
% 3.44/1.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.44/1.01    inference(cnf_transformation,[],[f28])).
% 3.44/1.01  
% 3.44/1.01  fof(f6,axiom,(
% 3.44/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f45,plain,(
% 3.44/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.44/1.01    inference(cnf_transformation,[],[f6])).
% 3.44/1.01  
% 3.44/1.01  fof(f7,axiom,(
% 3.44/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f46,plain,(
% 3.44/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.44/1.01    inference(cnf_transformation,[],[f7])).
% 3.44/1.01  
% 3.44/1.01  fof(f8,axiom,(
% 3.44/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f47,plain,(
% 3.44/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.44/1.01    inference(cnf_transformation,[],[f8])).
% 3.44/1.01  
% 3.44/1.01  fof(f9,axiom,(
% 3.44/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f48,plain,(
% 3.44/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.44/1.01    inference(cnf_transformation,[],[f9])).
% 3.44/1.01  
% 3.44/1.01  fof(f62,plain,(
% 3.44/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.44/1.01    inference(definition_unfolding,[],[f47,f48])).
% 3.44/1.01  
% 3.44/1.01  fof(f63,plain,(
% 3.44/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.44/1.01    inference(definition_unfolding,[],[f46,f62])).
% 3.44/1.01  
% 3.44/1.01  fof(f66,plain,(
% 3.44/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.44/1.01    inference(definition_unfolding,[],[f45,f63])).
% 3.44/1.01  
% 3.44/1.01  fof(f68,plain,(
% 3.44/1.01    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.44/1.01    inference(definition_unfolding,[],[f50,f66])).
% 3.44/1.01  
% 3.44/1.01  fof(f4,axiom,(
% 3.44/1.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f21,plain,(
% 3.44/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.44/1.01    inference(ennf_transformation,[],[f4])).
% 3.44/1.01  
% 3.44/1.01  fof(f43,plain,(
% 3.44/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.44/1.01    inference(cnf_transformation,[],[f21])).
% 3.44/1.01  
% 3.44/1.01  fof(f11,axiom,(
% 3.44/1.01    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f29,plain,(
% 3.44/1.01    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.44/1.01    inference(nnf_transformation,[],[f11])).
% 3.44/1.01  
% 3.44/1.01  fof(f51,plain,(
% 3.44/1.01    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.44/1.01    inference(cnf_transformation,[],[f29])).
% 3.44/1.01  
% 3.44/1.01  fof(f3,axiom,(
% 3.44/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f42,plain,(
% 3.44/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.44/1.01    inference(cnf_transformation,[],[f3])).
% 3.44/1.01  
% 3.44/1.01  fof(f12,axiom,(
% 3.44/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f53,plain,(
% 3.44/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.44/1.01    inference(cnf_transformation,[],[f12])).
% 3.44/1.01  
% 3.44/1.01  fof(f64,plain,(
% 3.44/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.44/1.01    inference(definition_unfolding,[],[f53,f63])).
% 3.44/1.01  
% 3.44/1.01  fof(f65,plain,(
% 3.44/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 3.44/1.01    inference(definition_unfolding,[],[f42,f64])).
% 3.44/1.01  
% 3.44/1.01  fof(f71,plain,(
% 3.44/1.01    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_setfam_1(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)))) != k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.44/1.01    inference(definition_unfolding,[],[f51,f65,f66,f66,f66])).
% 3.44/1.01  
% 3.44/1.01  fof(f72,plain,(
% 3.44/1.01    ( ! [X1] : (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k1_setfam_1(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)))) != k3_enumset1(X1,X1,X1,X1,X1)) )),
% 3.44/1.01    inference(equality_resolution,[],[f71])).
% 3.44/1.01  
% 3.44/1.01  fof(f1,axiom,(
% 3.44/1.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f18,plain,(
% 3.44/1.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.44/1.01    inference(rectify,[],[f1])).
% 3.44/1.01  
% 3.44/1.01  fof(f40,plain,(
% 3.44/1.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.44/1.01    inference(cnf_transformation,[],[f18])).
% 3.44/1.01  
% 3.44/1.01  fof(f67,plain,(
% 3.44/1.01    ( ! [X0] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 3.44/1.01    inference(definition_unfolding,[],[f40,f64])).
% 3.44/1.01  
% 3.44/1.01  fof(f5,axiom,(
% 3.44/1.01    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f44,plain,(
% 3.44/1.01    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.44/1.01    inference(cnf_transformation,[],[f5])).
% 3.44/1.01  
% 3.44/1.01  fof(f15,axiom,(
% 3.44/1.01    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f23,plain,(
% 3.44/1.01    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.44/1.01    inference(ennf_transformation,[],[f15])).
% 3.44/1.01  
% 3.44/1.01  fof(f24,plain,(
% 3.44/1.01    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.44/1.01    inference(flattening,[],[f23])).
% 3.44/1.01  
% 3.44/1.01  fof(f38,plain,(
% 3.44/1.01    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK5(X1),k2_relat_1(X1)))),
% 3.44/1.01    introduced(choice_axiom,[])).
% 3.44/1.01  
% 3.44/1.01  fof(f39,plain,(
% 3.44/1.01    ! [X0,X1] : (r2_hidden(sK5(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.44/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f38])).
% 3.44/1.01  
% 3.44/1.01  fof(f60,plain,(
% 3.44/1.01    ( ! [X0,X1] : (r2_hidden(sK5(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.44/1.01    inference(cnf_transformation,[],[f39])).
% 3.44/1.01  
% 3.44/1.01  fof(f16,conjecture,(
% 3.44/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f17,negated_conjecture,(
% 3.44/1.01    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 3.44/1.01    inference(negated_conjecture,[],[f16])).
% 3.44/1.01  
% 3.44/1.01  fof(f25,plain,(
% 3.44/1.01    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 3.44/1.01    inference(ennf_transformation,[],[f17])).
% 3.44/1.01  
% 3.44/1.01  fof(f61,plain,(
% 3.44/1.01    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 3.44/1.01    inference(cnf_transformation,[],[f25])).
% 3.44/1.01  
% 3.44/1.01  fof(f52,plain,(
% 3.44/1.01    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.44/1.01    inference(cnf_transformation,[],[f29])).
% 3.44/1.01  
% 3.44/1.01  fof(f70,plain,(
% 3.44/1.01    ( ! [X0,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_setfam_1(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)))) = k3_enumset1(X0,X0,X0,X0,X0) | X0 = X1) )),
% 3.44/1.01    inference(definition_unfolding,[],[f52,f65,f66,f66,f66])).
% 3.44/1.01  
% 3.44/1.01  fof(f13,axiom,(
% 3.44/1.01    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 3.44/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.01  
% 3.44/1.01  fof(f19,plain,(
% 3.44/1.01    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 3.44/1.01    inference(unused_predicate_definition_removal,[],[f13])).
% 3.44/1.01  
% 3.44/1.01  fof(f22,plain,(
% 3.44/1.01    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 3.44/1.01    inference(ennf_transformation,[],[f19])).
% 3.44/1.01  
% 3.44/1.01  fof(f30,plain,(
% 3.44/1.01    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 3.44/1.01    introduced(choice_axiom,[])).
% 3.44/1.01  
% 3.44/1.01  fof(f31,plain,(
% 3.44/1.01    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 3.44/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f30])).
% 3.44/1.01  
% 3.44/1.01  fof(f54,plain,(
% 3.44/1.01    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 3.44/1.01    inference(cnf_transformation,[],[f31])).
% 3.44/1.01  
% 3.44/1.01  cnf(c_1,plain,
% 3.44/1.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.44/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_485,plain,
% 3.44/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.44/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_13,plain,
% 3.44/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.44/1.01      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
% 3.44/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_476,plain,
% 3.44/1.01      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.44/1.01      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) = iProver_top ),
% 3.44/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_4,plain,
% 3.44/1.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.44/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_483,plain,
% 3.44/1.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
% 3.44/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 3.44/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_2,plain,
% 3.44/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.44/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_484,plain,
% 3.44/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.44/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_913,plain,
% 3.44/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k1_xboole_0
% 3.44/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.44/1.01      inference(superposition,[status(thm)],[c_483,c_484]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_7,plain,
% 3.44/1.01      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_setfam_1(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)))) != k3_enumset1(X0,X0,X0,X0,X0) ),
% 3.44/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_0,plain,
% 3.44/1.01      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
% 3.44/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_3,plain,
% 3.44/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.44/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_544,plain,
% 3.44/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 3.44/1.01      inference(demodulation,[status(thm)],[c_7,c_0,c_3]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_1139,plain,
% 3.44/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.44/1.01      inference(global_propositional_subsumption,[status(thm)],[c_913,c_544]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_1149,plain,
% 3.44/1.01      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 3.44/1.01      inference(superposition,[status(thm)],[c_476,c_1139]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_1208,plain,
% 3.44/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.44/1.01      inference(superposition,[status(thm)],[c_485,c_1149]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_14,plain,
% 3.44/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.44/1.01      | r2_hidden(sK5(X1),k2_relat_1(X1))
% 3.44/1.01      | ~ v1_relat_1(X1) ),
% 3.44/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_475,plain,
% 3.44/1.01      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.44/1.01      | r2_hidden(sK5(X1),k2_relat_1(X1)) = iProver_top
% 3.44/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.44/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_826,plain,
% 3.44/1.01      ( k1_relat_1(X0) = k1_xboole_0
% 3.44/1.01      | r2_hidden(sK5(X0),k2_relat_1(X0)) = iProver_top
% 3.44/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.44/1.01      inference(superposition,[status(thm)],[c_485,c_475]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_1497,plain,
% 3.44/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 3.44/1.01      | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
% 3.44/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.44/1.01      inference(superposition,[status(thm)],[c_1208,c_826]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_15,negated_conjecture,
% 3.44/1.01      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
% 3.44/1.01      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 3.44/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_37,plain,
% 3.44/1.01      ( k5_xboole_0(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k3_enumset1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 3.44/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_6,plain,
% 3.44/1.01      ( X0 = X1
% 3.44/1.01      | k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k1_setfam_1(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0)))) = k3_enumset1(X1,X1,X1,X1,X1) ),
% 3.44/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_38,plain,
% 3.44/1.01      ( k5_xboole_0(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k3_enumset1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.44/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.44/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_164,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_610,plain,
% 3.44/1.01      ( k2_relat_1(k1_xboole_0) != X0
% 3.44/1.01      | k1_xboole_0 != X0
% 3.44/1.01      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 3.44/1.01      inference(instantiation,[status(thm)],[c_164]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_611,plain,
% 3.44/1.01      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 3.44/1.01      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 3.44/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.44/1.01      inference(instantiation,[status(thm)],[c_610]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_673,plain,
% 3.44/1.01      ( k1_relat_1(k1_xboole_0) != X0
% 3.44/1.01      | k1_xboole_0 != X0
% 3.44/1.01      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 3.44/1.01      inference(instantiation,[status(thm)],[c_164]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_674,plain,
% 3.44/1.01      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 3.44/1.01      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 3.44/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.44/1.01      inference(instantiation,[status(thm)],[c_673]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_9,plain,
% 3.44/1.01      ( r2_hidden(sK1(X0),X0) | v1_relat_1(X0) ),
% 3.44/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_480,plain,
% 3.44/1.01      ( r2_hidden(sK1(X0),X0) = iProver_top | v1_relat_1(X0) = iProver_top ),
% 3.44/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_1147,plain,
% 3.44/1.01      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.44/1.01      inference(superposition,[status(thm)],[c_480,c_1139]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_4224,plain,
% 3.44/1.01      ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.44/1.01      inference(global_propositional_subsumption,
% 3.44/1.01                [status(thm)],
% 3.44/1.01                [c_1497,c_15,c_37,c_38,c_611,c_674,c_1147,c_1208]) ).
% 3.44/1.01  
% 3.44/1.01  cnf(c_4229,plain,
% 3.44/1.01      ( $false ),
% 3.44/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4224,c_1139]) ).
% 3.44/1.01  
% 3.44/1.01  
% 3.44/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/1.01  
% 3.44/1.01  ------                               Statistics
% 3.44/1.01  
% 3.44/1.01  ------ Selected
% 3.44/1.01  
% 3.44/1.01  total_time:                             0.198
% 3.44/1.01  
%------------------------------------------------------------------------------
