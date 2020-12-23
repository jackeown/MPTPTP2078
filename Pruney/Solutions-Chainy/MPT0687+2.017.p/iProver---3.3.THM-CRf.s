%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:33 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 388 expanded)
%              Number of clauses        :   52 (  84 expanded)
%              Number of leaves         :   14 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          :  322 (1153 expanded)
%              Number of equality atoms :  109 ( 372 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0
        | ~ r2_hidden(sK2,k2_relat_1(sK3)) )
      & ( k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0
        | r2_hidden(sK2,k2_relat_1(sK3)) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0
      | ~ r2_hidden(sK2,k2_relat_1(sK3)) )
    & ( k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0
      | r2_hidden(sK2,k2_relat_1(sK3)) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f30])).

fof(f53,plain,
    ( k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0
    | ~ r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
    | ~ r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,
    ( k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0
    | r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0
    | r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) != k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,plain,
    ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1398,plain,
    ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1399,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1767,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_1399])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK2,k2_relat_1(sK3))
    | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1396,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
    | r2_hidden(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3417,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
    | k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k2_relat_1(sK3)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1767,c_1396])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_261,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | k10_relat_1(X0,X1) = k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_262,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK3),X0)
    | k10_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_619,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK3),X0)
    | k10_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_262])).

cnf(c_1526,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1545,plain,
    ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1544,plain,
    ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2024,plain,
    ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k2_relat_1(sK3))
    | r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1639,plain,
    ( ~ r1_xboole_0(X0,k2_relat_1(sK3))
    | ~ r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),X0)
    | ~ r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2375,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k2_relat_1(sK3))
    | ~ r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1639])).

cnf(c_3676,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3417,c_15,c_1526,c_1545,c_1544,c_2024,c_2375])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1395,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0
    | r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3679,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3676,c_1395])).

cnf(c_3747,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3679])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1406,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1401,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1402,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1405,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1749,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_1405])).

cnf(c_1908,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1749])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1397,plain,
    ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1923,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_1397])).

cnf(c_2091,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1406,c_1923])).

cnf(c_3750,plain,
    ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3747,c_2091])).

cnf(c_3752,plain,
    ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3750])).

cnf(c_1865,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(X0,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1866,plain,
    ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1865])).

cnf(c_1868,plain,
    ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_14,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_249,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | k10_relat_1(X0,X1) != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_250,plain,
    ( r1_xboole_0(k2_relat_1(sK3),X0)
    | k10_relat_1(sK3,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_617,plain,
    ( r1_xboole_0(k2_relat_1(sK3),X0)
    | k10_relat_1(sK3,X0) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_250])).

cnf(c_1557,plain,
    ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_1558,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(c_19,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0
    | r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3752,c_3676,c_1868,c_1558,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:47:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.23/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/0.95  
% 2.23/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.23/0.95  
% 2.23/0.95  ------  iProver source info
% 2.23/0.95  
% 2.23/0.95  git: date: 2020-06-30 10:37:57 +0100
% 2.23/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.23/0.95  git: non_committed_changes: false
% 2.23/0.95  git: last_make_outside_of_git: false
% 2.23/0.95  
% 2.23/0.95  ------ 
% 2.23/0.95  
% 2.23/0.95  ------ Input Options
% 2.23/0.95  
% 2.23/0.95  --out_options                           all
% 2.23/0.95  --tptp_safe_out                         true
% 2.23/0.95  --problem_path                          ""
% 2.23/0.95  --include_path                          ""
% 2.23/0.95  --clausifier                            res/vclausify_rel
% 2.23/0.95  --clausifier_options                    --mode clausify
% 2.23/0.95  --stdin                                 false
% 2.23/0.95  --stats_out                             all
% 2.23/0.95  
% 2.23/0.95  ------ General Options
% 2.23/0.95  
% 2.23/0.95  --fof                                   false
% 2.23/0.95  --time_out_real                         305.
% 2.23/0.95  --time_out_virtual                      -1.
% 2.23/0.95  --symbol_type_check                     false
% 2.23/0.95  --clausify_out                          false
% 2.23/0.95  --sig_cnt_out                           false
% 2.23/0.95  --trig_cnt_out                          false
% 2.23/0.95  --trig_cnt_out_tolerance                1.
% 2.23/0.95  --trig_cnt_out_sk_spl                   false
% 2.23/0.95  --abstr_cl_out                          false
% 2.23/0.95  
% 2.23/0.95  ------ Global Options
% 2.23/0.95  
% 2.23/0.95  --schedule                              default
% 2.23/0.95  --add_important_lit                     false
% 2.23/0.95  --prop_solver_per_cl                    1000
% 2.23/0.95  --min_unsat_core                        false
% 2.23/0.95  --soft_assumptions                      false
% 2.23/0.95  --soft_lemma_size                       3
% 2.23/0.95  --prop_impl_unit_size                   0
% 2.23/0.95  --prop_impl_unit                        []
% 2.23/0.95  --share_sel_clauses                     true
% 2.23/0.95  --reset_solvers                         false
% 2.23/0.95  --bc_imp_inh                            [conj_cone]
% 2.23/0.95  --conj_cone_tolerance                   3.
% 2.23/0.95  --extra_neg_conj                        none
% 2.23/0.95  --large_theory_mode                     true
% 2.23/0.95  --prolific_symb_bound                   200
% 2.23/0.95  --lt_threshold                          2000
% 2.23/0.95  --clause_weak_htbl                      true
% 2.23/0.95  --gc_record_bc_elim                     false
% 2.23/0.95  
% 2.23/0.95  ------ Preprocessing Options
% 2.23/0.95  
% 2.23/0.95  --preprocessing_flag                    true
% 2.23/0.95  --time_out_prep_mult                    0.1
% 2.23/0.95  --splitting_mode                        input
% 2.23/0.95  --splitting_grd                         true
% 2.23/0.95  --splitting_cvd                         false
% 2.23/0.95  --splitting_cvd_svl                     false
% 2.23/0.95  --splitting_nvd                         32
% 2.23/0.95  --sub_typing                            true
% 2.23/0.95  --prep_gs_sim                           true
% 2.23/0.95  --prep_unflatten                        true
% 2.23/0.95  --prep_res_sim                          true
% 2.23/0.95  --prep_upred                            true
% 2.23/0.95  --prep_sem_filter                       exhaustive
% 2.23/0.95  --prep_sem_filter_out                   false
% 2.23/0.95  --pred_elim                             true
% 2.23/0.95  --res_sim_input                         true
% 2.23/0.95  --eq_ax_congr_red                       true
% 2.23/0.95  --pure_diseq_elim                       true
% 2.23/0.95  --brand_transform                       false
% 2.23/0.95  --non_eq_to_eq                          false
% 2.23/0.95  --prep_def_merge                        true
% 2.23/0.95  --prep_def_merge_prop_impl              false
% 2.23/0.95  --prep_def_merge_mbd                    true
% 2.23/0.95  --prep_def_merge_tr_red                 false
% 2.23/0.95  --prep_def_merge_tr_cl                  false
% 2.23/0.95  --smt_preprocessing                     true
% 2.23/0.95  --smt_ac_axioms                         fast
% 2.23/0.95  --preprocessed_out                      false
% 2.23/0.95  --preprocessed_stats                    false
% 2.23/0.95  
% 2.23/0.95  ------ Abstraction refinement Options
% 2.23/0.95  
% 2.23/0.95  --abstr_ref                             []
% 2.23/0.95  --abstr_ref_prep                        false
% 2.23/0.95  --abstr_ref_until_sat                   false
% 2.23/0.95  --abstr_ref_sig_restrict                funpre
% 2.23/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/0.95  --abstr_ref_under                       []
% 2.23/0.95  
% 2.23/0.95  ------ SAT Options
% 2.23/0.95  
% 2.23/0.95  --sat_mode                              false
% 2.23/0.95  --sat_fm_restart_options                ""
% 2.23/0.95  --sat_gr_def                            false
% 2.23/0.95  --sat_epr_types                         true
% 2.23/0.95  --sat_non_cyclic_types                  false
% 2.23/0.95  --sat_finite_models                     false
% 2.23/0.95  --sat_fm_lemmas                         false
% 2.23/0.95  --sat_fm_prep                           false
% 2.23/0.95  --sat_fm_uc_incr                        true
% 2.23/0.95  --sat_out_model                         small
% 2.23/0.95  --sat_out_clauses                       false
% 2.23/0.95  
% 2.23/0.95  ------ QBF Options
% 2.23/0.95  
% 2.23/0.95  --qbf_mode                              false
% 2.23/0.95  --qbf_elim_univ                         false
% 2.23/0.95  --qbf_dom_inst                          none
% 2.23/0.95  --qbf_dom_pre_inst                      false
% 2.23/0.95  --qbf_sk_in                             false
% 2.23/0.95  --qbf_pred_elim                         true
% 2.23/0.95  --qbf_split                             512
% 2.23/0.95  
% 2.23/0.95  ------ BMC1 Options
% 2.23/0.95  
% 2.23/0.95  --bmc1_incremental                      false
% 2.23/0.95  --bmc1_axioms                           reachable_all
% 2.23/0.95  --bmc1_min_bound                        0
% 2.23/0.95  --bmc1_max_bound                        -1
% 2.23/0.95  --bmc1_max_bound_default                -1
% 2.23/0.95  --bmc1_symbol_reachability              true
% 2.23/0.95  --bmc1_property_lemmas                  false
% 2.23/0.95  --bmc1_k_induction                      false
% 2.23/0.95  --bmc1_non_equiv_states                 false
% 2.23/0.95  --bmc1_deadlock                         false
% 2.23/0.95  --bmc1_ucm                              false
% 2.23/0.95  --bmc1_add_unsat_core                   none
% 2.23/0.95  --bmc1_unsat_core_children              false
% 2.23/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/0.95  --bmc1_out_stat                         full
% 2.23/0.95  --bmc1_ground_init                      false
% 2.23/0.95  --bmc1_pre_inst_next_state              false
% 2.23/0.95  --bmc1_pre_inst_state                   false
% 2.23/0.95  --bmc1_pre_inst_reach_state             false
% 2.23/0.95  --bmc1_out_unsat_core                   false
% 2.23/0.95  --bmc1_aig_witness_out                  false
% 2.23/0.95  --bmc1_verbose                          false
% 2.23/0.95  --bmc1_dump_clauses_tptp                false
% 2.23/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.23/0.95  --bmc1_dump_file                        -
% 2.23/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.23/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.23/0.95  --bmc1_ucm_extend_mode                  1
% 2.23/0.95  --bmc1_ucm_init_mode                    2
% 2.23/0.95  --bmc1_ucm_cone_mode                    none
% 2.23/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.23/0.95  --bmc1_ucm_relax_model                  4
% 2.23/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.23/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/0.95  --bmc1_ucm_layered_model                none
% 2.23/0.95  --bmc1_ucm_max_lemma_size               10
% 2.23/0.95  
% 2.23/0.95  ------ AIG Options
% 2.23/0.95  
% 2.23/0.95  --aig_mode                              false
% 2.23/0.95  
% 2.23/0.95  ------ Instantiation Options
% 2.23/0.95  
% 2.23/0.95  --instantiation_flag                    true
% 2.23/0.95  --inst_sos_flag                         false
% 2.23/0.95  --inst_sos_phase                        true
% 2.23/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/0.95  --inst_lit_sel_side                     num_symb
% 2.23/0.95  --inst_solver_per_active                1400
% 2.23/0.95  --inst_solver_calls_frac                1.
% 2.23/0.95  --inst_passive_queue_type               priority_queues
% 2.23/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/0.95  --inst_passive_queues_freq              [25;2]
% 2.23/0.95  --inst_dismatching                      true
% 2.23/0.95  --inst_eager_unprocessed_to_passive     true
% 2.23/0.95  --inst_prop_sim_given                   true
% 2.23/0.95  --inst_prop_sim_new                     false
% 2.23/0.95  --inst_subs_new                         false
% 2.23/0.95  --inst_eq_res_simp                      false
% 2.23/0.95  --inst_subs_given                       false
% 2.23/0.95  --inst_orphan_elimination               true
% 2.23/0.95  --inst_learning_loop_flag               true
% 2.23/0.95  --inst_learning_start                   3000
% 2.23/0.95  --inst_learning_factor                  2
% 2.23/0.95  --inst_start_prop_sim_after_learn       3
% 2.23/0.95  --inst_sel_renew                        solver
% 2.23/0.95  --inst_lit_activity_flag                true
% 2.23/0.95  --inst_restr_to_given                   false
% 2.23/0.95  --inst_activity_threshold               500
% 2.23/0.95  --inst_out_proof                        true
% 2.23/0.95  
% 2.23/0.95  ------ Resolution Options
% 2.23/0.95  
% 2.23/0.95  --resolution_flag                       true
% 2.23/0.95  --res_lit_sel                           adaptive
% 2.23/0.95  --res_lit_sel_side                      none
% 2.23/0.95  --res_ordering                          kbo
% 2.23/0.95  --res_to_prop_solver                    active
% 2.23/0.95  --res_prop_simpl_new                    false
% 2.23/0.95  --res_prop_simpl_given                  true
% 2.23/0.95  --res_passive_queue_type                priority_queues
% 2.23/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/0.95  --res_passive_queues_freq               [15;5]
% 2.23/0.95  --res_forward_subs                      full
% 2.23/0.95  --res_backward_subs                     full
% 2.23/0.95  --res_forward_subs_resolution           true
% 2.23/0.95  --res_backward_subs_resolution          true
% 2.23/0.95  --res_orphan_elimination                true
% 2.23/0.95  --res_time_limit                        2.
% 2.23/0.95  --res_out_proof                         true
% 2.23/0.95  
% 2.23/0.95  ------ Superposition Options
% 2.23/0.95  
% 2.23/0.95  --superposition_flag                    true
% 2.23/0.95  --sup_passive_queue_type                priority_queues
% 2.23/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.23/0.95  --demod_completeness_check              fast
% 2.23/0.95  --demod_use_ground                      true
% 2.23/0.95  --sup_to_prop_solver                    passive
% 2.23/0.95  --sup_prop_simpl_new                    true
% 2.23/0.95  --sup_prop_simpl_given                  true
% 2.23/0.95  --sup_fun_splitting                     false
% 2.23/0.95  --sup_smt_interval                      50000
% 2.23/0.95  
% 2.23/0.95  ------ Superposition Simplification Setup
% 2.23/0.95  
% 2.23/0.95  --sup_indices_passive                   []
% 2.23/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.95  --sup_full_bw                           [BwDemod]
% 2.23/0.95  --sup_immed_triv                        [TrivRules]
% 2.23/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.95  --sup_immed_bw_main                     []
% 2.23/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.95  
% 2.23/0.95  ------ Combination Options
% 2.23/0.95  
% 2.23/0.95  --comb_res_mult                         3
% 2.23/0.95  --comb_sup_mult                         2
% 2.23/0.95  --comb_inst_mult                        10
% 2.23/0.95  
% 2.23/0.95  ------ Debug Options
% 2.23/0.95  
% 2.23/0.95  --dbg_backtrace                         false
% 2.23/0.95  --dbg_dump_prop_clauses                 false
% 2.23/0.95  --dbg_dump_prop_clauses_file            -
% 2.23/0.95  --dbg_out_stat                          false
% 2.23/0.95  ------ Parsing...
% 2.23/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.23/0.95  
% 2.23/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.23/0.95  
% 2.23/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.23/0.95  
% 2.23/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.23/0.95  ------ Proving...
% 2.23/0.95  ------ Problem Properties 
% 2.23/0.95  
% 2.23/0.95  
% 2.23/0.95  clauses                                 17
% 2.23/0.95  conjectures                             2
% 2.23/0.95  EPR                                     1
% 2.23/0.95  Horn                                    10
% 2.23/0.95  unary                                   0
% 2.23/0.95  binary                                  12
% 2.23/0.95  lits                                    40
% 2.23/0.95  lits eq                                 9
% 2.23/0.95  fd_pure                                 0
% 2.23/0.95  fd_pseudo                               0
% 2.23/0.95  fd_cond                                 0
% 2.23/0.95  fd_pseudo_cond                          3
% 2.23/0.95  AC symbols                              0
% 2.23/0.95  
% 2.23/0.95  ------ Schedule dynamic 5 is on 
% 2.23/0.95  
% 2.23/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.23/0.95  
% 2.23/0.95  
% 2.23/0.95  ------ 
% 2.23/0.95  Current options:
% 2.23/0.95  ------ 
% 2.23/0.95  
% 2.23/0.95  ------ Input Options
% 2.23/0.95  
% 2.23/0.95  --out_options                           all
% 2.23/0.95  --tptp_safe_out                         true
% 2.23/0.95  --problem_path                          ""
% 2.23/0.95  --include_path                          ""
% 2.23/0.95  --clausifier                            res/vclausify_rel
% 2.23/0.95  --clausifier_options                    --mode clausify
% 2.23/0.95  --stdin                                 false
% 2.23/0.95  --stats_out                             all
% 2.23/0.95  
% 2.23/0.95  ------ General Options
% 2.23/0.95  
% 2.23/0.95  --fof                                   false
% 2.23/0.95  --time_out_real                         305.
% 2.23/0.95  --time_out_virtual                      -1.
% 2.23/0.95  --symbol_type_check                     false
% 2.23/0.95  --clausify_out                          false
% 2.23/0.95  --sig_cnt_out                           false
% 2.23/0.95  --trig_cnt_out                          false
% 2.23/0.95  --trig_cnt_out_tolerance                1.
% 2.23/0.95  --trig_cnt_out_sk_spl                   false
% 2.23/0.95  --abstr_cl_out                          false
% 2.23/0.95  
% 2.23/0.95  ------ Global Options
% 2.23/0.95  
% 2.23/0.95  --schedule                              default
% 2.23/0.95  --add_important_lit                     false
% 2.23/0.95  --prop_solver_per_cl                    1000
% 2.23/0.95  --min_unsat_core                        false
% 2.23/0.95  --soft_assumptions                      false
% 2.23/0.95  --soft_lemma_size                       3
% 2.23/0.95  --prop_impl_unit_size                   0
% 2.23/0.95  --prop_impl_unit                        []
% 2.23/0.95  --share_sel_clauses                     true
% 2.23/0.95  --reset_solvers                         false
% 2.23/0.95  --bc_imp_inh                            [conj_cone]
% 2.23/0.95  --conj_cone_tolerance                   3.
% 2.23/0.95  --extra_neg_conj                        none
% 2.23/0.95  --large_theory_mode                     true
% 2.23/0.95  --prolific_symb_bound                   200
% 2.23/0.95  --lt_threshold                          2000
% 2.23/0.95  --clause_weak_htbl                      true
% 2.23/0.95  --gc_record_bc_elim                     false
% 2.23/0.95  
% 2.23/0.95  ------ Preprocessing Options
% 2.23/0.95  
% 2.23/0.95  --preprocessing_flag                    true
% 2.23/0.95  --time_out_prep_mult                    0.1
% 2.23/0.95  --splitting_mode                        input
% 2.23/0.95  --splitting_grd                         true
% 2.23/0.95  --splitting_cvd                         false
% 2.23/0.95  --splitting_cvd_svl                     false
% 2.23/0.95  --splitting_nvd                         32
% 2.23/0.95  --sub_typing                            true
% 2.23/0.95  --prep_gs_sim                           true
% 2.23/0.95  --prep_unflatten                        true
% 2.23/0.95  --prep_res_sim                          true
% 2.23/0.95  --prep_upred                            true
% 2.23/0.95  --prep_sem_filter                       exhaustive
% 2.23/0.95  --prep_sem_filter_out                   false
% 2.23/0.95  --pred_elim                             true
% 2.23/0.95  --res_sim_input                         true
% 2.23/0.95  --eq_ax_congr_red                       true
% 2.23/0.95  --pure_diseq_elim                       true
% 2.23/0.95  --brand_transform                       false
% 2.23/0.95  --non_eq_to_eq                          false
% 2.23/0.95  --prep_def_merge                        true
% 2.23/0.95  --prep_def_merge_prop_impl              false
% 2.23/0.95  --prep_def_merge_mbd                    true
% 2.23/0.95  --prep_def_merge_tr_red                 false
% 2.23/0.95  --prep_def_merge_tr_cl                  false
% 2.23/0.95  --smt_preprocessing                     true
% 2.23/0.95  --smt_ac_axioms                         fast
% 2.23/0.95  --preprocessed_out                      false
% 2.23/0.95  --preprocessed_stats                    false
% 2.23/0.95  
% 2.23/0.95  ------ Abstraction refinement Options
% 2.23/0.95  
% 2.23/0.95  --abstr_ref                             []
% 2.23/0.95  --abstr_ref_prep                        false
% 2.23/0.95  --abstr_ref_until_sat                   false
% 2.23/0.95  --abstr_ref_sig_restrict                funpre
% 2.23/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/0.95  --abstr_ref_under                       []
% 2.23/0.95  
% 2.23/0.95  ------ SAT Options
% 2.23/0.95  
% 2.23/0.95  --sat_mode                              false
% 2.23/0.95  --sat_fm_restart_options                ""
% 2.23/0.95  --sat_gr_def                            false
% 2.23/0.95  --sat_epr_types                         true
% 2.23/0.95  --sat_non_cyclic_types                  false
% 2.23/0.95  --sat_finite_models                     false
% 2.23/0.95  --sat_fm_lemmas                         false
% 2.23/0.95  --sat_fm_prep                           false
% 2.23/0.95  --sat_fm_uc_incr                        true
% 2.23/0.95  --sat_out_model                         small
% 2.23/0.95  --sat_out_clauses                       false
% 2.23/0.95  
% 2.23/0.95  ------ QBF Options
% 2.23/0.95  
% 2.23/0.95  --qbf_mode                              false
% 2.23/0.95  --qbf_elim_univ                         false
% 2.23/0.95  --qbf_dom_inst                          none
% 2.23/0.95  --qbf_dom_pre_inst                      false
% 2.23/0.95  --qbf_sk_in                             false
% 2.23/0.95  --qbf_pred_elim                         true
% 2.23/0.95  --qbf_split                             512
% 2.23/0.95  
% 2.23/0.95  ------ BMC1 Options
% 2.23/0.95  
% 2.23/0.95  --bmc1_incremental                      false
% 2.23/0.95  --bmc1_axioms                           reachable_all
% 2.23/0.95  --bmc1_min_bound                        0
% 2.23/0.95  --bmc1_max_bound                        -1
% 2.23/0.95  --bmc1_max_bound_default                -1
% 2.23/0.95  --bmc1_symbol_reachability              true
% 2.23/0.95  --bmc1_property_lemmas                  false
% 2.23/0.95  --bmc1_k_induction                      false
% 2.23/0.95  --bmc1_non_equiv_states                 false
% 2.23/0.95  --bmc1_deadlock                         false
% 2.23/0.95  --bmc1_ucm                              false
% 2.23/0.95  --bmc1_add_unsat_core                   none
% 2.23/0.95  --bmc1_unsat_core_children              false
% 2.23/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/0.95  --bmc1_out_stat                         full
% 2.23/0.95  --bmc1_ground_init                      false
% 2.23/0.95  --bmc1_pre_inst_next_state              false
% 2.23/0.95  --bmc1_pre_inst_state                   false
% 2.23/0.95  --bmc1_pre_inst_reach_state             false
% 2.23/0.95  --bmc1_out_unsat_core                   false
% 2.23/0.95  --bmc1_aig_witness_out                  false
% 2.23/0.95  --bmc1_verbose                          false
% 2.23/0.95  --bmc1_dump_clauses_tptp                false
% 2.23/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.23/0.95  --bmc1_dump_file                        -
% 2.23/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.23/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.23/0.95  --bmc1_ucm_extend_mode                  1
% 2.23/0.95  --bmc1_ucm_init_mode                    2
% 2.23/0.95  --bmc1_ucm_cone_mode                    none
% 2.23/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.23/0.95  --bmc1_ucm_relax_model                  4
% 2.23/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.23/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/0.95  --bmc1_ucm_layered_model                none
% 2.23/0.95  --bmc1_ucm_max_lemma_size               10
% 2.23/0.95  
% 2.23/0.95  ------ AIG Options
% 2.23/0.95  
% 2.23/0.95  --aig_mode                              false
% 2.23/0.95  
% 2.23/0.95  ------ Instantiation Options
% 2.23/0.95  
% 2.23/0.95  --instantiation_flag                    true
% 2.23/0.95  --inst_sos_flag                         false
% 2.23/0.95  --inst_sos_phase                        true
% 2.23/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/0.95  --inst_lit_sel_side                     none
% 2.23/0.95  --inst_solver_per_active                1400
% 2.23/0.95  --inst_solver_calls_frac                1.
% 2.23/0.95  --inst_passive_queue_type               priority_queues
% 2.23/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/0.95  --inst_passive_queues_freq              [25;2]
% 2.23/0.95  --inst_dismatching                      true
% 2.23/0.95  --inst_eager_unprocessed_to_passive     true
% 2.23/0.95  --inst_prop_sim_given                   true
% 2.23/0.95  --inst_prop_sim_new                     false
% 2.23/0.95  --inst_subs_new                         false
% 2.23/0.95  --inst_eq_res_simp                      false
% 2.23/0.95  --inst_subs_given                       false
% 2.23/0.95  --inst_orphan_elimination               true
% 2.23/0.95  --inst_learning_loop_flag               true
% 2.23/0.95  --inst_learning_start                   3000
% 2.23/0.95  --inst_learning_factor                  2
% 2.23/0.95  --inst_start_prop_sim_after_learn       3
% 2.23/0.95  --inst_sel_renew                        solver
% 2.23/0.95  --inst_lit_activity_flag                true
% 2.23/0.95  --inst_restr_to_given                   false
% 2.23/0.95  --inst_activity_threshold               500
% 2.23/0.95  --inst_out_proof                        true
% 2.23/0.95  
% 2.23/0.95  ------ Resolution Options
% 2.23/0.95  
% 2.23/0.95  --resolution_flag                       false
% 2.23/0.95  --res_lit_sel                           adaptive
% 2.23/0.95  --res_lit_sel_side                      none
% 2.23/0.95  --res_ordering                          kbo
% 2.23/0.95  --res_to_prop_solver                    active
% 2.23/0.95  --res_prop_simpl_new                    false
% 2.23/0.95  --res_prop_simpl_given                  true
% 2.23/0.95  --res_passive_queue_type                priority_queues
% 2.23/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/0.95  --res_passive_queues_freq               [15;5]
% 2.23/0.95  --res_forward_subs                      full
% 2.23/0.95  --res_backward_subs                     full
% 2.23/0.95  --res_forward_subs_resolution           true
% 2.23/0.95  --res_backward_subs_resolution          true
% 2.23/0.95  --res_orphan_elimination                true
% 2.23/0.95  --res_time_limit                        2.
% 2.23/0.95  --res_out_proof                         true
% 2.23/0.95  
% 2.23/0.95  ------ Superposition Options
% 2.23/0.95  
% 2.23/0.95  --superposition_flag                    true
% 2.23/0.95  --sup_passive_queue_type                priority_queues
% 2.23/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.23/0.95  --demod_completeness_check              fast
% 2.23/0.95  --demod_use_ground                      true
% 2.23/0.95  --sup_to_prop_solver                    passive
% 2.23/0.95  --sup_prop_simpl_new                    true
% 2.23/0.95  --sup_prop_simpl_given                  true
% 2.23/0.95  --sup_fun_splitting                     false
% 2.23/0.95  --sup_smt_interval                      50000
% 2.23/0.95  
% 2.23/0.95  ------ Superposition Simplification Setup
% 2.23/0.95  
% 2.23/0.95  --sup_indices_passive                   []
% 2.23/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.95  --sup_full_bw                           [BwDemod]
% 2.23/0.95  --sup_immed_triv                        [TrivRules]
% 2.23/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.95  --sup_immed_bw_main                     []
% 2.23/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.95  
% 2.23/0.95  ------ Combination Options
% 2.23/0.95  
% 2.23/0.95  --comb_res_mult                         3
% 2.23/0.95  --comb_sup_mult                         2
% 2.23/0.95  --comb_inst_mult                        10
% 2.23/0.95  
% 2.23/0.95  ------ Debug Options
% 2.23/0.95  
% 2.23/0.95  --dbg_backtrace                         false
% 2.23/0.95  --dbg_dump_prop_clauses                 false
% 2.23/0.95  --dbg_dump_prop_clauses_file            -
% 2.23/0.95  --dbg_out_stat                          false
% 2.23/0.95  
% 2.23/0.95  
% 2.23/0.95  
% 2.23/0.95  
% 2.23/0.95  ------ Proving...
% 2.23/0.95  
% 2.23/0.95  
% 2.23/0.95  % SZS status Theorem for theBenchmark.p
% 2.23/0.95  
% 2.23/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.23/0.95  
% 2.23/0.95  fof(f8,axiom,(
% 2.23/0.95    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f15,plain,(
% 2.23/0.95    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.23/0.95    inference(ennf_transformation,[],[f8])).
% 2.23/0.95  
% 2.23/0.95  fof(f47,plain,(
% 2.23/0.95    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f15])).
% 2.23/0.95  
% 2.23/0.95  fof(f4,axiom,(
% 2.23/0.95    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f43,plain,(
% 2.23/0.95    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f4])).
% 2.23/0.95  
% 2.23/0.95  fof(f5,axiom,(
% 2.23/0.95    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f44,plain,(
% 2.23/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f5])).
% 2.23/0.95  
% 2.23/0.95  fof(f6,axiom,(
% 2.23/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f45,plain,(
% 2.23/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f6])).
% 2.23/0.95  
% 2.23/0.95  fof(f7,axiom,(
% 2.23/0.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f46,plain,(
% 2.23/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f7])).
% 2.23/0.95  
% 2.23/0.95  fof(f54,plain,(
% 2.23/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.23/0.95    inference(definition_unfolding,[],[f45,f46])).
% 2.23/0.95  
% 2.23/0.95  fof(f55,plain,(
% 2.23/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.23/0.95    inference(definition_unfolding,[],[f44,f54])).
% 2.23/0.95  
% 2.23/0.95  fof(f56,plain,(
% 2.23/0.95    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.23/0.95    inference(definition_unfolding,[],[f43,f55])).
% 2.23/0.95  
% 2.23/0.95  fof(f57,plain,(
% 2.23/0.95    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.23/0.95    inference(definition_unfolding,[],[f47,f56])).
% 2.23/0.95  
% 2.23/0.95  fof(f3,axiom,(
% 2.23/0.95    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f26,plain,(
% 2.23/0.95    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.23/0.95    inference(nnf_transformation,[],[f3])).
% 2.23/0.95  
% 2.23/0.95  fof(f41,plain,(
% 2.23/0.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f26])).
% 2.23/0.95  
% 2.23/0.95  fof(f11,conjecture,(
% 2.23/0.95    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f12,negated_conjecture,(
% 2.23/0.95    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 2.23/0.95    inference(negated_conjecture,[],[f11])).
% 2.23/0.95  
% 2.23/0.95  fof(f18,plain,(
% 2.23/0.95    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) & v1_relat_1(X1))),
% 2.23/0.95    inference(ennf_transformation,[],[f12])).
% 2.23/0.95  
% 2.23/0.95  fof(f28,plain,(
% 2.23/0.95    ? [X0,X1] : (((k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1))) & (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 2.23/0.95    inference(nnf_transformation,[],[f18])).
% 2.23/0.95  
% 2.23/0.95  fof(f29,plain,(
% 2.23/0.95    ? [X0,X1] : ((k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1))) & (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 2.23/0.95    inference(flattening,[],[f28])).
% 2.23/0.95  
% 2.23/0.95  fof(f30,plain,(
% 2.23/0.95    ? [X0,X1] : ((k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1))) & (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0 | ~r2_hidden(sK2,k2_relat_1(sK3))) & (k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0 | r2_hidden(sK2,k2_relat_1(sK3))) & v1_relat_1(sK3))),
% 2.23/0.95    introduced(choice_axiom,[])).
% 2.23/0.95  
% 2.23/0.95  fof(f31,plain,(
% 2.23/0.95    (k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0 | ~r2_hidden(sK2,k2_relat_1(sK3))) & (k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0 | r2_hidden(sK2,k2_relat_1(sK3))) & v1_relat_1(sK3)),
% 2.23/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f30])).
% 2.23/0.95  
% 2.23/0.95  fof(f53,plain,(
% 2.23/0.95    k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0 | ~r2_hidden(sK2,k2_relat_1(sK3))),
% 2.23/0.95    inference(cnf_transformation,[],[f31])).
% 2.23/0.95  
% 2.23/0.95  fof(f59,plain,(
% 2.23/0.95    k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 | ~r2_hidden(sK2,k2_relat_1(sK3))),
% 2.23/0.95    inference(definition_unfolding,[],[f53,f56])).
% 2.23/0.95  
% 2.23/0.95  fof(f10,axiom,(
% 2.23/0.95    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f17,plain,(
% 2.23/0.95    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.23/0.95    inference(ennf_transformation,[],[f10])).
% 2.23/0.95  
% 2.23/0.95  fof(f27,plain,(
% 2.23/0.95    ! [X0,X1] : (((k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 2.23/0.95    inference(nnf_transformation,[],[f17])).
% 2.23/0.95  
% 2.23/0.95  fof(f50,plain,(
% 2.23/0.95    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f27])).
% 2.23/0.95  
% 2.23/0.95  fof(f51,plain,(
% 2.23/0.95    v1_relat_1(sK3)),
% 2.23/0.95    inference(cnf_transformation,[],[f31])).
% 2.23/0.95  
% 2.23/0.95  fof(f2,axiom,(
% 2.23/0.95    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f13,plain,(
% 2.23/0.95    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.23/0.95    inference(rectify,[],[f2])).
% 2.23/0.95  
% 2.23/0.95  fof(f14,plain,(
% 2.23/0.95    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.23/0.95    inference(ennf_transformation,[],[f13])).
% 2.23/0.95  
% 2.23/0.95  fof(f24,plain,(
% 2.23/0.95    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.23/0.95    introduced(choice_axiom,[])).
% 2.23/0.95  
% 2.23/0.95  fof(f25,plain,(
% 2.23/0.95    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.23/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f24])).
% 2.23/0.95  
% 2.23/0.95  fof(f39,plain,(
% 2.23/0.95    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f25])).
% 2.23/0.95  
% 2.23/0.95  fof(f38,plain,(
% 2.23/0.95    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f25])).
% 2.23/0.95  
% 2.23/0.95  fof(f40,plain,(
% 2.23/0.95    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f25])).
% 2.23/0.95  
% 2.23/0.95  fof(f52,plain,(
% 2.23/0.95    k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0 | r2_hidden(sK2,k2_relat_1(sK3))),
% 2.23/0.95    inference(cnf_transformation,[],[f31])).
% 2.23/0.95  
% 2.23/0.95  fof(f60,plain,(
% 2.23/0.95    k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0 | r2_hidden(sK2,k2_relat_1(sK3))),
% 2.23/0.95    inference(definition_unfolding,[],[f52,f56])).
% 2.23/0.95  
% 2.23/0.95  fof(f1,axiom,(
% 2.23/0.95    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f19,plain,(
% 2.23/0.95    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.23/0.95    inference(nnf_transformation,[],[f1])).
% 2.23/0.95  
% 2.23/0.95  fof(f20,plain,(
% 2.23/0.95    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.23/0.95    inference(flattening,[],[f19])).
% 2.23/0.95  
% 2.23/0.95  fof(f21,plain,(
% 2.23/0.95    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.23/0.95    inference(rectify,[],[f20])).
% 2.23/0.95  
% 2.23/0.95  fof(f22,plain,(
% 2.23/0.95    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.23/0.95    introduced(choice_axiom,[])).
% 2.23/0.95  
% 2.23/0.95  fof(f23,plain,(
% 2.23/0.95    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.23/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.23/0.95  
% 2.23/0.95  fof(f34,plain,(
% 2.23/0.95    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.23/0.95    inference(cnf_transformation,[],[f23])).
% 2.23/0.95  
% 2.23/0.95  fof(f61,plain,(
% 2.23/0.95    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.23/0.95    inference(equality_resolution,[],[f34])).
% 2.23/0.95  
% 2.23/0.95  fof(f33,plain,(
% 2.23/0.95    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.23/0.95    inference(cnf_transformation,[],[f23])).
% 2.23/0.95  
% 2.23/0.95  fof(f62,plain,(
% 2.23/0.95    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.23/0.95    inference(equality_resolution,[],[f33])).
% 2.23/0.95  
% 2.23/0.95  fof(f9,axiom,(
% 2.23/0.95    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.23/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.23/0.95  
% 2.23/0.95  fof(f16,plain,(
% 2.23/0.95    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.23/0.95    inference(ennf_transformation,[],[f9])).
% 2.23/0.95  
% 2.23/0.95  fof(f48,plain,(
% 2.23/0.95    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f16])).
% 2.23/0.95  
% 2.23/0.95  fof(f58,plain,(
% 2.23/0.95    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 2.23/0.95    inference(definition_unfolding,[],[f48,f55])).
% 2.23/0.95  
% 2.23/0.95  fof(f49,plain,(
% 2.23/0.95    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0 | ~v1_relat_1(X1)) )),
% 2.23/0.95    inference(cnf_transformation,[],[f27])).
% 2.23/0.95  
% 2.23/0.95  cnf(c_11,plain,
% 2.23/0.95      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 2.23/0.95      inference(cnf_transformation,[],[f57]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1398,plain,
% 2.23/0.95      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
% 2.23/0.95      | r2_hidden(X0,X1) = iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_10,plain,
% 2.23/0.95      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.23/0.95      inference(cnf_transformation,[],[f41]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1399,plain,
% 2.23/0.95      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1767,plain,
% 2.23/0.95      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 2.23/0.95      | r2_hidden(X0,X1) = iProver_top ),
% 2.23/0.95      inference(superposition,[status(thm)],[c_1398,c_1399]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_15,negated_conjecture,
% 2.23/0.95      ( ~ r2_hidden(sK2,k2_relat_1(sK3))
% 2.23/0.95      | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 2.23/0.95      inference(cnf_transformation,[],[f59]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1396,plain,
% 2.23/0.95      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
% 2.23/0.95      | r2_hidden(sK2,k2_relat_1(sK3)) != iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_3417,plain,
% 2.23/0.95      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
% 2.23/0.95      | k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k2_relat_1(sK3)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 2.23/0.95      inference(superposition,[status(thm)],[c_1767,c_1396]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_13,plain,
% 2.23/0.95      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 2.23/0.95      | ~ v1_relat_1(X0)
% 2.23/0.95      | k10_relat_1(X0,X1) = k1_xboole_0 ),
% 2.23/0.95      inference(cnf_transformation,[],[f50]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_17,negated_conjecture,
% 2.23/0.95      ( v1_relat_1(sK3) ),
% 2.23/0.95      inference(cnf_transformation,[],[f51]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_261,plain,
% 2.23/0.95      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 2.23/0.95      | k10_relat_1(X0,X1) = k1_xboole_0
% 2.23/0.95      | sK3 != X0 ),
% 2.23/0.95      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_262,plain,
% 2.23/0.95      ( ~ r1_xboole_0(k2_relat_1(sK3),X0)
% 2.23/0.95      | k10_relat_1(sK3,X0) = k1_xboole_0 ),
% 2.23/0.95      inference(unflattening,[status(thm)],[c_261]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_619,plain,
% 2.23/0.95      ( ~ r1_xboole_0(k2_relat_1(sK3),X0)
% 2.23/0.95      | k10_relat_1(sK3,X0) = k1_xboole_0 ),
% 2.23/0.95      inference(prop_impl,[status(thm)],[c_262]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1526,plain,
% 2.23/0.95      ( ~ r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 2.23/0.95      | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 2.23/0.95      inference(instantiation,[status(thm)],[c_619]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_7,plain,
% 2.23/0.95      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 2.23/0.95      inference(cnf_transformation,[],[f39]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1545,plain,
% 2.23/0.95      ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 2.23/0.95      | r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 2.23/0.95      inference(instantiation,[status(thm)],[c_7]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_8,plain,
% 2.23/0.95      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.23/0.95      inference(cnf_transformation,[],[f38]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1544,plain,
% 2.23/0.95      ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 2.23/0.95      | r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k2_relat_1(sK3)) ),
% 2.23/0.95      inference(instantiation,[status(thm)],[c_8]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_2024,plain,
% 2.23/0.95      ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k2_relat_1(sK3))
% 2.23/0.95      | r2_hidden(sK2,k2_relat_1(sK3)) ),
% 2.23/0.95      inference(instantiation,[status(thm)],[c_11]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_6,plain,
% 2.23/0.95      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 2.23/0.95      inference(cnf_transformation,[],[f40]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1639,plain,
% 2.23/0.95      ( ~ r1_xboole_0(X0,k2_relat_1(sK3))
% 2.23/0.95      | ~ r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),X0)
% 2.23/0.95      | ~ r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k2_relat_1(sK3)) ),
% 2.23/0.95      inference(instantiation,[status(thm)],[c_6]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_2375,plain,
% 2.23/0.95      ( ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k2_relat_1(sK3))
% 2.23/0.95      | ~ r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 2.23/0.95      | ~ r2_hidden(sK1(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k2_relat_1(sK3)) ),
% 2.23/0.95      inference(instantiation,[status(thm)],[c_1639]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_3676,plain,
% 2.23/0.95      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 2.23/0.95      inference(global_propositional_subsumption,
% 2.23/0.95                [status(thm)],
% 2.23/0.95                [c_3417,c_15,c_1526,c_1545,c_1544,c_2024,c_2375]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_16,negated_conjecture,
% 2.23/0.95      ( r2_hidden(sK2,k2_relat_1(sK3))
% 2.23/0.95      | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0 ),
% 2.23/0.95      inference(cnf_transformation,[],[f60]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1395,plain,
% 2.23/0.95      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0
% 2.23/0.95      | r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_3679,plain,
% 2.23/0.95      ( k1_xboole_0 != k1_xboole_0
% 2.23/0.95      | r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
% 2.23/0.95      inference(demodulation,[status(thm)],[c_3676,c_1395]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_3747,plain,
% 2.23/0.95      ( r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
% 2.23/0.95      inference(equality_resolution_simp,[status(thm)],[c_3679]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_3,plain,
% 2.23/0.95      ( ~ r2_hidden(X0,X1)
% 2.23/0.95      | r2_hidden(X0,X2)
% 2.23/0.95      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.23/0.95      inference(cnf_transformation,[],[f61]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1406,plain,
% 2.23/0.95      ( r2_hidden(X0,X1) != iProver_top
% 2.23/0.95      | r2_hidden(X0,X2) = iProver_top
% 2.23/0.95      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1401,plain,
% 2.23/0.95      ( r1_xboole_0(X0,X1) = iProver_top
% 2.23/0.95      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1402,plain,
% 2.23/0.95      ( r1_xboole_0(X0,X1) = iProver_top
% 2.23/0.95      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_4,plain,
% 2.23/0.95      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.23/0.95      inference(cnf_transformation,[],[f62]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1405,plain,
% 2.23/0.95      ( r2_hidden(X0,X1) != iProver_top
% 2.23/0.95      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1749,plain,
% 2.23/0.95      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 2.23/0.95      | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 2.23/0.95      inference(superposition,[status(thm)],[c_1402,c_1405]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1908,plain,
% 2.23/0.95      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 2.23/0.95      inference(superposition,[status(thm)],[c_1401,c_1749]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_12,plain,
% 2.23/0.95      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 2.23/0.95      | ~ r2_hidden(X0,X2) ),
% 2.23/0.95      inference(cnf_transformation,[],[f58]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1397,plain,
% 2.23/0.95      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) != iProver_top
% 2.23/0.95      | r2_hidden(X0,X2) != iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1923,plain,
% 2.23/0.95      ( r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X2))) != iProver_top ),
% 2.23/0.95      inference(superposition,[status(thm)],[c_1908,c_1397]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_2091,plain,
% 2.23/0.95      ( r2_hidden(X0,X1) != iProver_top
% 2.23/0.95      | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X2)) = iProver_top ),
% 2.23/0.95      inference(superposition,[status(thm)],[c_1406,c_1923]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_3750,plain,
% 2.23/0.95      ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,X0)) = iProver_top ),
% 2.23/0.95      inference(superposition,[status(thm)],[c_3747,c_2091]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_3752,plain,
% 2.23/0.95      ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.23/0.95      inference(instantiation,[status(thm)],[c_3750]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1865,plain,
% 2.23/0.95      ( ~ r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 2.23/0.95      | ~ r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 2.23/0.95      | ~ r2_hidden(X0,k2_relat_1(sK3)) ),
% 2.23/0.95      inference(instantiation,[status(thm)],[c_6]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1866,plain,
% 2.23/0.95      ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 2.23/0.95      | r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 2.23/0.95      | r2_hidden(X0,k2_relat_1(sK3)) != iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_1865]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1868,plain,
% 2.23/0.95      ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 2.23/0.95      | r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 2.23/0.95      | r2_hidden(sK2,k2_relat_1(sK3)) != iProver_top ),
% 2.23/0.95      inference(instantiation,[status(thm)],[c_1866]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_14,plain,
% 2.23/0.95      ( r1_xboole_0(k2_relat_1(X0),X1)
% 2.23/0.95      | ~ v1_relat_1(X0)
% 2.23/0.95      | k10_relat_1(X0,X1) != k1_xboole_0 ),
% 2.23/0.95      inference(cnf_transformation,[],[f49]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_249,plain,
% 2.23/0.95      ( r1_xboole_0(k2_relat_1(X0),X1)
% 2.23/0.95      | k10_relat_1(X0,X1) != k1_xboole_0
% 2.23/0.95      | sK3 != X0 ),
% 2.23/0.95      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_250,plain,
% 2.23/0.95      ( r1_xboole_0(k2_relat_1(sK3),X0)
% 2.23/0.95      | k10_relat_1(sK3,X0) != k1_xboole_0 ),
% 2.23/0.95      inference(unflattening,[status(thm)],[c_249]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_617,plain,
% 2.23/0.95      ( r1_xboole_0(k2_relat_1(sK3),X0)
% 2.23/0.95      | k10_relat_1(sK3,X0) != k1_xboole_0 ),
% 2.23/0.95      inference(prop_impl,[status(thm)],[c_250]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1557,plain,
% 2.23/0.95      ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 2.23/0.95      | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0 ),
% 2.23/0.95      inference(instantiation,[status(thm)],[c_617]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_1558,plain,
% 2.23/0.95      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0
% 2.23/0.95      | r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_1557]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(c_19,plain,
% 2.23/0.95      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0
% 2.23/0.95      | r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
% 2.23/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.23/0.95  
% 2.23/0.95  cnf(contradiction,plain,
% 2.23/0.95      ( $false ),
% 2.23/0.95      inference(minisat,[status(thm)],[c_3752,c_3676,c_1868,c_1558,c_19]) ).
% 2.23/0.95  
% 2.23/0.95  
% 2.23/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.23/0.95  
% 2.23/0.95  ------                               Statistics
% 2.23/0.95  
% 2.23/0.95  ------ General
% 2.23/0.95  
% 2.23/0.95  abstr_ref_over_cycles:                  0
% 2.23/0.95  abstr_ref_under_cycles:                 0
% 2.23/0.95  gc_basic_clause_elim:                   0
% 2.23/0.95  forced_gc_time:                         0
% 2.23/0.95  parsing_time:                           0.008
% 2.23/0.95  unif_index_cands_time:                  0.
% 2.23/0.95  unif_index_add_time:                    0.
% 2.23/0.95  orderings_time:                         0.
% 2.23/0.95  out_proof_time:                         0.007
% 2.23/0.95  total_time:                             0.152
% 2.23/0.95  num_of_symbols:                         43
% 2.23/0.95  num_of_terms:                           3387
% 2.23/0.95  
% 2.23/0.95  ------ Preprocessing
% 2.23/0.95  
% 2.23/0.95  num_of_splits:                          0
% 2.23/0.95  num_of_split_atoms:                     0
% 2.23/0.95  num_of_reused_defs:                     0
% 2.23/0.95  num_eq_ax_congr_red:                    24
% 2.23/0.95  num_of_sem_filtered_clauses:            1
% 2.23/0.95  num_of_subtypes:                        0
% 2.23/0.95  monotx_restored_types:                  0
% 2.23/0.95  sat_num_of_epr_types:                   0
% 2.23/0.95  sat_num_of_non_cyclic_types:            0
% 2.23/0.95  sat_guarded_non_collapsed_types:        0
% 2.23/0.95  num_pure_diseq_elim:                    0
% 2.23/0.95  simp_replaced_by:                       0
% 2.23/0.95  res_preprocessed:                       84
% 2.23/0.95  prep_upred:                             0
% 2.23/0.95  prep_unflattend:                        48
% 2.23/0.95  smt_new_axioms:                         0
% 2.23/0.95  pred_elim_cands:                        2
% 2.23/0.95  pred_elim:                              1
% 2.23/0.95  pred_elim_cl:                           1
% 2.23/0.95  pred_elim_cycles:                       3
% 2.23/0.95  merged_defs:                            22
% 2.23/0.95  merged_defs_ncl:                        0
% 2.23/0.95  bin_hyper_res:                          22
% 2.23/0.95  prep_cycles:                            4
% 2.23/0.95  pred_elim_time:                         0.007
% 2.23/0.95  splitting_time:                         0.
% 2.23/0.95  sem_filter_time:                        0.
% 2.23/0.95  monotx_time:                            0.001
% 2.23/0.95  subtype_inf_time:                       0.
% 2.23/0.95  
% 2.23/0.95  ------ Problem properties
% 2.23/0.95  
% 2.23/0.95  clauses:                                17
% 2.23/0.95  conjectures:                            2
% 2.23/0.95  epr:                                    1
% 2.23/0.95  horn:                                   10
% 2.23/0.95  ground:                                 2
% 2.23/0.95  unary:                                  0
% 2.23/0.95  binary:                                 12
% 2.23/0.95  lits:                                   40
% 2.23/0.95  lits_eq:                                9
% 2.23/0.95  fd_pure:                                0
% 2.23/0.95  fd_pseudo:                              0
% 2.23/0.95  fd_cond:                                0
% 2.23/0.95  fd_pseudo_cond:                         3
% 2.23/0.95  ac_symbols:                             0
% 2.23/0.95  
% 2.23/0.95  ------ Propositional Solver
% 2.23/0.95  
% 2.23/0.95  prop_solver_calls:                      30
% 2.23/0.95  prop_fast_solver_calls:                 591
% 2.23/0.95  smt_solver_calls:                       0
% 2.23/0.95  smt_fast_solver_calls:                  0
% 2.23/0.95  prop_num_of_clauses:                    1104
% 2.23/0.95  prop_preprocess_simplified:             3848
% 2.23/0.95  prop_fo_subsumed:                       1
% 2.23/0.95  prop_solver_time:                       0.
% 2.23/0.95  smt_solver_time:                        0.
% 2.23/0.95  smt_fast_solver_time:                   0.
% 2.23/0.95  prop_fast_solver_time:                  0.
% 2.23/0.95  prop_unsat_core_time:                   0.
% 2.23/0.95  
% 2.23/0.95  ------ QBF
% 2.23/0.95  
% 2.23/0.95  qbf_q_res:                              0
% 2.23/0.95  qbf_num_tautologies:                    0
% 2.23/0.95  qbf_prep_cycles:                        0
% 2.23/0.95  
% 2.23/0.95  ------ BMC1
% 2.23/0.95  
% 2.23/0.95  bmc1_current_bound:                     -1
% 2.23/0.95  bmc1_last_solved_bound:                 -1
% 2.23/0.95  bmc1_unsat_core_size:                   -1
% 2.23/0.95  bmc1_unsat_core_parents_size:           -1
% 2.23/0.95  bmc1_merge_next_fun:                    0
% 2.23/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.23/0.95  
% 2.23/0.95  ------ Instantiation
% 2.23/0.95  
% 2.23/0.95  inst_num_of_clauses:                    260
% 2.23/0.95  inst_num_in_passive:                    134
% 2.23/0.95  inst_num_in_active:                     94
% 2.23/0.95  inst_num_in_unprocessed:                32
% 2.23/0.95  inst_num_of_loops:                      210
% 2.23/0.95  inst_num_of_learning_restarts:          0
% 2.23/0.95  inst_num_moves_active_passive:          111
% 2.23/0.95  inst_lit_activity:                      0
% 2.23/0.95  inst_lit_activity_moves:                0
% 2.23/0.95  inst_num_tautologies:                   0
% 2.23/0.95  inst_num_prop_implied:                  0
% 2.23/0.95  inst_num_existing_simplified:           0
% 2.23/0.95  inst_num_eq_res_simplified:             0
% 2.23/0.95  inst_num_child_elim:                    0
% 2.23/0.95  inst_num_of_dismatching_blockings:      99
% 2.23/0.95  inst_num_of_non_proper_insts:           279
% 2.23/0.95  inst_num_of_duplicates:                 0
% 2.23/0.95  inst_inst_num_from_inst_to_res:         0
% 2.23/0.95  inst_dismatching_checking_time:         0.
% 2.23/0.95  
% 2.23/0.95  ------ Resolution
% 2.23/0.95  
% 2.23/0.95  res_num_of_clauses:                     0
% 2.23/0.95  res_num_in_passive:                     0
% 2.23/0.95  res_num_in_active:                      0
% 2.23/0.95  res_num_of_loops:                       88
% 2.23/0.95  res_forward_subset_subsumed:            7
% 2.23/0.95  res_backward_subset_subsumed:           0
% 2.23/0.95  res_forward_subsumed:                   0
% 2.23/0.95  res_backward_subsumed:                  0
% 2.23/0.95  res_forward_subsumption_resolution:     0
% 2.23/0.95  res_backward_subsumption_resolution:    0
% 2.23/0.95  res_clause_to_clause_subsumption:       690
% 2.23/0.95  res_orphan_elimination:                 0
% 2.23/0.95  res_tautology_del:                      87
% 2.23/0.95  res_num_eq_res_simplified:              0
% 2.23/0.95  res_num_sel_changes:                    0
% 2.23/0.95  res_moves_from_active_to_pass:          0
% 2.23/0.95  
% 2.23/0.95  ------ Superposition
% 2.23/0.95  
% 2.23/0.95  sup_time_total:                         0.
% 2.23/0.95  sup_time_generating:                    0.
% 2.23/0.95  sup_time_sim_full:                      0.
% 2.23/0.95  sup_time_sim_immed:                     0.
% 2.23/0.95  
% 2.23/0.95  sup_num_of_clauses:                     102
% 2.23/0.95  sup_num_in_active:                      39
% 2.23/0.95  sup_num_in_passive:                     63
% 2.23/0.95  sup_num_of_loops:                       40
% 2.23/0.95  sup_fw_superposition:                   59
% 2.23/0.95  sup_bw_superposition:                   91
% 2.23/0.95  sup_immediate_simplified:               35
% 2.23/0.95  sup_given_eliminated:                   0
% 2.23/0.95  comparisons_done:                       0
% 2.23/0.95  comparisons_avoided:                    0
% 2.23/0.95  
% 2.23/0.95  ------ Simplifications
% 2.23/0.95  
% 2.23/0.95  
% 2.23/0.95  sim_fw_subset_subsumed:                 0
% 2.23/0.95  sim_bw_subset_subsumed:                 1
% 2.23/0.95  sim_fw_subsumed:                        17
% 2.23/0.95  sim_bw_subsumed:                        2
% 2.23/0.95  sim_fw_subsumption_res:                 2
% 2.23/0.95  sim_bw_subsumption_res:                 0
% 2.23/0.95  sim_tautology_del:                      10
% 2.23/0.95  sim_eq_tautology_del:                   0
% 2.23/0.95  sim_eq_res_simp:                        2
% 2.23/0.95  sim_fw_demodulated:                     9
% 2.23/0.95  sim_bw_demodulated:                     1
% 2.23/0.95  sim_light_normalised:                   9
% 2.23/0.95  sim_joinable_taut:                      0
% 2.23/0.95  sim_joinable_simp:                      0
% 2.23/0.95  sim_ac_normalised:                      0
% 2.23/0.95  sim_smt_subsumption:                    0
% 2.23/0.95  
%------------------------------------------------------------------------------
