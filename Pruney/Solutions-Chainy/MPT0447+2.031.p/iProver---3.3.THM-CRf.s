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
% DateTime   : Thu Dec  3 11:43:14 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 255 expanded)
%              Number of clauses        :   61 (  75 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  358 ( 812 expanded)
%              Number of equality atoms :  125 ( 191 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f27,f26,f25])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f63,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK8))
        & r1_tarski(X0,sK8)
        & v1_relat_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(X1))
          & r1_tarski(sK7,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    & r1_tarski(sK7,sK8)
    & v1_relat_1(sK8)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f18,f36,f35])).

fof(f56,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f44,f44])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f58,plain,(
    ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_611,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_604,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_610,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1885,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_610])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_605,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4973,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(X2)) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_605])).

cnf(c_5283,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1),k1_relat_1(X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_4973])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_612,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8436,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5283,c_612])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_208,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_209,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8))) = k3_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_5,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_609,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1094,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_609])).

cnf(c_1119,plain,
    ( r1_tarski(X0,k3_relat_1(sK8)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_209,c_1094])).

cnf(c_8593,plain,
    ( r1_tarski(X0,sK8) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8436,c_1119])).

cnf(c_8644,plain,
    ( r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
    | r1_tarski(sK7,sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8593])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_600,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1754,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_600,c_610])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_601,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4075,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k2_relat_1(X2)) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_601])).

cnf(c_5015,plain,
    ( r2_hidden(sK0(k2_relat_1(X0),X1),k2_relat_1(X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_4075])).

cnf(c_8267,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5015,c_612])).

cnf(c_1093,plain,
    ( r1_tarski(X0,k3_relat_1(sK8)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_209,c_609])).

cnf(c_8405,plain,
    ( r1_tarski(X0,sK8) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8267,c_1093])).

cnf(c_8428,plain,
    ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
    | r1_tarski(sK7,sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8405])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2533,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK8))
    | ~ r1_tarski(X1,k3_relat_1(sK8))
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),k3_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6560,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8))
    | ~ r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8))
    | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_2533])).

cnf(c_6561,plain,
    ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6560])).

cnf(c_331,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_729,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    | k3_relat_1(sK8) != X1
    | k3_relat_1(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_750,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK8))
    | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    | k3_relat_1(sK8) != k3_relat_1(sK8)
    | k3_relat_1(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_2123,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8))
    | k3_relat_1(sK8) != k3_relat_1(sK8)
    | k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_2124,plain,
    ( k3_relat_1(sK8) != k3_relat_1(sK8)
    | k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
    | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2123])).

cnf(c_330,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_795,plain,
    ( X0 != X1
    | k3_relat_1(sK7) != X1
    | k3_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_1049,plain,
    ( X0 != k3_relat_1(sK7)
    | k3_relat_1(sK7) = X0
    | k3_relat_1(sK7) != k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_1548,plain,
    ( k3_relat_1(sK7) != k3_relat_1(sK7)
    | k3_relat_1(sK7) = k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
    | k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) != k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_329,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_751,plain,
    ( k3_relat_1(sK8) = k3_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_347,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_338,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_345,plain,
    ( k3_relat_1(sK7) = k3_relat_1(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_24,plain,
    ( ~ v1_relat_1(sK7)
    | k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,plain,
    ( r1_tarski(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8644,c_8428,c_6561,c_2124,c_1548,c_751,c_347,c_345,c_24,c_22,c_21,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:59:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.77/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/0.98  
% 2.77/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/0.98  
% 2.77/0.98  ------  iProver source info
% 2.77/0.98  
% 2.77/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.77/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/0.98  git: non_committed_changes: false
% 2.77/0.98  git: last_make_outside_of_git: false
% 2.77/0.98  
% 2.77/0.98  ------ 
% 2.77/0.98  
% 2.77/0.98  ------ Input Options
% 2.77/0.98  
% 2.77/0.98  --out_options                           all
% 2.77/0.98  --tptp_safe_out                         true
% 2.77/0.98  --problem_path                          ""
% 2.77/0.98  --include_path                          ""
% 2.77/0.98  --clausifier                            res/vclausify_rel
% 2.77/0.98  --clausifier_options                    --mode clausify
% 2.77/0.98  --stdin                                 false
% 2.77/0.98  --stats_out                             all
% 2.77/0.98  
% 2.77/0.98  ------ General Options
% 2.77/0.98  
% 2.77/0.98  --fof                                   false
% 2.77/0.98  --time_out_real                         305.
% 2.77/0.98  --time_out_virtual                      -1.
% 2.77/0.98  --symbol_type_check                     false
% 2.77/0.98  --clausify_out                          false
% 2.77/0.98  --sig_cnt_out                           false
% 2.77/0.98  --trig_cnt_out                          false
% 2.77/0.98  --trig_cnt_out_tolerance                1.
% 2.77/0.98  --trig_cnt_out_sk_spl                   false
% 2.77/0.98  --abstr_cl_out                          false
% 2.77/0.98  
% 2.77/0.98  ------ Global Options
% 2.77/0.98  
% 2.77/0.98  --schedule                              default
% 2.77/0.98  --add_important_lit                     false
% 2.77/0.98  --prop_solver_per_cl                    1000
% 2.77/0.98  --min_unsat_core                        false
% 2.77/0.98  --soft_assumptions                      false
% 2.77/0.98  --soft_lemma_size                       3
% 2.77/0.98  --prop_impl_unit_size                   0
% 2.77/0.98  --prop_impl_unit                        []
% 2.77/0.98  --share_sel_clauses                     true
% 2.77/0.98  --reset_solvers                         false
% 2.77/0.98  --bc_imp_inh                            [conj_cone]
% 2.77/0.98  --conj_cone_tolerance                   3.
% 2.77/0.98  --extra_neg_conj                        none
% 2.77/0.98  --large_theory_mode                     true
% 2.77/0.98  --prolific_symb_bound                   200
% 2.77/0.98  --lt_threshold                          2000
% 2.77/0.98  --clause_weak_htbl                      true
% 2.77/0.98  --gc_record_bc_elim                     false
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing Options
% 2.77/0.98  
% 2.77/0.98  --preprocessing_flag                    true
% 2.77/0.98  --time_out_prep_mult                    0.1
% 2.77/0.98  --splitting_mode                        input
% 2.77/0.98  --splitting_grd                         true
% 2.77/0.98  --splitting_cvd                         false
% 2.77/0.98  --splitting_cvd_svl                     false
% 2.77/0.98  --splitting_nvd                         32
% 2.77/0.98  --sub_typing                            true
% 2.77/0.98  --prep_gs_sim                           true
% 2.77/0.98  --prep_unflatten                        true
% 2.77/0.98  --prep_res_sim                          true
% 2.77/0.98  --prep_upred                            true
% 2.77/0.98  --prep_sem_filter                       exhaustive
% 2.77/0.98  --prep_sem_filter_out                   false
% 2.77/0.98  --pred_elim                             true
% 2.77/0.98  --res_sim_input                         true
% 2.77/0.98  --eq_ax_congr_red                       true
% 2.77/0.98  --pure_diseq_elim                       true
% 2.77/0.98  --brand_transform                       false
% 2.77/0.98  --non_eq_to_eq                          false
% 2.77/0.98  --prep_def_merge                        true
% 2.77/0.98  --prep_def_merge_prop_impl              false
% 2.77/0.98  --prep_def_merge_mbd                    true
% 2.77/0.98  --prep_def_merge_tr_red                 false
% 2.77/0.98  --prep_def_merge_tr_cl                  false
% 2.77/0.98  --smt_preprocessing                     true
% 2.77/0.98  --smt_ac_axioms                         fast
% 2.77/0.98  --preprocessed_out                      false
% 2.77/0.98  --preprocessed_stats                    false
% 2.77/0.98  
% 2.77/0.98  ------ Abstraction refinement Options
% 2.77/0.98  
% 2.77/0.98  --abstr_ref                             []
% 2.77/0.98  --abstr_ref_prep                        false
% 2.77/0.98  --abstr_ref_until_sat                   false
% 2.77/0.98  --abstr_ref_sig_restrict                funpre
% 2.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.98  --abstr_ref_under                       []
% 2.77/0.98  
% 2.77/0.98  ------ SAT Options
% 2.77/0.98  
% 2.77/0.98  --sat_mode                              false
% 2.77/0.98  --sat_fm_restart_options                ""
% 2.77/0.98  --sat_gr_def                            false
% 2.77/0.98  --sat_epr_types                         true
% 2.77/0.98  --sat_non_cyclic_types                  false
% 2.77/0.98  --sat_finite_models                     false
% 2.77/0.98  --sat_fm_lemmas                         false
% 2.77/0.98  --sat_fm_prep                           false
% 2.77/0.98  --sat_fm_uc_incr                        true
% 2.77/0.98  --sat_out_model                         small
% 2.77/0.98  --sat_out_clauses                       false
% 2.77/0.98  
% 2.77/0.98  ------ QBF Options
% 2.77/0.98  
% 2.77/0.98  --qbf_mode                              false
% 2.77/0.98  --qbf_elim_univ                         false
% 2.77/0.98  --qbf_dom_inst                          none
% 2.77/0.98  --qbf_dom_pre_inst                      false
% 2.77/0.98  --qbf_sk_in                             false
% 2.77/0.98  --qbf_pred_elim                         true
% 2.77/0.98  --qbf_split                             512
% 2.77/0.98  
% 2.77/0.98  ------ BMC1 Options
% 2.77/0.98  
% 2.77/0.98  --bmc1_incremental                      false
% 2.77/0.98  --bmc1_axioms                           reachable_all
% 2.77/0.98  --bmc1_min_bound                        0
% 2.77/0.98  --bmc1_max_bound                        -1
% 2.77/0.98  --bmc1_max_bound_default                -1
% 2.77/0.98  --bmc1_symbol_reachability              true
% 2.77/0.98  --bmc1_property_lemmas                  false
% 2.77/0.98  --bmc1_k_induction                      false
% 2.77/0.98  --bmc1_non_equiv_states                 false
% 2.77/0.98  --bmc1_deadlock                         false
% 2.77/0.98  --bmc1_ucm                              false
% 2.77/0.98  --bmc1_add_unsat_core                   none
% 2.77/0.98  --bmc1_unsat_core_children              false
% 2.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/0.98  --bmc1_out_stat                         full
% 2.77/0.98  --bmc1_ground_init                      false
% 2.77/0.98  --bmc1_pre_inst_next_state              false
% 2.77/0.98  --bmc1_pre_inst_state                   false
% 2.77/0.98  --bmc1_pre_inst_reach_state             false
% 2.77/0.98  --bmc1_out_unsat_core                   false
% 2.77/0.98  --bmc1_aig_witness_out                  false
% 2.77/0.98  --bmc1_verbose                          false
% 2.77/0.98  --bmc1_dump_clauses_tptp                false
% 2.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.77/0.98  --bmc1_dump_file                        -
% 2.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.77/0.98  --bmc1_ucm_extend_mode                  1
% 2.77/0.98  --bmc1_ucm_init_mode                    2
% 2.77/0.98  --bmc1_ucm_cone_mode                    none
% 2.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.77/0.98  --bmc1_ucm_relax_model                  4
% 2.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/0.98  --bmc1_ucm_layered_model                none
% 2.77/0.98  --bmc1_ucm_max_lemma_size               10
% 2.77/0.98  
% 2.77/0.98  ------ AIG Options
% 2.77/0.98  
% 2.77/0.98  --aig_mode                              false
% 2.77/0.98  
% 2.77/0.98  ------ Instantiation Options
% 2.77/0.98  
% 2.77/0.98  --instantiation_flag                    true
% 2.77/0.98  --inst_sos_flag                         false
% 2.77/0.98  --inst_sos_phase                        true
% 2.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel_side                     num_symb
% 2.77/0.98  --inst_solver_per_active                1400
% 2.77/0.98  --inst_solver_calls_frac                1.
% 2.77/0.98  --inst_passive_queue_type               priority_queues
% 2.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/0.98  --inst_passive_queues_freq              [25;2]
% 2.77/0.98  --inst_dismatching                      true
% 2.77/0.98  --inst_eager_unprocessed_to_passive     true
% 2.77/0.98  --inst_prop_sim_given                   true
% 2.77/0.98  --inst_prop_sim_new                     false
% 2.77/0.98  --inst_subs_new                         false
% 2.77/0.98  --inst_eq_res_simp                      false
% 2.77/0.98  --inst_subs_given                       false
% 2.77/0.98  --inst_orphan_elimination               true
% 2.77/0.98  --inst_learning_loop_flag               true
% 2.77/0.98  --inst_learning_start                   3000
% 2.77/0.98  --inst_learning_factor                  2
% 2.77/0.98  --inst_start_prop_sim_after_learn       3
% 2.77/0.98  --inst_sel_renew                        solver
% 2.77/0.98  --inst_lit_activity_flag                true
% 2.77/0.98  --inst_restr_to_given                   false
% 2.77/0.98  --inst_activity_threshold               500
% 2.77/0.98  --inst_out_proof                        true
% 2.77/0.98  
% 2.77/0.98  ------ Resolution Options
% 2.77/0.98  
% 2.77/0.98  --resolution_flag                       true
% 2.77/0.98  --res_lit_sel                           adaptive
% 2.77/0.98  --res_lit_sel_side                      none
% 2.77/0.98  --res_ordering                          kbo
% 2.77/0.98  --res_to_prop_solver                    active
% 2.77/0.98  --res_prop_simpl_new                    false
% 2.77/0.98  --res_prop_simpl_given                  true
% 2.77/0.98  --res_passive_queue_type                priority_queues
% 2.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/0.98  --res_passive_queues_freq               [15;5]
% 2.77/0.98  --res_forward_subs                      full
% 2.77/0.98  --res_backward_subs                     full
% 2.77/0.98  --res_forward_subs_resolution           true
% 2.77/0.98  --res_backward_subs_resolution          true
% 2.77/0.98  --res_orphan_elimination                true
% 2.77/0.98  --res_time_limit                        2.
% 2.77/0.98  --res_out_proof                         true
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Options
% 2.77/0.98  
% 2.77/0.98  --superposition_flag                    true
% 2.77/0.98  --sup_passive_queue_type                priority_queues
% 2.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.77/0.98  --demod_completeness_check              fast
% 2.77/0.98  --demod_use_ground                      true
% 2.77/0.98  --sup_to_prop_solver                    passive
% 2.77/0.98  --sup_prop_simpl_new                    true
% 2.77/0.98  --sup_prop_simpl_given                  true
% 2.77/0.98  --sup_fun_splitting                     false
% 2.77/0.98  --sup_smt_interval                      50000
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Simplification Setup
% 2.77/0.98  
% 2.77/0.98  --sup_indices_passive                   []
% 2.77/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_full_bw                           [BwDemod]
% 2.77/0.98  --sup_immed_triv                        [TrivRules]
% 2.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_immed_bw_main                     []
% 2.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.98  
% 2.77/0.98  ------ Combination Options
% 2.77/0.98  
% 2.77/0.98  --comb_res_mult                         3
% 2.77/0.98  --comb_sup_mult                         2
% 2.77/0.98  --comb_inst_mult                        10
% 2.77/0.98  
% 2.77/0.98  ------ Debug Options
% 2.77/0.98  
% 2.77/0.98  --dbg_backtrace                         false
% 2.77/0.98  --dbg_dump_prop_clauses                 false
% 2.77/0.98  --dbg_dump_prop_clauses_file            -
% 2.77/0.98  --dbg_out_stat                          false
% 2.77/0.98  ------ Parsing...
% 2.77/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/0.98  ------ Proving...
% 2.77/0.98  ------ Problem Properties 
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  clauses                                 18
% 2.77/0.98  conjectures                             2
% 2.77/0.98  EPR                                     2
% 2.77/0.98  Horn                                    15
% 2.77/0.98  unary                                   5
% 2.77/0.98  binary                                  7
% 2.77/0.98  lits                                    37
% 2.77/0.98  lits eq                                 7
% 2.77/0.98  fd_pure                                 0
% 2.77/0.98  fd_pseudo                               0
% 2.77/0.98  fd_cond                                 0
% 2.77/0.98  fd_pseudo_cond                          4
% 2.77/0.98  AC symbols                              0
% 2.77/0.98  
% 2.77/0.98  ------ Schedule dynamic 5 is on 
% 2.77/0.98  
% 2.77/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  ------ 
% 2.77/0.98  Current options:
% 2.77/0.98  ------ 
% 2.77/0.98  
% 2.77/0.98  ------ Input Options
% 2.77/0.98  
% 2.77/0.98  --out_options                           all
% 2.77/0.98  --tptp_safe_out                         true
% 2.77/0.98  --problem_path                          ""
% 2.77/0.98  --include_path                          ""
% 2.77/0.98  --clausifier                            res/vclausify_rel
% 2.77/0.98  --clausifier_options                    --mode clausify
% 2.77/0.98  --stdin                                 false
% 2.77/0.98  --stats_out                             all
% 2.77/0.98  
% 2.77/0.98  ------ General Options
% 2.77/0.98  
% 2.77/0.98  --fof                                   false
% 2.77/0.98  --time_out_real                         305.
% 2.77/0.98  --time_out_virtual                      -1.
% 2.77/0.98  --symbol_type_check                     false
% 2.77/0.98  --clausify_out                          false
% 2.77/0.98  --sig_cnt_out                           false
% 2.77/0.98  --trig_cnt_out                          false
% 2.77/0.98  --trig_cnt_out_tolerance                1.
% 2.77/0.98  --trig_cnt_out_sk_spl                   false
% 2.77/0.98  --abstr_cl_out                          false
% 2.77/0.98  
% 2.77/0.98  ------ Global Options
% 2.77/0.98  
% 2.77/0.98  --schedule                              default
% 2.77/0.98  --add_important_lit                     false
% 2.77/0.98  --prop_solver_per_cl                    1000
% 2.77/0.98  --min_unsat_core                        false
% 2.77/0.98  --soft_assumptions                      false
% 2.77/0.98  --soft_lemma_size                       3
% 2.77/0.98  --prop_impl_unit_size                   0
% 2.77/0.98  --prop_impl_unit                        []
% 2.77/0.98  --share_sel_clauses                     true
% 2.77/0.98  --reset_solvers                         false
% 2.77/0.98  --bc_imp_inh                            [conj_cone]
% 2.77/0.98  --conj_cone_tolerance                   3.
% 2.77/0.98  --extra_neg_conj                        none
% 2.77/0.98  --large_theory_mode                     true
% 2.77/0.98  --prolific_symb_bound                   200
% 2.77/0.98  --lt_threshold                          2000
% 2.77/0.98  --clause_weak_htbl                      true
% 2.77/0.98  --gc_record_bc_elim                     false
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing Options
% 2.77/0.98  
% 2.77/0.98  --preprocessing_flag                    true
% 2.77/0.98  --time_out_prep_mult                    0.1
% 2.77/0.98  --splitting_mode                        input
% 2.77/0.98  --splitting_grd                         true
% 2.77/0.98  --splitting_cvd                         false
% 2.77/0.98  --splitting_cvd_svl                     false
% 2.77/0.98  --splitting_nvd                         32
% 2.77/0.98  --sub_typing                            true
% 2.77/0.98  --prep_gs_sim                           true
% 2.77/0.98  --prep_unflatten                        true
% 2.77/0.98  --prep_res_sim                          true
% 2.77/0.98  --prep_upred                            true
% 2.77/0.98  --prep_sem_filter                       exhaustive
% 2.77/0.98  --prep_sem_filter_out                   false
% 2.77/0.98  --pred_elim                             true
% 2.77/0.98  --res_sim_input                         true
% 2.77/0.98  --eq_ax_congr_red                       true
% 2.77/0.98  --pure_diseq_elim                       true
% 2.77/0.98  --brand_transform                       false
% 2.77/0.98  --non_eq_to_eq                          false
% 2.77/0.98  --prep_def_merge                        true
% 2.77/0.98  --prep_def_merge_prop_impl              false
% 2.77/0.98  --prep_def_merge_mbd                    true
% 2.77/0.98  --prep_def_merge_tr_red                 false
% 2.77/0.98  --prep_def_merge_tr_cl                  false
% 2.77/0.98  --smt_preprocessing                     true
% 2.77/0.98  --smt_ac_axioms                         fast
% 2.77/0.98  --preprocessed_out                      false
% 2.77/0.98  --preprocessed_stats                    false
% 2.77/0.98  
% 2.77/0.98  ------ Abstraction refinement Options
% 2.77/0.98  
% 2.77/0.98  --abstr_ref                             []
% 2.77/0.98  --abstr_ref_prep                        false
% 2.77/0.98  --abstr_ref_until_sat                   false
% 2.77/0.98  --abstr_ref_sig_restrict                funpre
% 2.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.98  --abstr_ref_under                       []
% 2.77/0.98  
% 2.77/0.98  ------ SAT Options
% 2.77/0.98  
% 2.77/0.98  --sat_mode                              false
% 2.77/0.98  --sat_fm_restart_options                ""
% 2.77/0.98  --sat_gr_def                            false
% 2.77/0.98  --sat_epr_types                         true
% 2.77/0.98  --sat_non_cyclic_types                  false
% 2.77/0.98  --sat_finite_models                     false
% 2.77/0.98  --sat_fm_lemmas                         false
% 2.77/0.98  --sat_fm_prep                           false
% 2.77/0.98  --sat_fm_uc_incr                        true
% 2.77/0.98  --sat_out_model                         small
% 2.77/0.98  --sat_out_clauses                       false
% 2.77/0.98  
% 2.77/0.98  ------ QBF Options
% 2.77/0.98  
% 2.77/0.98  --qbf_mode                              false
% 2.77/0.98  --qbf_elim_univ                         false
% 2.77/0.98  --qbf_dom_inst                          none
% 2.77/0.98  --qbf_dom_pre_inst                      false
% 2.77/0.98  --qbf_sk_in                             false
% 2.77/0.98  --qbf_pred_elim                         true
% 2.77/0.98  --qbf_split                             512
% 2.77/0.98  
% 2.77/0.98  ------ BMC1 Options
% 2.77/0.98  
% 2.77/0.98  --bmc1_incremental                      false
% 2.77/0.98  --bmc1_axioms                           reachable_all
% 2.77/0.98  --bmc1_min_bound                        0
% 2.77/0.98  --bmc1_max_bound                        -1
% 2.77/0.98  --bmc1_max_bound_default                -1
% 2.77/0.98  --bmc1_symbol_reachability              true
% 2.77/0.98  --bmc1_property_lemmas                  false
% 2.77/0.98  --bmc1_k_induction                      false
% 2.77/0.98  --bmc1_non_equiv_states                 false
% 2.77/0.98  --bmc1_deadlock                         false
% 2.77/0.98  --bmc1_ucm                              false
% 2.77/0.98  --bmc1_add_unsat_core                   none
% 2.77/0.98  --bmc1_unsat_core_children              false
% 2.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/0.98  --bmc1_out_stat                         full
% 2.77/0.98  --bmc1_ground_init                      false
% 2.77/0.98  --bmc1_pre_inst_next_state              false
% 2.77/0.98  --bmc1_pre_inst_state                   false
% 2.77/0.98  --bmc1_pre_inst_reach_state             false
% 2.77/0.98  --bmc1_out_unsat_core                   false
% 2.77/0.98  --bmc1_aig_witness_out                  false
% 2.77/0.98  --bmc1_verbose                          false
% 2.77/0.98  --bmc1_dump_clauses_tptp                false
% 2.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.77/0.98  --bmc1_dump_file                        -
% 2.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.77/0.98  --bmc1_ucm_extend_mode                  1
% 2.77/0.98  --bmc1_ucm_init_mode                    2
% 2.77/0.98  --bmc1_ucm_cone_mode                    none
% 2.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.77/0.98  --bmc1_ucm_relax_model                  4
% 2.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/0.98  --bmc1_ucm_layered_model                none
% 2.77/0.98  --bmc1_ucm_max_lemma_size               10
% 2.77/0.98  
% 2.77/0.98  ------ AIG Options
% 2.77/0.98  
% 2.77/0.98  --aig_mode                              false
% 2.77/0.98  
% 2.77/0.98  ------ Instantiation Options
% 2.77/0.98  
% 2.77/0.98  --instantiation_flag                    true
% 2.77/0.98  --inst_sos_flag                         false
% 2.77/0.98  --inst_sos_phase                        true
% 2.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel_side                     none
% 2.77/0.98  --inst_solver_per_active                1400
% 2.77/0.98  --inst_solver_calls_frac                1.
% 2.77/0.98  --inst_passive_queue_type               priority_queues
% 2.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/0.98  --inst_passive_queues_freq              [25;2]
% 2.77/0.98  --inst_dismatching                      true
% 2.77/0.98  --inst_eager_unprocessed_to_passive     true
% 2.77/0.98  --inst_prop_sim_given                   true
% 2.77/0.98  --inst_prop_sim_new                     false
% 2.77/0.98  --inst_subs_new                         false
% 2.77/0.98  --inst_eq_res_simp                      false
% 2.77/0.98  --inst_subs_given                       false
% 2.77/0.98  --inst_orphan_elimination               true
% 2.77/0.98  --inst_learning_loop_flag               true
% 2.77/0.98  --inst_learning_start                   3000
% 2.77/0.98  --inst_learning_factor                  2
% 2.77/0.98  --inst_start_prop_sim_after_learn       3
% 2.77/0.98  --inst_sel_renew                        solver
% 2.77/0.98  --inst_lit_activity_flag                true
% 2.77/0.98  --inst_restr_to_given                   false
% 2.77/0.98  --inst_activity_threshold               500
% 2.77/0.98  --inst_out_proof                        true
% 2.77/0.98  
% 2.77/0.98  ------ Resolution Options
% 2.77/0.98  
% 2.77/0.98  --resolution_flag                       false
% 2.77/0.98  --res_lit_sel                           adaptive
% 2.77/0.98  --res_lit_sel_side                      none
% 2.77/0.98  --res_ordering                          kbo
% 2.77/0.98  --res_to_prop_solver                    active
% 2.77/0.98  --res_prop_simpl_new                    false
% 2.77/0.98  --res_prop_simpl_given                  true
% 2.77/0.98  --res_passive_queue_type                priority_queues
% 2.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/0.98  --res_passive_queues_freq               [15;5]
% 2.77/0.98  --res_forward_subs                      full
% 2.77/0.98  --res_backward_subs                     full
% 2.77/0.98  --res_forward_subs_resolution           true
% 2.77/0.98  --res_backward_subs_resolution          true
% 2.77/0.98  --res_orphan_elimination                true
% 2.77/0.98  --res_time_limit                        2.
% 2.77/0.98  --res_out_proof                         true
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Options
% 2.77/0.98  
% 2.77/0.98  --superposition_flag                    true
% 2.77/0.98  --sup_passive_queue_type                priority_queues
% 2.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.77/0.98  --demod_completeness_check              fast
% 2.77/0.98  --demod_use_ground                      true
% 2.77/0.98  --sup_to_prop_solver                    passive
% 2.77/0.98  --sup_prop_simpl_new                    true
% 2.77/0.98  --sup_prop_simpl_given                  true
% 2.77/0.98  --sup_fun_splitting                     false
% 2.77/0.98  --sup_smt_interval                      50000
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Simplification Setup
% 2.77/0.98  
% 2.77/0.98  --sup_indices_passive                   []
% 2.77/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_full_bw                           [BwDemod]
% 2.77/0.98  --sup_immed_triv                        [TrivRules]
% 2.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_immed_bw_main                     []
% 2.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.98  
% 2.77/0.98  ------ Combination Options
% 2.77/0.98  
% 2.77/0.98  --comb_res_mult                         3
% 2.77/0.98  --comb_sup_mult                         2
% 2.77/0.98  --comb_inst_mult                        10
% 2.77/0.98  
% 2.77/0.98  ------ Debug Options
% 2.77/0.98  
% 2.77/0.98  --dbg_backtrace                         false
% 2.77/0.98  --dbg_dump_prop_clauses                 false
% 2.77/0.98  --dbg_dump_prop_clauses_file            -
% 2.77/0.98  --dbg_out_stat                          false
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  ------ Proving...
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  % SZS status Theorem for theBenchmark.p
% 2.77/0.98  
% 2.77/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/0.98  
% 2.77/0.98  fof(f1,axiom,(
% 2.77/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.77/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/0.98  
% 2.77/0.98  fof(f12,plain,(
% 2.77/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.77/0.98    inference(ennf_transformation,[],[f1])).
% 2.77/0.98  
% 2.77/0.98  fof(f19,plain,(
% 2.77/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.77/0.98    inference(nnf_transformation,[],[f12])).
% 2.77/0.98  
% 2.77/0.98  fof(f20,plain,(
% 2.77/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.77/0.98    inference(rectify,[],[f19])).
% 2.77/0.98  
% 2.77/0.98  fof(f21,plain,(
% 2.77/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.77/0.98    introduced(choice_axiom,[])).
% 2.77/0.98  
% 2.77/0.98  fof(f22,plain,(
% 2.77/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 2.77/0.98  
% 2.77/0.98  fof(f39,plain,(
% 2.77/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f22])).
% 2.77/0.98  
% 2.77/0.98  fof(f7,axiom,(
% 2.77/0.98    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.77/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/0.98  
% 2.77/0.98  fof(f23,plain,(
% 2.77/0.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.77/0.98    inference(nnf_transformation,[],[f7])).
% 2.77/0.98  
% 2.77/0.98  fof(f24,plain,(
% 2.77/0.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.77/0.98    inference(rectify,[],[f23])).
% 2.77/0.98  
% 2.77/0.98  fof(f27,plain,(
% 2.77/0.98    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.77/0.98    introduced(choice_axiom,[])).
% 2.77/0.98  
% 2.77/0.98  fof(f26,plain,(
% 2.77/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.77/0.98    introduced(choice_axiom,[])).
% 2.77/0.98  
% 2.77/0.98  fof(f25,plain,(
% 2.77/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.77/0.98    introduced(choice_axiom,[])).
% 2.77/0.98  
% 2.77/0.98  fof(f28,plain,(
% 2.77/0.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f27,f26,f25])).
% 2.77/0.98  
% 2.77/0.98  fof(f46,plain,(
% 2.77/0.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.77/0.98    inference(cnf_transformation,[],[f28])).
% 2.77/0.98  
% 2.77/0.98  fof(f65,plain,(
% 2.77/0.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.77/0.98    inference(equality_resolution,[],[f46])).
% 2.77/0.98  
% 2.77/0.98  fof(f38,plain,(
% 2.77/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f22])).
% 2.77/0.98  
% 2.77/0.98  fof(f47,plain,(
% 2.77/0.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.77/0.98    inference(cnf_transformation,[],[f28])).
% 2.77/0.98  
% 2.77/0.98  fof(f64,plain,(
% 2.77/0.98    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.77/0.98    inference(equality_resolution,[],[f47])).
% 2.77/0.98  
% 2.77/0.98  fof(f40,plain,(
% 2.77/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f22])).
% 2.77/0.98  
% 2.77/0.98  fof(f9,axiom,(
% 2.77/0.98    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 2.77/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/0.98  
% 2.77/0.98  fof(f16,plain,(
% 2.77/0.98    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 2.77/0.98    inference(ennf_transformation,[],[f9])).
% 2.77/0.98  
% 2.77/0.98  fof(f54,plain,(
% 2.77/0.98    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f16])).
% 2.77/0.98  
% 2.77/0.98  fof(f6,axiom,(
% 2.77/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.77/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/0.98  
% 2.77/0.98  fof(f45,plain,(
% 2.77/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.77/0.98    inference(cnf_transformation,[],[f6])).
% 2.77/0.98  
% 2.77/0.98  fof(f5,axiom,(
% 2.77/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f44,plain,(
% 2.77/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f5])).
% 2.77/0.99  
% 2.77/0.99  fof(f59,plain,(
% 2.77/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.77/0.99    inference(definition_unfolding,[],[f45,f44])).
% 2.77/0.99  
% 2.77/0.99  fof(f63,plain,(
% 2.77/0.99    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.77/0.99    inference(definition_unfolding,[],[f54,f59])).
% 2.77/0.99  
% 2.77/0.99  fof(f10,conjecture,(
% 2.77/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f11,negated_conjecture,(
% 2.77/0.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.77/0.99    inference(negated_conjecture,[],[f10])).
% 2.77/0.99  
% 2.77/0.99  fof(f17,plain,(
% 2.77/0.99    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.77/0.99    inference(ennf_transformation,[],[f11])).
% 2.77/0.99  
% 2.77/0.99  fof(f18,plain,(
% 2.77/0.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.77/0.99    inference(flattening,[],[f17])).
% 2.77/0.99  
% 2.77/0.99  fof(f36,plain,(
% 2.77/0.99    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK8)) & r1_tarski(X0,sK8) & v1_relat_1(sK8))) )),
% 2.77/0.99    introduced(choice_axiom,[])).
% 2.77/0.99  
% 2.77/0.99  fof(f35,plain,(
% 2.77/0.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK7),k3_relat_1(X1)) & r1_tarski(sK7,X1) & v1_relat_1(X1)) & v1_relat_1(sK7))),
% 2.77/0.99    introduced(choice_axiom,[])).
% 2.77/0.99  
% 2.77/0.99  fof(f37,plain,(
% 2.77/0.99    (~r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) & r1_tarski(sK7,sK8) & v1_relat_1(sK8)) & v1_relat_1(sK7)),
% 2.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f18,f36,f35])).
% 2.77/0.99  
% 2.77/0.99  fof(f56,plain,(
% 2.77/0.99    v1_relat_1(sK8)),
% 2.77/0.99    inference(cnf_transformation,[],[f37])).
% 2.77/0.99  
% 2.77/0.99  fof(f4,axiom,(
% 2.77/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f43,plain,(
% 2.77/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f4])).
% 2.77/0.99  
% 2.77/0.99  fof(f62,plain,(
% 2.77/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.77/0.99    inference(definition_unfolding,[],[f43,f44,f44])).
% 2.77/0.99  
% 2.77/0.99  fof(f2,axiom,(
% 2.77/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f13,plain,(
% 2.77/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.77/0.99    inference(ennf_transformation,[],[f2])).
% 2.77/0.99  
% 2.77/0.99  fof(f41,plain,(
% 2.77/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f13])).
% 2.77/0.99  
% 2.77/0.99  fof(f60,plain,(
% 2.77/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.77/0.99    inference(definition_unfolding,[],[f41,f59])).
% 2.77/0.99  
% 2.77/0.99  fof(f8,axiom,(
% 2.77/0.99    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f29,plain,(
% 2.77/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 2.77/0.99    inference(nnf_transformation,[],[f8])).
% 2.77/0.99  
% 2.77/0.99  fof(f30,plain,(
% 2.77/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.77/0.99    inference(rectify,[],[f29])).
% 2.77/0.99  
% 2.77/0.99  fof(f33,plain,(
% 2.77/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 2.77/0.99    introduced(choice_axiom,[])).
% 2.77/0.99  
% 2.77/0.99  fof(f32,plain,(
% 2.77/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 2.77/0.99    introduced(choice_axiom,[])).
% 2.77/0.99  
% 2.77/0.99  fof(f31,plain,(
% 2.77/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.77/0.99    introduced(choice_axiom,[])).
% 2.77/0.99  
% 2.77/0.99  fof(f34,plain,(
% 2.77/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).
% 2.77/0.99  
% 2.77/0.99  fof(f50,plain,(
% 2.77/0.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 2.77/0.99    inference(cnf_transformation,[],[f34])).
% 2.77/0.99  
% 2.77/0.99  fof(f67,plain,(
% 2.77/0.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 2.77/0.99    inference(equality_resolution,[],[f50])).
% 2.77/0.99  
% 2.77/0.99  fof(f51,plain,(
% 2.77/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 2.77/0.99    inference(cnf_transformation,[],[f34])).
% 2.77/0.99  
% 2.77/0.99  fof(f66,plain,(
% 2.77/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 2.77/0.99    inference(equality_resolution,[],[f51])).
% 2.77/0.99  
% 2.77/0.99  fof(f3,axiom,(
% 2.77/0.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f14,plain,(
% 2.77/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.77/0.99    inference(ennf_transformation,[],[f3])).
% 2.77/0.99  
% 2.77/0.99  fof(f15,plain,(
% 2.77/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.77/0.99    inference(flattening,[],[f14])).
% 2.77/0.99  
% 2.77/0.99  fof(f42,plain,(
% 2.77/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f15])).
% 2.77/0.99  
% 2.77/0.99  fof(f61,plain,(
% 2.77/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.77/0.99    inference(definition_unfolding,[],[f42,f59])).
% 2.77/0.99  
% 2.77/0.99  fof(f58,plain,(
% 2.77/0.99    ~r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))),
% 2.77/0.99    inference(cnf_transformation,[],[f37])).
% 2.77/0.99  
% 2.77/0.99  fof(f57,plain,(
% 2.77/0.99    r1_tarski(sK7,sK8)),
% 2.77/0.99    inference(cnf_transformation,[],[f37])).
% 2.77/0.99  
% 2.77/0.99  fof(f55,plain,(
% 2.77/0.99    v1_relat_1(sK7)),
% 2.77/0.99    inference(cnf_transformation,[],[f37])).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1,plain,
% 2.77/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.77/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_611,plain,
% 2.77/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.77/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_9,plain,
% 2.77/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.77/0.99      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.77/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_604,plain,
% 2.77/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.77/0.99      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2,plain,
% 2.77/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.77/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_610,plain,
% 2.77/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.77/0.99      | r2_hidden(X0,X2) = iProver_top
% 2.77/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1885,plain,
% 2.77/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.77/0.99      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X2) = iProver_top
% 2.77/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_604,c_610]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_8,plain,
% 2.77/0.99      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.77/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_605,plain,
% 2.77/0.99      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.77/0.99      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4973,plain,
% 2.77/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.77/0.99      | r2_hidden(X0,k1_relat_1(X2)) = iProver_top
% 2.77/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1885,c_605]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_5283,plain,
% 2.77/0.99      ( r2_hidden(sK0(k1_relat_1(X0),X1),k1_relat_1(X2)) = iProver_top
% 2.77/0.99      | r1_tarski(X0,X2) != iProver_top
% 2.77/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_611,c_4973]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_0,plain,
% 2.77/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.77/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_612,plain,
% 2.77/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.77/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_8436,plain,
% 2.77/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.77/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_5283,c_612]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_14,plain,
% 2.77/0.99      ( ~ v1_relat_1(X0)
% 2.77/0.99      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 2.77/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_17,negated_conjecture,
% 2.77/0.99      ( v1_relat_1(sK8) ),
% 2.77/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_208,plain,
% 2.77/0.99      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 2.77/0.99      | sK8 != X0 ),
% 2.77/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_209,plain,
% 2.77/0.99      ( k3_tarski(k1_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8))) = k3_relat_1(sK8) ),
% 2.77/0.99      inference(unflattening,[status(thm)],[c_208]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_5,plain,
% 2.77/0.99      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 2.77/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_3,plain,
% 2.77/0.99      ( ~ r1_tarski(X0,X1)
% 2.77/0.99      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 2.77/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_609,plain,
% 2.77/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.77/0.99      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1094,plain,
% 2.77/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.77/0.99      | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_5,c_609]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1119,plain,
% 2.77/0.99      ( r1_tarski(X0,k3_relat_1(sK8)) = iProver_top
% 2.77/0.99      | r1_tarski(X0,k1_relat_1(sK8)) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_209,c_1094]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_8593,plain,
% 2.77/0.99      ( r1_tarski(X0,sK8) != iProver_top
% 2.77/0.99      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK8)) = iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_8436,c_1119]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_8644,plain,
% 2.77/0.99      ( r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
% 2.77/0.99      | r1_tarski(sK7,sK8) != iProver_top ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_8593]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_13,plain,
% 2.77/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.77/0.99      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 2.77/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_600,plain,
% 2.77/0.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 2.77/0.99      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1754,plain,
% 2.77/0.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 2.77/0.99      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X2) = iProver_top
% 2.77/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_600,c_610]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_12,plain,
% 2.77/0.99      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 2.77/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_601,plain,
% 2.77/0.99      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 2.77/0.99      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4075,plain,
% 2.77/0.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 2.77/0.99      | r2_hidden(X0,k2_relat_1(X2)) = iProver_top
% 2.77/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1754,c_601]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_5015,plain,
% 2.77/0.99      ( r2_hidden(sK0(k2_relat_1(X0),X1),k2_relat_1(X2)) = iProver_top
% 2.77/0.99      | r1_tarski(X0,X2) != iProver_top
% 2.77/0.99      | r1_tarski(k2_relat_1(X0),X1) = iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_611,c_4075]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_8267,plain,
% 2.77/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.77/0.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_5015,c_612]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1093,plain,
% 2.77/0.99      ( r1_tarski(X0,k3_relat_1(sK8)) = iProver_top
% 2.77/0.99      | r1_tarski(X0,k2_relat_1(sK8)) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_209,c_609]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_8405,plain,
% 2.77/0.99      ( r1_tarski(X0,sK8) != iProver_top
% 2.77/0.99      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK8)) = iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_8267,c_1093]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_8428,plain,
% 2.77/0.99      ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
% 2.77/0.99      | r1_tarski(sK7,sK8) != iProver_top ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_8405]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4,plain,
% 2.77/0.99      ( ~ r1_tarski(X0,X1)
% 2.77/0.99      | ~ r1_tarski(X2,X1)
% 2.77/0.99      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 2.77/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2533,plain,
% 2.77/0.99      ( ~ r1_tarski(X0,k3_relat_1(sK8))
% 2.77/0.99      | ~ r1_tarski(X1,k3_relat_1(sK8))
% 2.77/0.99      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),k3_relat_1(sK8)) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_6560,plain,
% 2.77/0.99      ( ~ r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8))
% 2.77/0.99      | ~ r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8))
% 2.77/0.99      | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_2533]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_6561,plain,
% 2.77/0.99      ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
% 2.77/0.99      | r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
% 2.77/0.99      | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_6560]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_331,plain,
% 2.77/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.77/0.99      theory(equality) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_729,plain,
% 2.77/0.99      ( ~ r1_tarski(X0,X1)
% 2.77/0.99      | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
% 2.77/0.99      | k3_relat_1(sK8) != X1
% 2.77/0.99      | k3_relat_1(sK7) != X0 ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_331]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_750,plain,
% 2.77/0.99      ( ~ r1_tarski(X0,k3_relat_1(sK8))
% 2.77/0.99      | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
% 2.77/0.99      | k3_relat_1(sK8) != k3_relat_1(sK8)
% 2.77/0.99      | k3_relat_1(sK7) != X0 ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_729]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2123,plain,
% 2.77/0.99      ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
% 2.77/0.99      | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8))
% 2.77/0.99      | k3_relat_1(sK8) != k3_relat_1(sK8)
% 2.77/0.99      | k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_750]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2124,plain,
% 2.77/0.99      ( k3_relat_1(sK8) != k3_relat_1(sK8)
% 2.77/0.99      | k3_relat_1(sK7) != k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
% 2.77/0.99      | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
% 2.77/0.99      | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_2123]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_330,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_795,plain,
% 2.77/0.99      ( X0 != X1 | k3_relat_1(sK7) != X1 | k3_relat_1(sK7) = X0 ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_330]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1049,plain,
% 2.77/0.99      ( X0 != k3_relat_1(sK7)
% 2.77/0.99      | k3_relat_1(sK7) = X0
% 2.77/0.99      | k3_relat_1(sK7) != k3_relat_1(sK7) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_795]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1548,plain,
% 2.77/0.99      ( k3_relat_1(sK7) != k3_relat_1(sK7)
% 2.77/0.99      | k3_relat_1(sK7) = k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
% 2.77/0.99      | k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) != k3_relat_1(sK7) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_1049]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_329,plain,( X0 = X0 ),theory(equality) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_751,plain,
% 2.77/0.99      ( k3_relat_1(sK8) = k3_relat_1(sK8) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_329]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_347,plain,
% 2.77/0.99      ( sK7 = sK7 ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_329]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_338,plain,
% 2.77/0.99      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 2.77/0.99      theory(equality) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_345,plain,
% 2.77/0.99      ( k3_relat_1(sK7) = k3_relat_1(sK7) | sK7 != sK7 ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_338]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_24,plain,
% 2.77/0.99      ( ~ v1_relat_1(sK7)
% 2.77/0.99      | k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_15,negated_conjecture,
% 2.77/0.99      ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
% 2.77/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_22,plain,
% 2.77/0.99      ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_16,negated_conjecture,
% 2.77/0.99      ( r1_tarski(sK7,sK8) ),
% 2.77/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_21,plain,
% 2.77/0.99      ( r1_tarski(sK7,sK8) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_18,negated_conjecture,
% 2.77/0.99      ( v1_relat_1(sK7) ),
% 2.77/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(contradiction,plain,
% 2.77/0.99      ( $false ),
% 2.77/0.99      inference(minisat,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_8644,c_8428,c_6561,c_2124,c_1548,c_751,c_347,c_345,
% 2.77/0.99                 c_24,c_22,c_21,c_18]) ).
% 2.77/0.99  
% 2.77/0.99  
% 2.77/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/0.99  
% 2.77/0.99  ------                               Statistics
% 2.77/0.99  
% 2.77/0.99  ------ General
% 2.77/0.99  
% 2.77/0.99  abstr_ref_over_cycles:                  0
% 2.77/0.99  abstr_ref_under_cycles:                 0
% 2.77/0.99  gc_basic_clause_elim:                   0
% 2.77/0.99  forced_gc_time:                         0
% 2.77/0.99  parsing_time:                           0.008
% 2.77/0.99  unif_index_cands_time:                  0.
% 2.77/0.99  unif_index_add_time:                    0.
% 2.77/0.99  orderings_time:                         0.
% 2.77/0.99  out_proof_time:                         0.006
% 2.77/0.99  total_time:                             0.248
% 2.77/0.99  num_of_symbols:                         49
% 2.77/0.99  num_of_terms:                           7441
% 2.77/0.99  
% 2.77/0.99  ------ Preprocessing
% 2.77/0.99  
% 2.77/0.99  num_of_splits:                          0
% 2.77/0.99  num_of_split_atoms:                     0
% 2.77/0.99  num_of_reused_defs:                     0
% 2.77/0.99  num_eq_ax_congr_red:                    44
% 2.77/0.99  num_of_sem_filtered_clauses:            1
% 2.77/0.99  num_of_subtypes:                        0
% 2.77/0.99  monotx_restored_types:                  0
% 2.77/0.99  sat_num_of_epr_types:                   0
% 2.77/0.99  sat_num_of_non_cyclic_types:            0
% 2.77/0.99  sat_guarded_non_collapsed_types:        0
% 2.77/0.99  num_pure_diseq_elim:                    0
% 2.77/0.99  simp_replaced_by:                       0
% 2.77/0.99  res_preprocessed:                       94
% 2.77/0.99  prep_upred:                             0
% 2.77/0.99  prep_unflattend:                        2
% 2.77/0.99  smt_new_axioms:                         0
% 2.77/0.99  pred_elim_cands:                        2
% 2.77/0.99  pred_elim:                              1
% 2.77/0.99  pred_elim_cl:                           1
% 2.77/0.99  pred_elim_cycles:                       3
% 2.77/0.99  merged_defs:                            0
% 2.77/0.99  merged_defs_ncl:                        0
% 2.77/0.99  bin_hyper_res:                          0
% 2.77/0.99  prep_cycles:                            4
% 2.77/0.99  pred_elim_time:                         0.
% 2.77/0.99  splitting_time:                         0.
% 2.77/0.99  sem_filter_time:                        0.
% 2.77/0.99  monotx_time:                            0.001
% 2.77/0.99  subtype_inf_time:                       0.
% 2.77/0.99  
% 2.77/0.99  ------ Problem properties
% 2.77/0.99  
% 2.77/0.99  clauses:                                18
% 2.77/0.99  conjectures:                            2
% 2.77/0.99  epr:                                    2
% 2.77/0.99  horn:                                   15
% 2.77/0.99  ground:                                 4
% 2.77/0.99  unary:                                  5
% 2.77/0.99  binary:                                 7
% 2.77/0.99  lits:                                   37
% 2.77/0.99  lits_eq:                                7
% 2.77/0.99  fd_pure:                                0
% 2.77/0.99  fd_pseudo:                              0
% 2.77/0.99  fd_cond:                                0
% 2.77/0.99  fd_pseudo_cond:                         4
% 2.77/0.99  ac_symbols:                             0
% 2.77/0.99  
% 2.77/0.99  ------ Propositional Solver
% 2.77/0.99  
% 2.77/0.99  prop_solver_calls:                      30
% 2.77/0.99  prop_fast_solver_calls:                 704
% 2.77/0.99  smt_solver_calls:                       0
% 2.77/0.99  smt_fast_solver_calls:                  0
% 2.77/0.99  prop_num_of_clauses:                    3221
% 2.77/0.99  prop_preprocess_simplified:             6217
% 2.77/0.99  prop_fo_subsumed:                       13
% 2.77/0.99  prop_solver_time:                       0.
% 2.77/0.99  smt_solver_time:                        0.
% 2.77/0.99  smt_fast_solver_time:                   0.
% 2.77/0.99  prop_fast_solver_time:                  0.
% 2.77/0.99  prop_unsat_core_time:                   0.
% 2.77/0.99  
% 2.77/0.99  ------ QBF
% 2.77/0.99  
% 2.77/0.99  qbf_q_res:                              0
% 2.77/0.99  qbf_num_tautologies:                    0
% 2.77/0.99  qbf_prep_cycles:                        0
% 2.77/0.99  
% 2.77/0.99  ------ BMC1
% 2.77/0.99  
% 2.77/0.99  bmc1_current_bound:                     -1
% 2.77/0.99  bmc1_last_solved_bound:                 -1
% 2.77/0.99  bmc1_unsat_core_size:                   -1
% 2.77/0.99  bmc1_unsat_core_parents_size:           -1
% 2.77/0.99  bmc1_merge_next_fun:                    0
% 2.77/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.77/0.99  
% 2.77/0.99  ------ Instantiation
% 2.77/0.99  
% 2.77/0.99  inst_num_of_clauses:                    811
% 2.77/0.99  inst_num_in_passive:                    85
% 2.77/0.99  inst_num_in_active:                     415
% 2.77/0.99  inst_num_in_unprocessed:                311
% 2.77/0.99  inst_num_of_loops:                      510
% 2.77/0.99  inst_num_of_learning_restarts:          0
% 2.77/0.99  inst_num_moves_active_passive:          90
% 2.77/0.99  inst_lit_activity:                      0
% 2.77/0.99  inst_lit_activity_moves:                0
% 2.77/0.99  inst_num_tautologies:                   0
% 2.77/0.99  inst_num_prop_implied:                  0
% 2.77/0.99  inst_num_existing_simplified:           0
% 2.77/0.99  inst_num_eq_res_simplified:             0
% 2.77/0.99  inst_num_child_elim:                    0
% 2.77/0.99  inst_num_of_dismatching_blockings:      325
% 2.77/0.99  inst_num_of_non_proper_insts:           1028
% 2.77/0.99  inst_num_of_duplicates:                 0
% 2.77/0.99  inst_inst_num_from_inst_to_res:         0
% 2.77/0.99  inst_dismatching_checking_time:         0.
% 2.77/0.99  
% 2.77/0.99  ------ Resolution
% 2.77/0.99  
% 2.77/0.99  res_num_of_clauses:                     0
% 2.77/0.99  res_num_in_passive:                     0
% 2.77/0.99  res_num_in_active:                      0
% 2.77/0.99  res_num_of_loops:                       98
% 2.77/0.99  res_forward_subset_subsumed:            83
% 2.77/0.99  res_backward_subset_subsumed:           0
% 2.77/0.99  res_forward_subsumed:                   0
% 2.77/0.99  res_backward_subsumed:                  0
% 2.77/0.99  res_forward_subsumption_resolution:     0
% 2.77/0.99  res_backward_subsumption_resolution:    0
% 2.77/0.99  res_clause_to_clause_subsumption:       1964
% 2.77/0.99  res_orphan_elimination:                 0
% 2.77/0.99  res_tautology_del:                      92
% 2.77/0.99  res_num_eq_res_simplified:              0
% 2.77/0.99  res_num_sel_changes:                    0
% 2.77/0.99  res_moves_from_active_to_pass:          0
% 2.77/0.99  
% 2.77/0.99  ------ Superposition
% 2.77/0.99  
% 2.77/0.99  sup_time_total:                         0.
% 2.77/0.99  sup_time_generating:                    0.
% 2.77/0.99  sup_time_sim_full:                      0.
% 2.77/0.99  sup_time_sim_immed:                     0.
% 2.77/0.99  
% 2.77/0.99  sup_num_of_clauses:                     246
% 2.77/0.99  sup_num_in_active:                      101
% 2.77/0.99  sup_num_in_passive:                     145
% 2.77/0.99  sup_num_of_loops:                       100
% 2.77/0.99  sup_fw_superposition:                   227
% 2.77/0.99  sup_bw_superposition:                   107
% 2.77/0.99  sup_immediate_simplified:               20
% 2.77/0.99  sup_given_eliminated:                   0
% 2.77/0.99  comparisons_done:                       0
% 2.77/0.99  comparisons_avoided:                    0
% 2.77/0.99  
% 2.77/0.99  ------ Simplifications
% 2.77/0.99  
% 2.77/0.99  
% 2.77/0.99  sim_fw_subset_subsumed:                 9
% 2.77/0.99  sim_bw_subset_subsumed:                 2
% 2.77/0.99  sim_fw_subsumed:                        5
% 2.77/0.99  sim_bw_subsumed:                        0
% 2.77/0.99  sim_fw_subsumption_res:                 2
% 2.77/0.99  sim_bw_subsumption_res:                 0
% 2.77/0.99  sim_tautology_del:                      11
% 2.77/0.99  sim_eq_tautology_del:                   4
% 2.77/0.99  sim_eq_res_simp:                        0
% 2.77/0.99  sim_fw_demodulated:                     0
% 2.77/0.99  sim_bw_demodulated:                     0
% 2.77/0.99  sim_light_normalised:                   10
% 2.77/0.99  sim_joinable_taut:                      0
% 2.77/0.99  sim_joinable_simp:                      0
% 2.77/0.99  sim_ac_normalised:                      0
% 2.77/0.99  sim_smt_subsumption:                    0
% 2.77/0.99  
%------------------------------------------------------------------------------
