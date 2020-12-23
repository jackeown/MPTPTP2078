%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:07 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 235 expanded)
%              Number of clauses        :   29 (  37 expanded)
%              Number of leaves         :   22 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  246 ( 508 expanded)
%              Number of equality atoms :   70 ( 173 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f77])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f78])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f80])).

fof(f84,plain,(
    ! [X0] :
      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f72,f81])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k3_relat_1(X2))
          | ~ r2_hidden(X0,k3_relat_1(X2)) )
        & r2_hidden(k4_tarski(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK9,k3_relat_1(sK10))
        | ~ r2_hidden(sK8,k3_relat_1(sK10)) )
      & r2_hidden(k4_tarski(sK8,sK9),sK10)
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ r2_hidden(sK9,k3_relat_1(sK10))
      | ~ r2_hidden(sK8,k3_relat_1(sK10)) )
    & r2_hidden(k4_tarski(sK8,sK9),sK10)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f23,f44])).

fof(f73,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f83,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f50,f80,f80])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f81])).

fof(f74,plain,(
    r2_hidden(k4_tarski(sK8,sK9),sK10) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f39,f42,f41,f40])).

fof(f69,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f75,plain,
    ( ~ r2_hidden(sK9,k3_relat_1(sK10))
    | ~ r2_hidden(sK8,k3_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_296,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_297,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(sK10),k1_relat_1(sK10),k1_relat_1(sK10),k1_relat_1(sK10),k1_relat_1(sK10),k1_relat_1(sK10),k1_relat_1(sK10),k2_relat_1(sK10))) = k3_relat_1(sK10) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_4,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1463,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2322,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1463])).

cnf(c_2700,plain,
    ( r1_tarski(k2_relat_1(sK10),k3_relat_1(sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_297,c_2322])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1448,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1451,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2859,plain,
    ( r2_hidden(sK9,k2_relat_1(sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_1451])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1464,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3343,plain,
    ( r2_hidden(sK9,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK10),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2859,c_1464])).

cnf(c_3650,plain,
    ( r2_hidden(sK9,k3_relat_1(sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2700,c_3343])).

cnf(c_1666,plain,
    ( r2_hidden(sK8,X0)
    | ~ r2_hidden(sK8,k1_relat_1(sK10))
    | ~ r1_tarski(k1_relat_1(sK10),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2731,plain,
    ( r2_hidden(sK8,k3_relat_1(sK10))
    | ~ r2_hidden(sK8,k1_relat_1(sK10))
    | ~ r1_tarski(k1_relat_1(sK10),k3_relat_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_2732,plain,
    ( r2_hidden(sK8,k3_relat_1(sK10)) = iProver_top
    | r2_hidden(sK8,k1_relat_1(sK10)) != iProver_top
    | r1_tarski(k1_relat_1(sK10),k3_relat_1(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2731])).

cnf(c_2321,plain,
    ( r1_tarski(k1_relat_1(sK10),k3_relat_1(sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_297,c_1463])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1617,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
    | r2_hidden(sK8,k1_relat_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1618,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10) != iProver_top
    | r2_hidden(sK8,k1_relat_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1617])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(sK8,k3_relat_1(sK10))
    | ~ r2_hidden(sK9,k3_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,plain,
    ( r2_hidden(sK8,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(sK9,k3_relat_1(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3650,c_2732,c_2321,c_1618,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:52:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.98/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/0.98  
% 1.98/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.98/0.98  
% 1.98/0.98  ------  iProver source info
% 1.98/0.98  
% 1.98/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.98/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.98/0.98  git: non_committed_changes: false
% 1.98/0.98  git: last_make_outside_of_git: false
% 1.98/0.98  
% 1.98/0.98  ------ 
% 1.98/0.98  
% 1.98/0.98  ------ Input Options
% 1.98/0.98  
% 1.98/0.98  --out_options                           all
% 1.98/0.98  --tptp_safe_out                         true
% 1.98/0.98  --problem_path                          ""
% 1.98/0.98  --include_path                          ""
% 1.98/0.98  --clausifier                            res/vclausify_rel
% 1.98/0.98  --clausifier_options                    --mode clausify
% 1.98/0.98  --stdin                                 false
% 1.98/0.98  --stats_out                             all
% 1.98/0.98  
% 1.98/0.98  ------ General Options
% 1.98/0.98  
% 1.98/0.98  --fof                                   false
% 1.98/0.98  --time_out_real                         305.
% 1.98/0.98  --time_out_virtual                      -1.
% 1.98/0.98  --symbol_type_check                     false
% 1.98/0.98  --clausify_out                          false
% 1.98/0.98  --sig_cnt_out                           false
% 1.98/0.99  --trig_cnt_out                          false
% 1.98/0.99  --trig_cnt_out_tolerance                1.
% 1.98/0.99  --trig_cnt_out_sk_spl                   false
% 1.98/0.99  --abstr_cl_out                          false
% 1.98/0.99  
% 1.98/0.99  ------ Global Options
% 1.98/0.99  
% 1.98/0.99  --schedule                              default
% 1.98/0.99  --add_important_lit                     false
% 1.98/0.99  --prop_solver_per_cl                    1000
% 1.98/0.99  --min_unsat_core                        false
% 1.98/0.99  --soft_assumptions                      false
% 1.98/0.99  --soft_lemma_size                       3
% 1.98/0.99  --prop_impl_unit_size                   0
% 1.98/0.99  --prop_impl_unit                        []
% 1.98/0.99  --share_sel_clauses                     true
% 1.98/0.99  --reset_solvers                         false
% 1.98/0.99  --bc_imp_inh                            [conj_cone]
% 1.98/0.99  --conj_cone_tolerance                   3.
% 1.98/0.99  --extra_neg_conj                        none
% 1.98/0.99  --large_theory_mode                     true
% 1.98/0.99  --prolific_symb_bound                   200
% 1.98/0.99  --lt_threshold                          2000
% 1.98/0.99  --clause_weak_htbl                      true
% 1.98/0.99  --gc_record_bc_elim                     false
% 1.98/0.99  
% 1.98/0.99  ------ Preprocessing Options
% 1.98/0.99  
% 1.98/0.99  --preprocessing_flag                    true
% 1.98/0.99  --time_out_prep_mult                    0.1
% 1.98/0.99  --splitting_mode                        input
% 1.98/0.99  --splitting_grd                         true
% 1.98/0.99  --splitting_cvd                         false
% 1.98/0.99  --splitting_cvd_svl                     false
% 1.98/0.99  --splitting_nvd                         32
% 1.98/0.99  --sub_typing                            true
% 1.98/0.99  --prep_gs_sim                           true
% 1.98/0.99  --prep_unflatten                        true
% 1.98/0.99  --prep_res_sim                          true
% 1.98/0.99  --prep_upred                            true
% 1.98/0.99  --prep_sem_filter                       exhaustive
% 1.98/0.99  --prep_sem_filter_out                   false
% 1.98/0.99  --pred_elim                             true
% 1.98/0.99  --res_sim_input                         true
% 1.98/0.99  --eq_ax_congr_red                       true
% 1.98/0.99  --pure_diseq_elim                       true
% 1.98/0.99  --brand_transform                       false
% 1.98/0.99  --non_eq_to_eq                          false
% 1.98/0.99  --prep_def_merge                        true
% 1.98/0.99  --prep_def_merge_prop_impl              false
% 1.98/0.99  --prep_def_merge_mbd                    true
% 1.98/0.99  --prep_def_merge_tr_red                 false
% 1.98/0.99  --prep_def_merge_tr_cl                  false
% 1.98/0.99  --smt_preprocessing                     true
% 1.98/0.99  --smt_ac_axioms                         fast
% 1.98/0.99  --preprocessed_out                      false
% 1.98/0.99  --preprocessed_stats                    false
% 1.98/0.99  
% 1.98/0.99  ------ Abstraction refinement Options
% 1.98/0.99  
% 1.98/0.99  --abstr_ref                             []
% 1.98/0.99  --abstr_ref_prep                        false
% 1.98/0.99  --abstr_ref_until_sat                   false
% 1.98/0.99  --abstr_ref_sig_restrict                funpre
% 1.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.98/0.99  --abstr_ref_under                       []
% 1.98/0.99  
% 1.98/0.99  ------ SAT Options
% 1.98/0.99  
% 1.98/0.99  --sat_mode                              false
% 1.98/0.99  --sat_fm_restart_options                ""
% 1.98/0.99  --sat_gr_def                            false
% 1.98/0.99  --sat_epr_types                         true
% 1.98/0.99  --sat_non_cyclic_types                  false
% 1.98/0.99  --sat_finite_models                     false
% 1.98/0.99  --sat_fm_lemmas                         false
% 1.98/0.99  --sat_fm_prep                           false
% 1.98/0.99  --sat_fm_uc_incr                        true
% 1.98/0.99  --sat_out_model                         small
% 1.98/0.99  --sat_out_clauses                       false
% 1.98/0.99  
% 1.98/0.99  ------ QBF Options
% 1.98/0.99  
% 1.98/0.99  --qbf_mode                              false
% 1.98/0.99  --qbf_elim_univ                         false
% 1.98/0.99  --qbf_dom_inst                          none
% 1.98/0.99  --qbf_dom_pre_inst                      false
% 1.98/0.99  --qbf_sk_in                             false
% 1.98/0.99  --qbf_pred_elim                         true
% 1.98/0.99  --qbf_split                             512
% 1.98/0.99  
% 1.98/0.99  ------ BMC1 Options
% 1.98/0.99  
% 1.98/0.99  --bmc1_incremental                      false
% 1.98/0.99  --bmc1_axioms                           reachable_all
% 1.98/0.99  --bmc1_min_bound                        0
% 1.98/0.99  --bmc1_max_bound                        -1
% 1.98/0.99  --bmc1_max_bound_default                -1
% 1.98/0.99  --bmc1_symbol_reachability              true
% 1.98/0.99  --bmc1_property_lemmas                  false
% 1.98/0.99  --bmc1_k_induction                      false
% 1.98/0.99  --bmc1_non_equiv_states                 false
% 1.98/0.99  --bmc1_deadlock                         false
% 1.98/0.99  --bmc1_ucm                              false
% 1.98/0.99  --bmc1_add_unsat_core                   none
% 1.98/0.99  --bmc1_unsat_core_children              false
% 1.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.98/0.99  --bmc1_out_stat                         full
% 1.98/0.99  --bmc1_ground_init                      false
% 1.98/0.99  --bmc1_pre_inst_next_state              false
% 1.98/0.99  --bmc1_pre_inst_state                   false
% 1.98/0.99  --bmc1_pre_inst_reach_state             false
% 1.98/0.99  --bmc1_out_unsat_core                   false
% 1.98/0.99  --bmc1_aig_witness_out                  false
% 1.98/0.99  --bmc1_verbose                          false
% 1.98/0.99  --bmc1_dump_clauses_tptp                false
% 1.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.98/0.99  --bmc1_dump_file                        -
% 1.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.98/0.99  --bmc1_ucm_extend_mode                  1
% 1.98/0.99  --bmc1_ucm_init_mode                    2
% 1.98/0.99  --bmc1_ucm_cone_mode                    none
% 1.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.98/0.99  --bmc1_ucm_relax_model                  4
% 1.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.98/0.99  --bmc1_ucm_layered_model                none
% 1.98/0.99  --bmc1_ucm_max_lemma_size               10
% 1.98/0.99  
% 1.98/0.99  ------ AIG Options
% 1.98/0.99  
% 1.98/0.99  --aig_mode                              false
% 1.98/0.99  
% 1.98/0.99  ------ Instantiation Options
% 1.98/0.99  
% 1.98/0.99  --instantiation_flag                    true
% 1.98/0.99  --inst_sos_flag                         false
% 1.98/0.99  --inst_sos_phase                        true
% 1.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.98/0.99  --inst_lit_sel_side                     num_symb
% 1.98/0.99  --inst_solver_per_active                1400
% 1.98/0.99  --inst_solver_calls_frac                1.
% 1.98/0.99  --inst_passive_queue_type               priority_queues
% 1.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.98/0.99  --inst_passive_queues_freq              [25;2]
% 1.98/0.99  --inst_dismatching                      true
% 1.98/0.99  --inst_eager_unprocessed_to_passive     true
% 1.98/0.99  --inst_prop_sim_given                   true
% 1.98/0.99  --inst_prop_sim_new                     false
% 1.98/0.99  --inst_subs_new                         false
% 1.98/0.99  --inst_eq_res_simp                      false
% 1.98/0.99  --inst_subs_given                       false
% 1.98/0.99  --inst_orphan_elimination               true
% 1.98/0.99  --inst_learning_loop_flag               true
% 1.98/0.99  --inst_learning_start                   3000
% 1.98/0.99  --inst_learning_factor                  2
% 1.98/0.99  --inst_start_prop_sim_after_learn       3
% 1.98/0.99  --inst_sel_renew                        solver
% 1.98/0.99  --inst_lit_activity_flag                true
% 1.98/0.99  --inst_restr_to_given                   false
% 1.98/0.99  --inst_activity_threshold               500
% 1.98/0.99  --inst_out_proof                        true
% 1.98/0.99  
% 1.98/0.99  ------ Resolution Options
% 1.98/0.99  
% 1.98/0.99  --resolution_flag                       true
% 1.98/0.99  --res_lit_sel                           adaptive
% 1.98/0.99  --res_lit_sel_side                      none
% 1.98/0.99  --res_ordering                          kbo
% 1.98/0.99  --res_to_prop_solver                    active
% 1.98/0.99  --res_prop_simpl_new                    false
% 1.98/0.99  --res_prop_simpl_given                  true
% 1.98/0.99  --res_passive_queue_type                priority_queues
% 1.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.98/0.99  --res_passive_queues_freq               [15;5]
% 1.98/0.99  --res_forward_subs                      full
% 1.98/0.99  --res_backward_subs                     full
% 1.98/0.99  --res_forward_subs_resolution           true
% 1.98/0.99  --res_backward_subs_resolution          true
% 1.98/0.99  --res_orphan_elimination                true
% 1.98/0.99  --res_time_limit                        2.
% 1.98/0.99  --res_out_proof                         true
% 1.98/0.99  
% 1.98/0.99  ------ Superposition Options
% 1.98/0.99  
% 1.98/0.99  --superposition_flag                    true
% 1.98/0.99  --sup_passive_queue_type                priority_queues
% 1.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.98/0.99  --demod_completeness_check              fast
% 1.98/0.99  --demod_use_ground                      true
% 1.98/0.99  --sup_to_prop_solver                    passive
% 1.98/0.99  --sup_prop_simpl_new                    true
% 1.98/0.99  --sup_prop_simpl_given                  true
% 1.98/0.99  --sup_fun_splitting                     false
% 1.98/0.99  --sup_smt_interval                      50000
% 1.98/0.99  
% 1.98/0.99  ------ Superposition Simplification Setup
% 1.98/0.99  
% 1.98/0.99  --sup_indices_passive                   []
% 1.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.99  --sup_full_bw                           [BwDemod]
% 1.98/0.99  --sup_immed_triv                        [TrivRules]
% 1.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.99  --sup_immed_bw_main                     []
% 1.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.99  
% 1.98/0.99  ------ Combination Options
% 1.98/0.99  
% 1.98/0.99  --comb_res_mult                         3
% 1.98/0.99  --comb_sup_mult                         2
% 1.98/0.99  --comb_inst_mult                        10
% 1.98/0.99  
% 1.98/0.99  ------ Debug Options
% 1.98/0.99  
% 1.98/0.99  --dbg_backtrace                         false
% 1.98/0.99  --dbg_dump_prop_clauses                 false
% 1.98/0.99  --dbg_dump_prop_clauses_file            -
% 1.98/0.99  --dbg_out_stat                          false
% 1.98/0.99  ------ Parsing...
% 1.98/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.98/0.99  
% 1.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.98/0.99  
% 1.98/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.98/0.99  
% 1.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.98/0.99  ------ Proving...
% 1.98/0.99  ------ Problem Properties 
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  clauses                                 22
% 1.98/0.99  conjectures                             2
% 1.98/0.99  EPR                                     1
% 1.98/0.99  Horn                                    18
% 1.98/0.99  unary                                   5
% 1.98/0.99  binary                                  10
% 1.98/0.99  lits                                    46
% 1.98/0.99  lits eq                                 9
% 1.98/0.99  fd_pure                                 0
% 1.98/0.99  fd_pseudo                               0
% 1.98/0.99  fd_cond                                 0
% 1.98/0.99  fd_pseudo_cond                          6
% 1.98/0.99  AC symbols                              0
% 1.98/0.99  
% 1.98/0.99  ------ Schedule dynamic 5 is on 
% 1.98/0.99  
% 1.98/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  ------ 
% 1.98/0.99  Current options:
% 1.98/0.99  ------ 
% 1.98/0.99  
% 1.98/0.99  ------ Input Options
% 1.98/0.99  
% 1.98/0.99  --out_options                           all
% 1.98/0.99  --tptp_safe_out                         true
% 1.98/0.99  --problem_path                          ""
% 1.98/0.99  --include_path                          ""
% 1.98/0.99  --clausifier                            res/vclausify_rel
% 1.98/0.99  --clausifier_options                    --mode clausify
% 1.98/0.99  --stdin                                 false
% 1.98/0.99  --stats_out                             all
% 1.98/0.99  
% 1.98/0.99  ------ General Options
% 1.98/0.99  
% 1.98/0.99  --fof                                   false
% 1.98/0.99  --time_out_real                         305.
% 1.98/0.99  --time_out_virtual                      -1.
% 1.98/0.99  --symbol_type_check                     false
% 1.98/0.99  --clausify_out                          false
% 1.98/0.99  --sig_cnt_out                           false
% 1.98/0.99  --trig_cnt_out                          false
% 1.98/0.99  --trig_cnt_out_tolerance                1.
% 1.98/0.99  --trig_cnt_out_sk_spl                   false
% 1.98/0.99  --abstr_cl_out                          false
% 1.98/0.99  
% 1.98/0.99  ------ Global Options
% 1.98/0.99  
% 1.98/0.99  --schedule                              default
% 1.98/0.99  --add_important_lit                     false
% 1.98/0.99  --prop_solver_per_cl                    1000
% 1.98/0.99  --min_unsat_core                        false
% 1.98/0.99  --soft_assumptions                      false
% 1.98/0.99  --soft_lemma_size                       3
% 1.98/0.99  --prop_impl_unit_size                   0
% 1.98/0.99  --prop_impl_unit                        []
% 1.98/0.99  --share_sel_clauses                     true
% 1.98/0.99  --reset_solvers                         false
% 1.98/0.99  --bc_imp_inh                            [conj_cone]
% 1.98/0.99  --conj_cone_tolerance                   3.
% 1.98/0.99  --extra_neg_conj                        none
% 1.98/0.99  --large_theory_mode                     true
% 1.98/0.99  --prolific_symb_bound                   200
% 1.98/0.99  --lt_threshold                          2000
% 1.98/0.99  --clause_weak_htbl                      true
% 1.98/0.99  --gc_record_bc_elim                     false
% 1.98/0.99  
% 1.98/0.99  ------ Preprocessing Options
% 1.98/0.99  
% 1.98/0.99  --preprocessing_flag                    true
% 1.98/0.99  --time_out_prep_mult                    0.1
% 1.98/0.99  --splitting_mode                        input
% 1.98/0.99  --splitting_grd                         true
% 1.98/0.99  --splitting_cvd                         false
% 1.98/0.99  --splitting_cvd_svl                     false
% 1.98/0.99  --splitting_nvd                         32
% 1.98/0.99  --sub_typing                            true
% 1.98/0.99  --prep_gs_sim                           true
% 1.98/0.99  --prep_unflatten                        true
% 1.98/0.99  --prep_res_sim                          true
% 1.98/0.99  --prep_upred                            true
% 1.98/0.99  --prep_sem_filter                       exhaustive
% 1.98/0.99  --prep_sem_filter_out                   false
% 1.98/0.99  --pred_elim                             true
% 1.98/0.99  --res_sim_input                         true
% 1.98/0.99  --eq_ax_congr_red                       true
% 1.98/0.99  --pure_diseq_elim                       true
% 1.98/0.99  --brand_transform                       false
% 1.98/0.99  --non_eq_to_eq                          false
% 1.98/0.99  --prep_def_merge                        true
% 1.98/0.99  --prep_def_merge_prop_impl              false
% 1.98/0.99  --prep_def_merge_mbd                    true
% 1.98/0.99  --prep_def_merge_tr_red                 false
% 1.98/0.99  --prep_def_merge_tr_cl                  false
% 1.98/0.99  --smt_preprocessing                     true
% 1.98/0.99  --smt_ac_axioms                         fast
% 1.98/0.99  --preprocessed_out                      false
% 1.98/0.99  --preprocessed_stats                    false
% 1.98/0.99  
% 1.98/0.99  ------ Abstraction refinement Options
% 1.98/0.99  
% 1.98/0.99  --abstr_ref                             []
% 1.98/0.99  --abstr_ref_prep                        false
% 1.98/0.99  --abstr_ref_until_sat                   false
% 1.98/0.99  --abstr_ref_sig_restrict                funpre
% 1.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.98/0.99  --abstr_ref_under                       []
% 1.98/0.99  
% 1.98/0.99  ------ SAT Options
% 1.98/0.99  
% 1.98/0.99  --sat_mode                              false
% 1.98/0.99  --sat_fm_restart_options                ""
% 1.98/0.99  --sat_gr_def                            false
% 1.98/0.99  --sat_epr_types                         true
% 1.98/0.99  --sat_non_cyclic_types                  false
% 1.98/0.99  --sat_finite_models                     false
% 1.98/0.99  --sat_fm_lemmas                         false
% 1.98/0.99  --sat_fm_prep                           false
% 1.98/0.99  --sat_fm_uc_incr                        true
% 1.98/0.99  --sat_out_model                         small
% 1.98/0.99  --sat_out_clauses                       false
% 1.98/0.99  
% 1.98/0.99  ------ QBF Options
% 1.98/0.99  
% 1.98/0.99  --qbf_mode                              false
% 1.98/0.99  --qbf_elim_univ                         false
% 1.98/0.99  --qbf_dom_inst                          none
% 1.98/0.99  --qbf_dom_pre_inst                      false
% 1.98/0.99  --qbf_sk_in                             false
% 1.98/0.99  --qbf_pred_elim                         true
% 1.98/0.99  --qbf_split                             512
% 1.98/0.99  
% 1.98/0.99  ------ BMC1 Options
% 1.98/0.99  
% 1.98/0.99  --bmc1_incremental                      false
% 1.98/0.99  --bmc1_axioms                           reachable_all
% 1.98/0.99  --bmc1_min_bound                        0
% 1.98/0.99  --bmc1_max_bound                        -1
% 1.98/0.99  --bmc1_max_bound_default                -1
% 1.98/0.99  --bmc1_symbol_reachability              true
% 1.98/0.99  --bmc1_property_lemmas                  false
% 1.98/0.99  --bmc1_k_induction                      false
% 1.98/0.99  --bmc1_non_equiv_states                 false
% 1.98/0.99  --bmc1_deadlock                         false
% 1.98/0.99  --bmc1_ucm                              false
% 1.98/0.99  --bmc1_add_unsat_core                   none
% 1.98/0.99  --bmc1_unsat_core_children              false
% 1.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.98/0.99  --bmc1_out_stat                         full
% 1.98/0.99  --bmc1_ground_init                      false
% 1.98/0.99  --bmc1_pre_inst_next_state              false
% 1.98/0.99  --bmc1_pre_inst_state                   false
% 1.98/0.99  --bmc1_pre_inst_reach_state             false
% 1.98/0.99  --bmc1_out_unsat_core                   false
% 1.98/0.99  --bmc1_aig_witness_out                  false
% 1.98/0.99  --bmc1_verbose                          false
% 1.98/0.99  --bmc1_dump_clauses_tptp                false
% 1.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.98/0.99  --bmc1_dump_file                        -
% 1.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.98/0.99  --bmc1_ucm_extend_mode                  1
% 1.98/0.99  --bmc1_ucm_init_mode                    2
% 1.98/0.99  --bmc1_ucm_cone_mode                    none
% 1.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.98/0.99  --bmc1_ucm_relax_model                  4
% 1.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.98/0.99  --bmc1_ucm_layered_model                none
% 1.98/0.99  --bmc1_ucm_max_lemma_size               10
% 1.98/0.99  
% 1.98/0.99  ------ AIG Options
% 1.98/0.99  
% 1.98/0.99  --aig_mode                              false
% 1.98/0.99  
% 1.98/0.99  ------ Instantiation Options
% 1.98/0.99  
% 1.98/0.99  --instantiation_flag                    true
% 1.98/0.99  --inst_sos_flag                         false
% 1.98/0.99  --inst_sos_phase                        true
% 1.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.98/0.99  --inst_lit_sel_side                     none
% 1.98/0.99  --inst_solver_per_active                1400
% 1.98/0.99  --inst_solver_calls_frac                1.
% 1.98/0.99  --inst_passive_queue_type               priority_queues
% 1.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.98/0.99  --inst_passive_queues_freq              [25;2]
% 1.98/0.99  --inst_dismatching                      true
% 1.98/0.99  --inst_eager_unprocessed_to_passive     true
% 1.98/0.99  --inst_prop_sim_given                   true
% 1.98/0.99  --inst_prop_sim_new                     false
% 1.98/0.99  --inst_subs_new                         false
% 1.98/0.99  --inst_eq_res_simp                      false
% 1.98/0.99  --inst_subs_given                       false
% 1.98/0.99  --inst_orphan_elimination               true
% 1.98/0.99  --inst_learning_loop_flag               true
% 1.98/0.99  --inst_learning_start                   3000
% 1.98/0.99  --inst_learning_factor                  2
% 1.98/0.99  --inst_start_prop_sim_after_learn       3
% 1.98/0.99  --inst_sel_renew                        solver
% 1.98/0.99  --inst_lit_activity_flag                true
% 1.98/0.99  --inst_restr_to_given                   false
% 1.98/0.99  --inst_activity_threshold               500
% 1.98/0.99  --inst_out_proof                        true
% 1.98/0.99  
% 1.98/0.99  ------ Resolution Options
% 1.98/0.99  
% 1.98/0.99  --resolution_flag                       false
% 1.98/0.99  --res_lit_sel                           adaptive
% 1.98/0.99  --res_lit_sel_side                      none
% 1.98/0.99  --res_ordering                          kbo
% 1.98/0.99  --res_to_prop_solver                    active
% 1.98/0.99  --res_prop_simpl_new                    false
% 1.98/0.99  --res_prop_simpl_given                  true
% 1.98/0.99  --res_passive_queue_type                priority_queues
% 1.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.98/0.99  --res_passive_queues_freq               [15;5]
% 1.98/0.99  --res_forward_subs                      full
% 1.98/0.99  --res_backward_subs                     full
% 1.98/0.99  --res_forward_subs_resolution           true
% 1.98/0.99  --res_backward_subs_resolution          true
% 1.98/0.99  --res_orphan_elimination                true
% 1.98/0.99  --res_time_limit                        2.
% 1.98/0.99  --res_out_proof                         true
% 1.98/0.99  
% 1.98/0.99  ------ Superposition Options
% 1.98/0.99  
% 1.98/0.99  --superposition_flag                    true
% 1.98/0.99  --sup_passive_queue_type                priority_queues
% 1.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.98/0.99  --demod_completeness_check              fast
% 1.98/0.99  --demod_use_ground                      true
% 1.98/0.99  --sup_to_prop_solver                    passive
% 1.98/0.99  --sup_prop_simpl_new                    true
% 1.98/0.99  --sup_prop_simpl_given                  true
% 1.98/0.99  --sup_fun_splitting                     false
% 1.98/0.99  --sup_smt_interval                      50000
% 1.98/0.99  
% 1.98/0.99  ------ Superposition Simplification Setup
% 1.98/0.99  
% 1.98/0.99  --sup_indices_passive                   []
% 1.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.99  --sup_full_bw                           [BwDemod]
% 1.98/0.99  --sup_immed_triv                        [TrivRules]
% 1.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.99  --sup_immed_bw_main                     []
% 1.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.99  
% 1.98/0.99  ------ Combination Options
% 1.98/0.99  
% 1.98/0.99  --comb_res_mult                         3
% 1.98/0.99  --comb_sup_mult                         2
% 1.98/0.99  --comb_inst_mult                        10
% 1.98/0.99  
% 1.98/0.99  ------ Debug Options
% 1.98/0.99  
% 1.98/0.99  --dbg_backtrace                         false
% 1.98/0.99  --dbg_dump_prop_clauses                 false
% 1.98/0.99  --dbg_dump_prop_clauses_file            -
% 1.98/0.99  --dbg_out_stat                          false
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  ------ Proving...
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  % SZS status Theorem for theBenchmark.p
% 1.98/0.99  
% 1.98/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.98/0.99  
% 1.98/0.99  fof(f16,axiom,(
% 1.98/0.99    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f21,plain,(
% 1.98/0.99    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.99    inference(ennf_transformation,[],[f16])).
% 1.98/0.99  
% 1.98/0.99  fof(f72,plain,(
% 1.98/0.99    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f21])).
% 1.98/0.99  
% 1.98/0.99  fof(f12,axiom,(
% 1.98/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f62,plain,(
% 1.98/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.98/0.99    inference(cnf_transformation,[],[f12])).
% 1.98/0.99  
% 1.98/0.99  fof(f4,axiom,(
% 1.98/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f51,plain,(
% 1.98/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f4])).
% 1.98/0.99  
% 1.98/0.99  fof(f5,axiom,(
% 1.98/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f52,plain,(
% 1.98/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f5])).
% 1.98/0.99  
% 1.98/0.99  fof(f6,axiom,(
% 1.98/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f53,plain,(
% 1.98/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f6])).
% 1.98/0.99  
% 1.98/0.99  fof(f7,axiom,(
% 1.98/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f54,plain,(
% 1.98/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f7])).
% 1.98/0.99  
% 1.98/0.99  fof(f8,axiom,(
% 1.98/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f55,plain,(
% 1.98/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f8])).
% 1.98/0.99  
% 1.98/0.99  fof(f9,axiom,(
% 1.98/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f56,plain,(
% 1.98/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f9])).
% 1.98/0.99  
% 1.98/0.99  fof(f76,plain,(
% 1.98/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.98/0.99    inference(definition_unfolding,[],[f55,f56])).
% 1.98/0.99  
% 1.98/0.99  fof(f77,plain,(
% 1.98/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.98/0.99    inference(definition_unfolding,[],[f54,f76])).
% 1.98/0.99  
% 1.98/0.99  fof(f78,plain,(
% 1.98/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.98/0.99    inference(definition_unfolding,[],[f53,f77])).
% 1.98/0.99  
% 1.98/0.99  fof(f79,plain,(
% 1.98/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.98/0.99    inference(definition_unfolding,[],[f52,f78])).
% 1.98/0.99  
% 1.98/0.99  fof(f80,plain,(
% 1.98/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.98/0.99    inference(definition_unfolding,[],[f51,f79])).
% 1.98/0.99  
% 1.98/0.99  fof(f81,plain,(
% 1.98/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.98/0.99    inference(definition_unfolding,[],[f62,f80])).
% 1.98/0.99  
% 1.98/0.99  fof(f84,plain,(
% 1.98/0.99    ( ! [X0] : (k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.98/0.99    inference(definition_unfolding,[],[f72,f81])).
% 1.98/0.99  
% 1.98/0.99  fof(f17,conjecture,(
% 1.98/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f18,negated_conjecture,(
% 1.98/0.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.98/0.99    inference(negated_conjecture,[],[f17])).
% 1.98/0.99  
% 1.98/0.99  fof(f22,plain,(
% 1.98/0.99    ? [X0,X1,X2] : (((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 1.98/0.99    inference(ennf_transformation,[],[f18])).
% 1.98/0.99  
% 1.98/0.99  fof(f23,plain,(
% 1.98/0.99    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2))),
% 1.98/0.99    inference(flattening,[],[f22])).
% 1.98/0.99  
% 1.98/0.99  fof(f44,plain,(
% 1.98/0.99    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2)) => ((~r2_hidden(sK9,k3_relat_1(sK10)) | ~r2_hidden(sK8,k3_relat_1(sK10))) & r2_hidden(k4_tarski(sK8,sK9),sK10) & v1_relat_1(sK10))),
% 1.98/0.99    introduced(choice_axiom,[])).
% 1.98/0.99  
% 1.98/0.99  fof(f45,plain,(
% 1.98/0.99    (~r2_hidden(sK9,k3_relat_1(sK10)) | ~r2_hidden(sK8,k3_relat_1(sK10))) & r2_hidden(k4_tarski(sK8,sK9),sK10) & v1_relat_1(sK10)),
% 1.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f23,f44])).
% 1.98/0.99  
% 1.98/0.99  fof(f73,plain,(
% 1.98/0.99    v1_relat_1(sK10)),
% 1.98/0.99    inference(cnf_transformation,[],[f45])).
% 1.98/0.99  
% 1.98/0.99  fof(f3,axiom,(
% 1.98/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f50,plain,(
% 1.98/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f3])).
% 1.98/0.99  
% 1.98/0.99  fof(f83,plain,(
% 1.98/0.99    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.98/0.99    inference(definition_unfolding,[],[f50,f80,f80])).
% 1.98/0.99  
% 1.98/0.99  fof(f2,axiom,(
% 1.98/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f49,plain,(
% 1.98/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.98/0.99    inference(cnf_transformation,[],[f2])).
% 1.98/0.99  
% 1.98/0.99  fof(f82,plain,(
% 1.98/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.98/0.99    inference(definition_unfolding,[],[f49,f81])).
% 1.98/0.99  
% 1.98/0.99  fof(f74,plain,(
% 1.98/0.99    r2_hidden(k4_tarski(sK8,sK9),sK10)),
% 1.98/0.99    inference(cnf_transformation,[],[f45])).
% 1.98/0.99  
% 1.98/0.99  fof(f15,axiom,(
% 1.98/0.99    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f38,plain,(
% 1.98/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.98/0.99    inference(nnf_transformation,[],[f15])).
% 1.98/0.99  
% 1.98/0.99  fof(f39,plain,(
% 1.98/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.98/0.99    inference(rectify,[],[f38])).
% 1.98/0.99  
% 1.98/0.99  fof(f42,plain,(
% 1.98/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 1.98/0.99    introduced(choice_axiom,[])).
% 1.98/0.99  
% 1.98/0.99  fof(f41,plain,(
% 1.98/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0))) )),
% 1.98/0.99    introduced(choice_axiom,[])).
% 1.98/0.99  
% 1.98/0.99  fof(f40,plain,(
% 1.98/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 1.98/0.99    introduced(choice_axiom,[])).
% 1.98/0.99  
% 1.98/0.99  fof(f43,plain,(
% 1.98/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f39,f42,f41,f40])).
% 1.98/0.99  
% 1.98/0.99  fof(f69,plain,(
% 1.98/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.98/0.99    inference(cnf_transformation,[],[f43])).
% 1.98/0.99  
% 1.98/0.99  fof(f89,plain,(
% 1.98/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 1.98/0.99    inference(equality_resolution,[],[f69])).
% 1.98/0.99  
% 1.98/0.99  fof(f1,axiom,(
% 1.98/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f19,plain,(
% 1.98/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.98/0.99    inference(ennf_transformation,[],[f1])).
% 1.98/0.99  
% 1.98/0.99  fof(f24,plain,(
% 1.98/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.98/0.99    inference(nnf_transformation,[],[f19])).
% 1.98/0.99  
% 1.98/0.99  fof(f25,plain,(
% 1.98/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.98/0.99    inference(rectify,[],[f24])).
% 1.98/0.99  
% 1.98/0.99  fof(f26,plain,(
% 1.98/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.98/0.99    introduced(choice_axiom,[])).
% 1.98/0.99  
% 1.98/0.99  fof(f27,plain,(
% 1.98/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.98/0.99  
% 1.98/0.99  fof(f46,plain,(
% 1.98/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f27])).
% 1.98/0.99  
% 1.98/0.99  fof(f14,axiom,(
% 1.98/0.99    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f32,plain,(
% 1.98/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.98/0.99    inference(nnf_transformation,[],[f14])).
% 1.98/0.99  
% 1.98/0.99  fof(f33,plain,(
% 1.98/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.98/0.99    inference(rectify,[],[f32])).
% 1.98/0.99  
% 1.98/0.99  fof(f36,plain,(
% 1.98/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 1.98/0.99    introduced(choice_axiom,[])).
% 1.98/0.99  
% 1.98/0.99  fof(f35,plain,(
% 1.98/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 1.98/0.99    introduced(choice_axiom,[])).
% 1.98/0.99  
% 1.98/0.99  fof(f34,plain,(
% 1.98/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.98/0.99    introduced(choice_axiom,[])).
% 1.98/0.99  
% 1.98/0.99  fof(f37,plain,(
% 1.98/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).
% 1.98/0.99  
% 1.98/0.99  fof(f65,plain,(
% 1.98/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.98/0.99    inference(cnf_transformation,[],[f37])).
% 1.98/0.99  
% 1.98/0.99  fof(f87,plain,(
% 1.98/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 1.98/0.99    inference(equality_resolution,[],[f65])).
% 1.98/0.99  
% 1.98/0.99  fof(f75,plain,(
% 1.98/0.99    ~r2_hidden(sK9,k3_relat_1(sK10)) | ~r2_hidden(sK8,k3_relat_1(sK10))),
% 1.98/0.99    inference(cnf_transformation,[],[f45])).
% 1.98/0.99  
% 1.98/0.99  cnf(c_19,plain,
% 1.98/0.99      ( ~ v1_relat_1(X0)
% 1.98/0.99      | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 1.98/0.99      inference(cnf_transformation,[],[f84]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_22,negated_conjecture,
% 1.98/0.99      ( v1_relat_1(sK10) ),
% 1.98/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_296,plain,
% 1.98/0.99      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 1.98/0.99      | sK10 != X0 ),
% 1.98/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_297,plain,
% 1.98/0.99      ( k3_tarski(k6_enumset1(k1_relat_1(sK10),k1_relat_1(sK10),k1_relat_1(sK10),k1_relat_1(sK10),k1_relat_1(sK10),k1_relat_1(sK10),k1_relat_1(sK10),k2_relat_1(sK10))) = k3_relat_1(sK10) ),
% 1.98/0.99      inference(unflattening,[status(thm)],[c_296]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_4,plain,
% 1.98/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 1.98/0.99      inference(cnf_transformation,[],[f83]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_3,plain,
% 1.98/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 1.98/0.99      inference(cnf_transformation,[],[f82]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1463,plain,
% 1.98/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2322,plain,
% 1.98/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_4,c_1463]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2700,plain,
% 1.98/0.99      ( r1_tarski(k2_relat_1(sK10),k3_relat_1(sK10)) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_297,c_2322]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_21,negated_conjecture,
% 1.98/0.99      ( r2_hidden(k4_tarski(sK8,sK9),sK10) ),
% 1.98/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1448,plain,
% 1.98/0.99      ( r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_17,plain,
% 1.98/0.99      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 1.98/0.99      inference(cnf_transformation,[],[f89]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1451,plain,
% 1.98/0.99      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 1.98/0.99      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2859,plain,
% 1.98/0.99      ( r2_hidden(sK9,k2_relat_1(sK10)) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1448,c_1451]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2,plain,
% 1.98/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.98/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1464,plain,
% 1.98/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.98/0.99      | r2_hidden(X0,X2) = iProver_top
% 1.98/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_3343,plain,
% 1.98/0.99      ( r2_hidden(sK9,X0) = iProver_top
% 1.98/0.99      | r1_tarski(k2_relat_1(sK10),X0) != iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_2859,c_1464]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_3650,plain,
% 1.98/0.99      ( r2_hidden(sK9,k3_relat_1(sK10)) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_2700,c_3343]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1666,plain,
% 1.98/0.99      ( r2_hidden(sK8,X0)
% 1.98/0.99      | ~ r2_hidden(sK8,k1_relat_1(sK10))
% 1.98/0.99      | ~ r1_tarski(k1_relat_1(sK10),X0) ),
% 1.98/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2731,plain,
% 1.98/0.99      ( r2_hidden(sK8,k3_relat_1(sK10))
% 1.98/0.99      | ~ r2_hidden(sK8,k1_relat_1(sK10))
% 1.98/0.99      | ~ r1_tarski(k1_relat_1(sK10),k3_relat_1(sK10)) ),
% 1.98/0.99      inference(instantiation,[status(thm)],[c_1666]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2732,plain,
% 1.98/0.99      ( r2_hidden(sK8,k3_relat_1(sK10)) = iProver_top
% 1.98/0.99      | r2_hidden(sK8,k1_relat_1(sK10)) != iProver_top
% 1.98/0.99      | r1_tarski(k1_relat_1(sK10),k3_relat_1(sK10)) != iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2731]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2321,plain,
% 1.98/0.99      ( r1_tarski(k1_relat_1(sK10),k3_relat_1(sK10)) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_297,c_1463]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_13,plain,
% 1.98/0.99      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 1.98/0.99      inference(cnf_transformation,[],[f87]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1617,plain,
% 1.98/0.99      ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
% 1.98/0.99      | r2_hidden(sK8,k1_relat_1(sK10)) ),
% 1.98/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1618,plain,
% 1.98/0.99      ( r2_hidden(k4_tarski(sK8,sK9),sK10) != iProver_top
% 1.98/0.99      | r2_hidden(sK8,k1_relat_1(sK10)) = iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1617]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_20,negated_conjecture,
% 1.98/0.99      ( ~ r2_hidden(sK8,k3_relat_1(sK10))
% 1.98/0.99      | ~ r2_hidden(sK9,k3_relat_1(sK10)) ),
% 1.98/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_25,plain,
% 1.98/0.99      ( r2_hidden(sK8,k3_relat_1(sK10)) != iProver_top
% 1.98/0.99      | r2_hidden(sK9,k3_relat_1(sK10)) != iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_24,plain,
% 1.98/0.99      ( r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(contradiction,plain,
% 1.98/0.99      ( $false ),
% 1.98/0.99      inference(minisat,
% 1.98/0.99                [status(thm)],
% 1.98/0.99                [c_3650,c_2732,c_2321,c_1618,c_25,c_24]) ).
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.98/0.99  
% 1.98/0.99  ------                               Statistics
% 1.98/0.99  
% 1.98/0.99  ------ General
% 1.98/0.99  
% 1.98/0.99  abstr_ref_over_cycles:                  0
% 1.98/0.99  abstr_ref_under_cycles:                 0
% 1.98/0.99  gc_basic_clause_elim:                   0
% 1.98/0.99  forced_gc_time:                         0
% 1.98/0.99  parsing_time:                           0.022
% 1.98/0.99  unif_index_cands_time:                  0.
% 1.98/0.99  unif_index_add_time:                    0.
% 1.98/0.99  orderings_time:                         0.
% 1.98/0.99  out_proof_time:                         0.007
% 1.98/0.99  total_time:                             0.165
% 1.98/0.99  num_of_symbols:                         52
% 1.98/0.99  num_of_terms:                           3785
% 1.98/0.99  
% 1.98/0.99  ------ Preprocessing
% 1.98/0.99  
% 1.98/0.99  num_of_splits:                          0
% 1.98/0.99  num_of_split_atoms:                     0
% 1.98/0.99  num_of_reused_defs:                     0
% 1.98/0.99  num_eq_ax_congr_red:                    53
% 1.98/0.99  num_of_sem_filtered_clauses:            1
% 1.98/0.99  num_of_subtypes:                        0
% 1.98/0.99  monotx_restored_types:                  0
% 1.98/0.99  sat_num_of_epr_types:                   0
% 1.98/0.99  sat_num_of_non_cyclic_types:            0
% 1.98/0.99  sat_guarded_non_collapsed_types:        0
% 1.98/0.99  num_pure_diseq_elim:                    0
% 1.98/0.99  simp_replaced_by:                       0
% 1.98/0.99  res_preprocessed:                       110
% 1.98/0.99  prep_upred:                             0
% 1.98/0.99  prep_unflattend:                        55
% 1.98/0.99  smt_new_axioms:                         0
% 1.98/0.99  pred_elim_cands:                        2
% 1.98/0.99  pred_elim:                              1
% 1.98/0.99  pred_elim_cl:                           1
% 1.98/0.99  pred_elim_cycles:                       3
% 1.98/0.99  merged_defs:                            8
% 1.98/0.99  merged_defs_ncl:                        0
% 1.98/0.99  bin_hyper_res:                          8
% 1.98/0.99  prep_cycles:                            4
% 1.98/0.99  pred_elim_time:                         0.007
% 1.98/0.99  splitting_time:                         0.
% 1.98/0.99  sem_filter_time:                        0.
% 1.98/0.99  monotx_time:                            0.
% 1.98/0.99  subtype_inf_time:                       0.
% 1.98/0.99  
% 1.98/0.99  ------ Problem properties
% 1.98/0.99  
% 1.98/0.99  clauses:                                22
% 1.98/0.99  conjectures:                            2
% 1.98/0.99  epr:                                    1
% 1.98/0.99  horn:                                   18
% 1.98/0.99  ground:                                 3
% 1.98/0.99  unary:                                  5
% 1.98/0.99  binary:                                 10
% 1.98/0.99  lits:                                   46
% 1.98/0.99  lits_eq:                                9
% 1.98/0.99  fd_pure:                                0
% 1.98/0.99  fd_pseudo:                              0
% 1.98/0.99  fd_cond:                                0
% 1.98/0.99  fd_pseudo_cond:                         6
% 1.98/0.99  ac_symbols:                             0
% 1.98/0.99  
% 1.98/0.99  ------ Propositional Solver
% 1.98/0.99  
% 1.98/0.99  prop_solver_calls:                      26
% 1.98/0.99  prop_fast_solver_calls:                 639
% 1.98/0.99  smt_solver_calls:                       0
% 1.98/0.99  smt_fast_solver_calls:                  0
% 1.98/0.99  prop_num_of_clauses:                    1272
% 1.98/0.99  prop_preprocess_simplified:             5344
% 1.98/0.99  prop_fo_subsumed:                       0
% 1.98/0.99  prop_solver_time:                       0.
% 1.98/0.99  smt_solver_time:                        0.
% 1.98/0.99  smt_fast_solver_time:                   0.
% 1.98/0.99  prop_fast_solver_time:                  0.
% 1.98/0.99  prop_unsat_core_time:                   0.
% 1.98/0.99  
% 1.98/0.99  ------ QBF
% 1.98/0.99  
% 1.98/0.99  qbf_q_res:                              0
% 1.98/0.99  qbf_num_tautologies:                    0
% 1.98/0.99  qbf_prep_cycles:                        0
% 1.98/0.99  
% 1.98/0.99  ------ BMC1
% 1.98/0.99  
% 1.98/0.99  bmc1_current_bound:                     -1
% 1.98/0.99  bmc1_last_solved_bound:                 -1
% 1.98/0.99  bmc1_unsat_core_size:                   -1
% 1.98/0.99  bmc1_unsat_core_parents_size:           -1
% 1.98/0.99  bmc1_merge_next_fun:                    0
% 1.98/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.98/0.99  
% 1.98/0.99  ------ Instantiation
% 1.98/0.99  
% 1.98/0.99  inst_num_of_clauses:                    336
% 1.98/0.99  inst_num_in_passive:                    204
% 1.98/0.99  inst_num_in_active:                     117
% 1.98/0.99  inst_num_in_unprocessed:                15
% 1.98/0.99  inst_num_of_loops:                      150
% 1.98/0.99  inst_num_of_learning_restarts:          0
% 1.98/0.99  inst_num_moves_active_passive:          32
% 1.98/0.99  inst_lit_activity:                      0
% 1.98/0.99  inst_lit_activity_moves:                0
% 1.98/0.99  inst_num_tautologies:                   0
% 1.98/0.99  inst_num_prop_implied:                  0
% 1.98/0.99  inst_num_existing_simplified:           0
% 1.98/0.99  inst_num_eq_res_simplified:             0
% 1.98/0.99  inst_num_child_elim:                    0
% 1.98/0.99  inst_num_of_dismatching_blockings:      46
% 1.98/0.99  inst_num_of_non_proper_insts:           173
% 1.98/0.99  inst_num_of_duplicates:                 0
% 1.98/0.99  inst_inst_num_from_inst_to_res:         0
% 1.98/0.99  inst_dismatching_checking_time:         0.
% 1.98/0.99  
% 1.98/0.99  ------ Resolution
% 1.98/0.99  
% 1.98/0.99  res_num_of_clauses:                     0
% 1.98/0.99  res_num_in_passive:                     0
% 1.98/0.99  res_num_in_active:                      0
% 1.98/0.99  res_num_of_loops:                       114
% 1.98/0.99  res_forward_subset_subsumed:            2
% 1.98/0.99  res_backward_subset_subsumed:           0
% 1.98/0.99  res_forward_subsumed:                   0
% 1.98/0.99  res_backward_subsumed:                  0
% 1.98/0.99  res_forward_subsumption_resolution:     0
% 1.98/0.99  res_backward_subsumption_resolution:    0
% 1.98/0.99  res_clause_to_clause_subsumption:       130
% 1.98/0.99  res_orphan_elimination:                 0
% 1.98/0.99  res_tautology_del:                      23
% 1.98/0.99  res_num_eq_res_simplified:              0
% 1.98/0.99  res_num_sel_changes:                    0
% 1.98/0.99  res_moves_from_active_to_pass:          0
% 1.98/0.99  
% 1.98/0.99  ------ Superposition
% 1.98/0.99  
% 1.98/0.99  sup_time_total:                         0.
% 1.98/0.99  sup_time_generating:                    0.
% 1.98/0.99  sup_time_sim_full:                      0.
% 1.98/0.99  sup_time_sim_immed:                     0.
% 1.98/0.99  
% 1.98/0.99  sup_num_of_clauses:                     65
% 1.98/0.99  sup_num_in_active:                      29
% 1.98/0.99  sup_num_in_passive:                     36
% 1.98/0.99  sup_num_of_loops:                       28
% 1.98/0.99  sup_fw_superposition:                   28
% 1.98/0.99  sup_bw_superposition:                   22
% 1.98/0.99  sup_immediate_simplified:               0
% 1.98/0.99  sup_given_eliminated:                   0
% 1.98/0.99  comparisons_done:                       0
% 1.98/0.99  comparisons_avoided:                    0
% 1.98/0.99  
% 1.98/0.99  ------ Simplifications
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  sim_fw_subset_subsumed:                 0
% 1.98/0.99  sim_bw_subset_subsumed:                 0
% 1.98/0.99  sim_fw_subsumed:                        0
% 1.98/0.99  sim_bw_subsumed:                        0
% 1.98/0.99  sim_fw_subsumption_res:                 0
% 1.98/0.99  sim_bw_subsumption_res:                 0
% 1.98/0.99  sim_tautology_del:                      3
% 1.98/0.99  sim_eq_tautology_del:                   0
% 1.98/0.99  sim_eq_res_simp:                        0
% 1.98/0.99  sim_fw_demodulated:                     0
% 1.98/0.99  sim_bw_demodulated:                     0
% 1.98/0.99  sim_light_normalised:                   0
% 1.98/0.99  sim_joinable_taut:                      0
% 1.98/0.99  sim_joinable_simp:                      0
% 1.98/0.99  sim_ac_normalised:                      0
% 1.98/0.99  sim_smt_subsumption:                    0
% 1.98/0.99  
%------------------------------------------------------------------------------
