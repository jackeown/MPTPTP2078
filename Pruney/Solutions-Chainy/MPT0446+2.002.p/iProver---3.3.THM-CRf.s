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
% DateTime   : Thu Dec  3 11:43:07 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 222 expanded)
%              Number of clauses        :   24 (  31 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  238 ( 470 expanded)
%              Number of equality atoms :   52 ( 155 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f77])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f81])).

fof(f85,plain,(
    ! [X0] :
      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f73,f82])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k3_relat_1(X2))
          | ~ r2_hidden(X0,k3_relat_1(X2)) )
        & r2_hidden(k4_tarski(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK8,k3_relat_1(sK9))
        | ~ r2_hidden(sK7,k3_relat_1(sK9)) )
      & r2_hidden(k4_tarski(sK7,sK8),sK9)
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ r2_hidden(sK8,k3_relat_1(sK9))
      | ~ r2_hidden(sK7,k3_relat_1(sK9)) )
    & r2_hidden(k4_tarski(sK7,sK8),sK9)
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f27,f45])).

fof(f74,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f84,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f51,f81,f81])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f82])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).

fof(f70,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f76,plain,
    ( ~ r2_hidden(sK8,k3_relat_1(sK9))
    | ~ r2_hidden(sK7,k3_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    r2_hidden(k4_tarski(sK7,sK8),sK9) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1169,plain,
    ( r2_hidden(sK8,X0)
    | ~ r2_hidden(sK8,k2_relat_1(sK9))
    | ~ r1_tarski(k2_relat_1(sK9),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2875,plain,
    ( r2_hidden(sK8,k3_relat_1(sK9))
    | ~ r2_hidden(sK8,k2_relat_1(sK9))
    | ~ r1_tarski(k2_relat_1(sK9),k3_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_297,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_298,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k2_relat_1(sK9))) = k3_relat_1(sK9) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_4,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_965,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1798,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_965])).

cnf(c_2097,plain,
    ( r1_tarski(k2_relat_1(sK9),k3_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_298,c_1798])).

cnf(c_2102,plain,
    ( r1_tarski(k2_relat_1(sK9),k3_relat_1(sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2097])).

cnf(c_1153,plain,
    ( r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,k1_relat_1(sK9))
    | ~ r1_tarski(k1_relat_1(sK9),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1922,plain,
    ( r2_hidden(sK7,k3_relat_1(sK9))
    | ~ r2_hidden(sK7,k1_relat_1(sK9))
    | ~ r1_tarski(k1_relat_1(sK9),k3_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_1797,plain,
    ( r1_tarski(k1_relat_1(sK9),k3_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_298,c_965])).

cnf(c_1804,plain,
    ( r1_tarski(k1_relat_1(sK9),k3_relat_1(sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1797])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1100,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK8),sK9)
    | r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1087,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK8),sK9)
    | r2_hidden(sK7,k1_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(sK7,k3_relat_1(sK9))
    | ~ r2_hidden(sK8,k3_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(k4_tarski(sK7,sK8),sK9) ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2875,c_2102,c_1922,c_1804,c_1100,c_1087,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:49:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.89/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/0.99  
% 1.89/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.89/0.99  
% 1.89/0.99  ------  iProver source info
% 1.89/0.99  
% 1.89/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.89/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.89/0.99  git: non_committed_changes: false
% 1.89/0.99  git: last_make_outside_of_git: false
% 1.89/0.99  
% 1.89/0.99  ------ 
% 1.89/0.99  
% 1.89/0.99  ------ Input Options
% 1.89/0.99  
% 1.89/0.99  --out_options                           all
% 1.89/0.99  --tptp_safe_out                         true
% 1.89/0.99  --problem_path                          ""
% 1.89/0.99  --include_path                          ""
% 1.89/0.99  --clausifier                            res/vclausify_rel
% 1.89/0.99  --clausifier_options                    --mode clausify
% 1.89/0.99  --stdin                                 false
% 1.89/0.99  --stats_out                             all
% 1.89/0.99  
% 1.89/0.99  ------ General Options
% 1.89/0.99  
% 1.89/0.99  --fof                                   false
% 1.89/0.99  --time_out_real                         305.
% 1.89/0.99  --time_out_virtual                      -1.
% 1.89/0.99  --symbol_type_check                     false
% 1.89/0.99  --clausify_out                          false
% 1.89/0.99  --sig_cnt_out                           false
% 1.89/0.99  --trig_cnt_out                          false
% 1.89/0.99  --trig_cnt_out_tolerance                1.
% 1.89/0.99  --trig_cnt_out_sk_spl                   false
% 1.89/0.99  --abstr_cl_out                          false
% 1.89/0.99  
% 1.89/0.99  ------ Global Options
% 1.89/0.99  
% 1.89/0.99  --schedule                              default
% 1.89/0.99  --add_important_lit                     false
% 1.89/0.99  --prop_solver_per_cl                    1000
% 1.89/0.99  --min_unsat_core                        false
% 1.89/0.99  --soft_assumptions                      false
% 1.89/0.99  --soft_lemma_size                       3
% 1.89/0.99  --prop_impl_unit_size                   0
% 1.89/0.99  --prop_impl_unit                        []
% 1.89/0.99  --share_sel_clauses                     true
% 1.89/0.99  --reset_solvers                         false
% 1.89/0.99  --bc_imp_inh                            [conj_cone]
% 1.89/0.99  --conj_cone_tolerance                   3.
% 1.89/0.99  --extra_neg_conj                        none
% 1.89/0.99  --large_theory_mode                     true
% 1.89/0.99  --prolific_symb_bound                   200
% 1.89/0.99  --lt_threshold                          2000
% 1.89/0.99  --clause_weak_htbl                      true
% 1.89/0.99  --gc_record_bc_elim                     false
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing Options
% 1.89/0.99  
% 1.89/0.99  --preprocessing_flag                    true
% 1.89/0.99  --time_out_prep_mult                    0.1
% 1.89/0.99  --splitting_mode                        input
% 1.89/0.99  --splitting_grd                         true
% 1.89/0.99  --splitting_cvd                         false
% 1.89/0.99  --splitting_cvd_svl                     false
% 1.89/0.99  --splitting_nvd                         32
% 1.89/0.99  --sub_typing                            true
% 1.89/0.99  --prep_gs_sim                           true
% 1.89/0.99  --prep_unflatten                        true
% 1.89/0.99  --prep_res_sim                          true
% 1.89/0.99  --prep_upred                            true
% 1.89/0.99  --prep_sem_filter                       exhaustive
% 1.89/0.99  --prep_sem_filter_out                   false
% 1.89/0.99  --pred_elim                             true
% 1.89/0.99  --res_sim_input                         true
% 1.89/0.99  --eq_ax_congr_red                       true
% 1.89/0.99  --pure_diseq_elim                       true
% 1.89/0.99  --brand_transform                       false
% 1.89/0.99  --non_eq_to_eq                          false
% 1.89/0.99  --prep_def_merge                        true
% 1.89/0.99  --prep_def_merge_prop_impl              false
% 1.89/0.99  --prep_def_merge_mbd                    true
% 1.89/0.99  --prep_def_merge_tr_red                 false
% 1.89/0.99  --prep_def_merge_tr_cl                  false
% 1.89/0.99  --smt_preprocessing                     true
% 1.89/0.99  --smt_ac_axioms                         fast
% 1.89/0.99  --preprocessed_out                      false
% 1.89/0.99  --preprocessed_stats                    false
% 1.89/0.99  
% 1.89/0.99  ------ Abstraction refinement Options
% 1.89/0.99  
% 1.89/0.99  --abstr_ref                             []
% 1.89/0.99  --abstr_ref_prep                        false
% 1.89/0.99  --abstr_ref_until_sat                   false
% 1.89/0.99  --abstr_ref_sig_restrict                funpre
% 1.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/0.99  --abstr_ref_under                       []
% 1.89/0.99  
% 1.89/0.99  ------ SAT Options
% 1.89/0.99  
% 1.89/0.99  --sat_mode                              false
% 1.89/0.99  --sat_fm_restart_options                ""
% 1.89/0.99  --sat_gr_def                            false
% 1.89/0.99  --sat_epr_types                         true
% 1.89/0.99  --sat_non_cyclic_types                  false
% 1.89/0.99  --sat_finite_models                     false
% 1.89/0.99  --sat_fm_lemmas                         false
% 1.89/0.99  --sat_fm_prep                           false
% 1.89/0.99  --sat_fm_uc_incr                        true
% 1.89/0.99  --sat_out_model                         small
% 1.89/0.99  --sat_out_clauses                       false
% 1.89/0.99  
% 1.89/0.99  ------ QBF Options
% 1.89/0.99  
% 1.89/0.99  --qbf_mode                              false
% 1.89/0.99  --qbf_elim_univ                         false
% 1.89/0.99  --qbf_dom_inst                          none
% 1.89/0.99  --qbf_dom_pre_inst                      false
% 1.89/0.99  --qbf_sk_in                             false
% 1.89/0.99  --qbf_pred_elim                         true
% 1.89/0.99  --qbf_split                             512
% 1.89/0.99  
% 1.89/0.99  ------ BMC1 Options
% 1.89/0.99  
% 1.89/0.99  --bmc1_incremental                      false
% 1.89/0.99  --bmc1_axioms                           reachable_all
% 1.89/0.99  --bmc1_min_bound                        0
% 1.89/0.99  --bmc1_max_bound                        -1
% 1.89/0.99  --bmc1_max_bound_default                -1
% 1.89/0.99  --bmc1_symbol_reachability              true
% 1.89/0.99  --bmc1_property_lemmas                  false
% 1.89/0.99  --bmc1_k_induction                      false
% 1.89/0.99  --bmc1_non_equiv_states                 false
% 1.89/0.99  --bmc1_deadlock                         false
% 1.89/0.99  --bmc1_ucm                              false
% 1.89/0.99  --bmc1_add_unsat_core                   none
% 1.89/0.99  --bmc1_unsat_core_children              false
% 1.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/0.99  --bmc1_out_stat                         full
% 1.89/0.99  --bmc1_ground_init                      false
% 1.89/0.99  --bmc1_pre_inst_next_state              false
% 1.89/0.99  --bmc1_pre_inst_state                   false
% 1.89/0.99  --bmc1_pre_inst_reach_state             false
% 1.89/0.99  --bmc1_out_unsat_core                   false
% 1.89/0.99  --bmc1_aig_witness_out                  false
% 1.89/0.99  --bmc1_verbose                          false
% 1.89/0.99  --bmc1_dump_clauses_tptp                false
% 1.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.89/0.99  --bmc1_dump_file                        -
% 1.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.89/0.99  --bmc1_ucm_extend_mode                  1
% 1.89/0.99  --bmc1_ucm_init_mode                    2
% 1.89/0.99  --bmc1_ucm_cone_mode                    none
% 1.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.89/0.99  --bmc1_ucm_relax_model                  4
% 1.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/0.99  --bmc1_ucm_layered_model                none
% 1.89/0.99  --bmc1_ucm_max_lemma_size               10
% 1.89/0.99  
% 1.89/0.99  ------ AIG Options
% 1.89/0.99  
% 1.89/0.99  --aig_mode                              false
% 1.89/0.99  
% 1.89/0.99  ------ Instantiation Options
% 1.89/0.99  
% 1.89/0.99  --instantiation_flag                    true
% 1.89/0.99  --inst_sos_flag                         false
% 1.89/0.99  --inst_sos_phase                        true
% 1.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel_side                     num_symb
% 1.89/0.99  --inst_solver_per_active                1400
% 1.89/0.99  --inst_solver_calls_frac                1.
% 1.89/0.99  --inst_passive_queue_type               priority_queues
% 1.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/0.99  --inst_passive_queues_freq              [25;2]
% 1.89/0.99  --inst_dismatching                      true
% 1.89/0.99  --inst_eager_unprocessed_to_passive     true
% 1.89/0.99  --inst_prop_sim_given                   true
% 1.89/0.99  --inst_prop_sim_new                     false
% 1.89/0.99  --inst_subs_new                         false
% 1.89/0.99  --inst_eq_res_simp                      false
% 1.89/0.99  --inst_subs_given                       false
% 1.89/0.99  --inst_orphan_elimination               true
% 1.89/0.99  --inst_learning_loop_flag               true
% 1.89/0.99  --inst_learning_start                   3000
% 1.89/0.99  --inst_learning_factor                  2
% 1.89/0.99  --inst_start_prop_sim_after_learn       3
% 1.89/0.99  --inst_sel_renew                        solver
% 1.89/0.99  --inst_lit_activity_flag                true
% 1.89/0.99  --inst_restr_to_given                   false
% 1.89/0.99  --inst_activity_threshold               500
% 1.89/0.99  --inst_out_proof                        true
% 1.89/0.99  
% 1.89/0.99  ------ Resolution Options
% 1.89/0.99  
% 1.89/0.99  --resolution_flag                       true
% 1.89/0.99  --res_lit_sel                           adaptive
% 1.89/0.99  --res_lit_sel_side                      none
% 1.89/0.99  --res_ordering                          kbo
% 1.89/0.99  --res_to_prop_solver                    active
% 1.89/0.99  --res_prop_simpl_new                    false
% 1.89/0.99  --res_prop_simpl_given                  true
% 1.89/0.99  --res_passive_queue_type                priority_queues
% 1.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/0.99  --res_passive_queues_freq               [15;5]
% 1.89/0.99  --res_forward_subs                      full
% 1.89/0.99  --res_backward_subs                     full
% 1.89/0.99  --res_forward_subs_resolution           true
% 1.89/0.99  --res_backward_subs_resolution          true
% 1.89/0.99  --res_orphan_elimination                true
% 1.89/0.99  --res_time_limit                        2.
% 1.89/0.99  --res_out_proof                         true
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Options
% 1.89/0.99  
% 1.89/0.99  --superposition_flag                    true
% 1.89/0.99  --sup_passive_queue_type                priority_queues
% 1.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.89/0.99  --demod_completeness_check              fast
% 1.89/0.99  --demod_use_ground                      true
% 1.89/0.99  --sup_to_prop_solver                    passive
% 1.89/0.99  --sup_prop_simpl_new                    true
% 1.89/0.99  --sup_prop_simpl_given                  true
% 1.89/0.99  --sup_fun_splitting                     false
% 1.89/0.99  --sup_smt_interval                      50000
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Simplification Setup
% 1.89/0.99  
% 1.89/0.99  --sup_indices_passive                   []
% 1.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_full_bw                           [BwDemod]
% 1.89/0.99  --sup_immed_triv                        [TrivRules]
% 1.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_immed_bw_main                     []
% 1.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  
% 1.89/0.99  ------ Combination Options
% 1.89/0.99  
% 1.89/0.99  --comb_res_mult                         3
% 1.89/0.99  --comb_sup_mult                         2
% 1.89/0.99  --comb_inst_mult                        10
% 1.89/0.99  
% 1.89/0.99  ------ Debug Options
% 1.89/0.99  
% 1.89/0.99  --dbg_backtrace                         false
% 1.89/0.99  --dbg_dump_prop_clauses                 false
% 1.89/0.99  --dbg_dump_prop_clauses_file            -
% 1.89/0.99  --dbg_out_stat                          false
% 1.89/0.99  ------ Parsing...
% 1.89/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.89/0.99  ------ Proving...
% 1.89/0.99  ------ Problem Properties 
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  clauses                                 19
% 1.89/0.99  conjectures                             2
% 1.89/0.99  EPR                                     1
% 1.89/0.99  Horn                                    16
% 1.89/0.99  unary                                   5
% 1.89/0.99  binary                                  9
% 1.89/0.99  lits                                    38
% 1.89/0.99  lits eq                                 7
% 1.89/0.99  fd_pure                                 0
% 1.89/0.99  fd_pseudo                               0
% 1.89/0.99  fd_cond                                 0
% 1.89/0.99  fd_pseudo_cond                          4
% 1.89/0.99  AC symbols                              0
% 1.89/0.99  
% 1.89/0.99  ------ Schedule dynamic 5 is on 
% 1.89/0.99  
% 1.89/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  ------ 
% 1.89/0.99  Current options:
% 1.89/0.99  ------ 
% 1.89/0.99  
% 1.89/0.99  ------ Input Options
% 1.89/0.99  
% 1.89/0.99  --out_options                           all
% 1.89/0.99  --tptp_safe_out                         true
% 1.89/0.99  --problem_path                          ""
% 1.89/0.99  --include_path                          ""
% 1.89/0.99  --clausifier                            res/vclausify_rel
% 1.89/0.99  --clausifier_options                    --mode clausify
% 1.89/0.99  --stdin                                 false
% 1.89/0.99  --stats_out                             all
% 1.89/0.99  
% 1.89/0.99  ------ General Options
% 1.89/0.99  
% 1.89/0.99  --fof                                   false
% 1.89/0.99  --time_out_real                         305.
% 1.89/0.99  --time_out_virtual                      -1.
% 1.89/0.99  --symbol_type_check                     false
% 1.89/0.99  --clausify_out                          false
% 1.89/0.99  --sig_cnt_out                           false
% 1.89/0.99  --trig_cnt_out                          false
% 1.89/0.99  --trig_cnt_out_tolerance                1.
% 1.89/0.99  --trig_cnt_out_sk_spl                   false
% 1.89/0.99  --abstr_cl_out                          false
% 1.89/0.99  
% 1.89/0.99  ------ Global Options
% 1.89/0.99  
% 1.89/0.99  --schedule                              default
% 1.89/0.99  --add_important_lit                     false
% 1.89/0.99  --prop_solver_per_cl                    1000
% 1.89/0.99  --min_unsat_core                        false
% 1.89/0.99  --soft_assumptions                      false
% 1.89/0.99  --soft_lemma_size                       3
% 1.89/0.99  --prop_impl_unit_size                   0
% 1.89/0.99  --prop_impl_unit                        []
% 1.89/0.99  --share_sel_clauses                     true
% 1.89/0.99  --reset_solvers                         false
% 1.89/0.99  --bc_imp_inh                            [conj_cone]
% 1.89/0.99  --conj_cone_tolerance                   3.
% 1.89/0.99  --extra_neg_conj                        none
% 1.89/0.99  --large_theory_mode                     true
% 1.89/0.99  --prolific_symb_bound                   200
% 1.89/0.99  --lt_threshold                          2000
% 1.89/0.99  --clause_weak_htbl                      true
% 1.89/0.99  --gc_record_bc_elim                     false
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing Options
% 1.89/0.99  
% 1.89/0.99  --preprocessing_flag                    true
% 1.89/0.99  --time_out_prep_mult                    0.1
% 1.89/0.99  --splitting_mode                        input
% 1.89/0.99  --splitting_grd                         true
% 1.89/0.99  --splitting_cvd                         false
% 1.89/0.99  --splitting_cvd_svl                     false
% 1.89/0.99  --splitting_nvd                         32
% 1.89/0.99  --sub_typing                            true
% 1.89/0.99  --prep_gs_sim                           true
% 1.89/0.99  --prep_unflatten                        true
% 1.89/0.99  --prep_res_sim                          true
% 1.89/0.99  --prep_upred                            true
% 1.89/0.99  --prep_sem_filter                       exhaustive
% 1.89/0.99  --prep_sem_filter_out                   false
% 1.89/0.99  --pred_elim                             true
% 1.89/0.99  --res_sim_input                         true
% 1.89/0.99  --eq_ax_congr_red                       true
% 1.89/0.99  --pure_diseq_elim                       true
% 1.89/0.99  --brand_transform                       false
% 1.89/0.99  --non_eq_to_eq                          false
% 1.89/0.99  --prep_def_merge                        true
% 1.89/0.99  --prep_def_merge_prop_impl              false
% 1.89/0.99  --prep_def_merge_mbd                    true
% 1.89/0.99  --prep_def_merge_tr_red                 false
% 1.89/0.99  --prep_def_merge_tr_cl                  false
% 1.89/0.99  --smt_preprocessing                     true
% 1.89/0.99  --smt_ac_axioms                         fast
% 1.89/0.99  --preprocessed_out                      false
% 1.89/0.99  --preprocessed_stats                    false
% 1.89/0.99  
% 1.89/0.99  ------ Abstraction refinement Options
% 1.89/0.99  
% 1.89/0.99  --abstr_ref                             []
% 1.89/0.99  --abstr_ref_prep                        false
% 1.89/0.99  --abstr_ref_until_sat                   false
% 1.89/0.99  --abstr_ref_sig_restrict                funpre
% 1.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/0.99  --abstr_ref_under                       []
% 1.89/0.99  
% 1.89/0.99  ------ SAT Options
% 1.89/0.99  
% 1.89/0.99  --sat_mode                              false
% 1.89/0.99  --sat_fm_restart_options                ""
% 1.89/0.99  --sat_gr_def                            false
% 1.89/0.99  --sat_epr_types                         true
% 1.89/0.99  --sat_non_cyclic_types                  false
% 1.89/0.99  --sat_finite_models                     false
% 1.89/0.99  --sat_fm_lemmas                         false
% 1.89/0.99  --sat_fm_prep                           false
% 1.89/0.99  --sat_fm_uc_incr                        true
% 1.89/0.99  --sat_out_model                         small
% 1.89/0.99  --sat_out_clauses                       false
% 1.89/0.99  
% 1.89/0.99  ------ QBF Options
% 1.89/0.99  
% 1.89/0.99  --qbf_mode                              false
% 1.89/0.99  --qbf_elim_univ                         false
% 1.89/0.99  --qbf_dom_inst                          none
% 1.89/0.99  --qbf_dom_pre_inst                      false
% 1.89/0.99  --qbf_sk_in                             false
% 1.89/0.99  --qbf_pred_elim                         true
% 1.89/0.99  --qbf_split                             512
% 1.89/0.99  
% 1.89/0.99  ------ BMC1 Options
% 1.89/0.99  
% 1.89/0.99  --bmc1_incremental                      false
% 1.89/0.99  --bmc1_axioms                           reachable_all
% 1.89/0.99  --bmc1_min_bound                        0
% 1.89/0.99  --bmc1_max_bound                        -1
% 1.89/0.99  --bmc1_max_bound_default                -1
% 1.89/0.99  --bmc1_symbol_reachability              true
% 1.89/0.99  --bmc1_property_lemmas                  false
% 1.89/0.99  --bmc1_k_induction                      false
% 1.89/0.99  --bmc1_non_equiv_states                 false
% 1.89/0.99  --bmc1_deadlock                         false
% 1.89/0.99  --bmc1_ucm                              false
% 1.89/0.99  --bmc1_add_unsat_core                   none
% 1.89/0.99  --bmc1_unsat_core_children              false
% 1.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/0.99  --bmc1_out_stat                         full
% 1.89/0.99  --bmc1_ground_init                      false
% 1.89/0.99  --bmc1_pre_inst_next_state              false
% 1.89/0.99  --bmc1_pre_inst_state                   false
% 1.89/0.99  --bmc1_pre_inst_reach_state             false
% 1.89/0.99  --bmc1_out_unsat_core                   false
% 1.89/0.99  --bmc1_aig_witness_out                  false
% 1.89/0.99  --bmc1_verbose                          false
% 1.89/0.99  --bmc1_dump_clauses_tptp                false
% 1.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.89/0.99  --bmc1_dump_file                        -
% 1.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.89/0.99  --bmc1_ucm_extend_mode                  1
% 1.89/0.99  --bmc1_ucm_init_mode                    2
% 1.89/0.99  --bmc1_ucm_cone_mode                    none
% 1.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.89/0.99  --bmc1_ucm_relax_model                  4
% 1.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/0.99  --bmc1_ucm_layered_model                none
% 1.89/0.99  --bmc1_ucm_max_lemma_size               10
% 1.89/0.99  
% 1.89/0.99  ------ AIG Options
% 1.89/0.99  
% 1.89/0.99  --aig_mode                              false
% 1.89/0.99  
% 1.89/0.99  ------ Instantiation Options
% 1.89/0.99  
% 1.89/0.99  --instantiation_flag                    true
% 1.89/0.99  --inst_sos_flag                         false
% 1.89/0.99  --inst_sos_phase                        true
% 1.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel_side                     none
% 1.89/0.99  --inst_solver_per_active                1400
% 1.89/0.99  --inst_solver_calls_frac                1.
% 1.89/0.99  --inst_passive_queue_type               priority_queues
% 1.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/0.99  --inst_passive_queues_freq              [25;2]
% 1.89/0.99  --inst_dismatching                      true
% 1.89/0.99  --inst_eager_unprocessed_to_passive     true
% 1.89/0.99  --inst_prop_sim_given                   true
% 1.89/0.99  --inst_prop_sim_new                     false
% 1.89/0.99  --inst_subs_new                         false
% 1.89/0.99  --inst_eq_res_simp                      false
% 1.89/0.99  --inst_subs_given                       false
% 1.89/0.99  --inst_orphan_elimination               true
% 1.89/0.99  --inst_learning_loop_flag               true
% 1.89/0.99  --inst_learning_start                   3000
% 1.89/0.99  --inst_learning_factor                  2
% 1.89/0.99  --inst_start_prop_sim_after_learn       3
% 1.89/0.99  --inst_sel_renew                        solver
% 1.89/0.99  --inst_lit_activity_flag                true
% 1.89/0.99  --inst_restr_to_given                   false
% 1.89/0.99  --inst_activity_threshold               500
% 1.89/0.99  --inst_out_proof                        true
% 1.89/0.99  
% 1.89/0.99  ------ Resolution Options
% 1.89/0.99  
% 1.89/0.99  --resolution_flag                       false
% 1.89/0.99  --res_lit_sel                           adaptive
% 1.89/0.99  --res_lit_sel_side                      none
% 1.89/0.99  --res_ordering                          kbo
% 1.89/0.99  --res_to_prop_solver                    active
% 1.89/0.99  --res_prop_simpl_new                    false
% 1.89/0.99  --res_prop_simpl_given                  true
% 1.89/0.99  --res_passive_queue_type                priority_queues
% 1.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/0.99  --res_passive_queues_freq               [15;5]
% 1.89/0.99  --res_forward_subs                      full
% 1.89/0.99  --res_backward_subs                     full
% 1.89/0.99  --res_forward_subs_resolution           true
% 1.89/0.99  --res_backward_subs_resolution          true
% 1.89/0.99  --res_orphan_elimination                true
% 1.89/0.99  --res_time_limit                        2.
% 1.89/0.99  --res_out_proof                         true
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Options
% 1.89/0.99  
% 1.89/0.99  --superposition_flag                    true
% 1.89/0.99  --sup_passive_queue_type                priority_queues
% 1.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.89/0.99  --demod_completeness_check              fast
% 1.89/0.99  --demod_use_ground                      true
% 1.89/0.99  --sup_to_prop_solver                    passive
% 1.89/0.99  --sup_prop_simpl_new                    true
% 1.89/0.99  --sup_prop_simpl_given                  true
% 1.89/0.99  --sup_fun_splitting                     false
% 1.89/0.99  --sup_smt_interval                      50000
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Simplification Setup
% 1.89/0.99  
% 1.89/0.99  --sup_indices_passive                   []
% 1.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_full_bw                           [BwDemod]
% 1.89/0.99  --sup_immed_triv                        [TrivRules]
% 1.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_immed_bw_main                     []
% 1.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  
% 1.89/0.99  ------ Combination Options
% 1.89/0.99  
% 1.89/0.99  --comb_res_mult                         3
% 1.89/0.99  --comb_sup_mult                         2
% 1.89/0.99  --comb_inst_mult                        10
% 1.89/0.99  
% 1.89/0.99  ------ Debug Options
% 1.89/0.99  
% 1.89/0.99  --dbg_backtrace                         false
% 1.89/0.99  --dbg_dump_prop_clauses                 false
% 1.89/0.99  --dbg_dump_prop_clauses_file            -
% 1.89/0.99  --dbg_out_stat                          false
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  ------ Proving...
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  % SZS status Theorem for theBenchmark.p
% 1.89/0.99  
% 1.89/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.89/0.99  
% 1.89/0.99  fof(f1,axiom,(
% 1.89/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f21,plain,(
% 1.89/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f1])).
% 1.89/0.99  
% 1.89/0.99  fof(f28,plain,(
% 1.89/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.89/0.99    inference(nnf_transformation,[],[f21])).
% 1.89/0.99  
% 1.89/0.99  fof(f29,plain,(
% 1.89/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.89/0.99    inference(rectify,[],[f28])).
% 1.89/0.99  
% 1.89/0.99  fof(f30,plain,(
% 1.89/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f31,plain,(
% 1.89/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 1.89/0.99  
% 1.89/0.99  fof(f47,plain,(
% 1.89/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f31])).
% 1.89/0.99  
% 1.89/0.99  fof(f18,axiom,(
% 1.89/0.99    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f25,plain,(
% 1.89/0.99    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 1.89/0.99    inference(ennf_transformation,[],[f18])).
% 1.89/0.99  
% 1.89/0.99  fof(f73,plain,(
% 1.89/0.99    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f25])).
% 1.89/0.99  
% 1.89/0.99  fof(f11,axiom,(
% 1.89/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f59,plain,(
% 1.89/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.89/0.99    inference(cnf_transformation,[],[f11])).
% 1.89/0.99  
% 1.89/0.99  fof(f4,axiom,(
% 1.89/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f52,plain,(
% 1.89/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f4])).
% 1.89/0.99  
% 1.89/0.99  fof(f5,axiom,(
% 1.89/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f53,plain,(
% 1.89/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f5])).
% 1.89/0.99  
% 1.89/0.99  fof(f6,axiom,(
% 1.89/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f54,plain,(
% 1.89/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f6])).
% 1.89/0.99  
% 1.89/0.99  fof(f7,axiom,(
% 1.89/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f55,plain,(
% 1.89/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f7])).
% 1.89/0.99  
% 1.89/0.99  fof(f8,axiom,(
% 1.89/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f56,plain,(
% 1.89/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f8])).
% 1.89/0.99  
% 1.89/0.99  fof(f9,axiom,(
% 1.89/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f57,plain,(
% 1.89/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f9])).
% 1.89/0.99  
% 1.89/0.99  fof(f77,plain,(
% 1.89/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.89/0.99    inference(definition_unfolding,[],[f56,f57])).
% 1.89/0.99  
% 1.89/0.99  fof(f78,plain,(
% 1.89/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.89/0.99    inference(definition_unfolding,[],[f55,f77])).
% 1.89/0.99  
% 1.89/0.99  fof(f79,plain,(
% 1.89/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.89/0.99    inference(definition_unfolding,[],[f54,f78])).
% 1.89/0.99  
% 1.89/0.99  fof(f80,plain,(
% 1.89/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.89/0.99    inference(definition_unfolding,[],[f53,f79])).
% 1.89/0.99  
% 1.89/0.99  fof(f81,plain,(
% 1.89/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.89/0.99    inference(definition_unfolding,[],[f52,f80])).
% 1.89/0.99  
% 1.89/0.99  fof(f82,plain,(
% 1.89/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.89/0.99    inference(definition_unfolding,[],[f59,f81])).
% 1.89/0.99  
% 1.89/0.99  fof(f85,plain,(
% 1.89/0.99    ( ! [X0] : (k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.89/0.99    inference(definition_unfolding,[],[f73,f82])).
% 1.89/0.99  
% 1.89/0.99  fof(f19,conjecture,(
% 1.89/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f20,negated_conjecture,(
% 1.89/0.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.89/0.99    inference(negated_conjecture,[],[f19])).
% 1.89/0.99  
% 1.89/0.99  fof(f26,plain,(
% 1.89/0.99    ? [X0,X1,X2] : (((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 1.89/0.99    inference(ennf_transformation,[],[f20])).
% 1.89/0.99  
% 1.89/0.99  fof(f27,plain,(
% 1.89/0.99    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2))),
% 1.89/0.99    inference(flattening,[],[f26])).
% 1.89/0.99  
% 1.89/0.99  fof(f45,plain,(
% 1.89/0.99    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2)) => ((~r2_hidden(sK8,k3_relat_1(sK9)) | ~r2_hidden(sK7,k3_relat_1(sK9))) & r2_hidden(k4_tarski(sK7,sK8),sK9) & v1_relat_1(sK9))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f46,plain,(
% 1.89/0.99    (~r2_hidden(sK8,k3_relat_1(sK9)) | ~r2_hidden(sK7,k3_relat_1(sK9))) & r2_hidden(k4_tarski(sK7,sK8),sK9) & v1_relat_1(sK9)),
% 1.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f27,f45])).
% 1.89/0.99  
% 1.89/0.99  fof(f74,plain,(
% 1.89/0.99    v1_relat_1(sK9)),
% 1.89/0.99    inference(cnf_transformation,[],[f46])).
% 1.89/0.99  
% 1.89/0.99  fof(f3,axiom,(
% 1.89/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f51,plain,(
% 1.89/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f3])).
% 1.89/0.99  
% 1.89/0.99  fof(f84,plain,(
% 1.89/0.99    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.89/0.99    inference(definition_unfolding,[],[f51,f81,f81])).
% 1.89/0.99  
% 1.89/0.99  fof(f2,axiom,(
% 1.89/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f50,plain,(
% 1.89/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.89/0.99    inference(cnf_transformation,[],[f2])).
% 1.89/0.99  
% 1.89/0.99  fof(f83,plain,(
% 1.89/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.89/0.99    inference(definition_unfolding,[],[f50,f82])).
% 1.89/0.99  
% 1.89/0.99  fof(f17,axiom,(
% 1.89/0.99    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f39,plain,(
% 1.89/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.89/0.99    inference(nnf_transformation,[],[f17])).
% 1.89/0.99  
% 1.89/0.99  fof(f40,plain,(
% 1.89/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.89/0.99    inference(rectify,[],[f39])).
% 1.89/0.99  
% 1.89/0.99  fof(f43,plain,(
% 1.89/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f42,plain,(
% 1.89/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f41,plain,(
% 1.89/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f44,plain,(
% 1.89/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).
% 1.89/0.99  
% 1.89/0.99  fof(f70,plain,(
% 1.89/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.89/0.99    inference(cnf_transformation,[],[f44])).
% 1.89/0.99  
% 1.89/0.99  fof(f88,plain,(
% 1.89/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 1.89/0.99    inference(equality_resolution,[],[f70])).
% 1.89/0.99  
% 1.89/0.99  fof(f16,axiom,(
% 1.89/0.99    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f33,plain,(
% 1.89/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.89/0.99    inference(nnf_transformation,[],[f16])).
% 1.89/0.99  
% 1.89/0.99  fof(f34,plain,(
% 1.89/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.89/0.99    inference(rectify,[],[f33])).
% 1.89/0.99  
% 1.89/0.99  fof(f37,plain,(
% 1.89/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f36,plain,(
% 1.89/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f35,plain,(
% 1.89/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f38,plain,(
% 1.89/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 1.89/0.99  
% 1.89/0.99  fof(f66,plain,(
% 1.89/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.89/0.99    inference(cnf_transformation,[],[f38])).
% 1.89/0.99  
% 1.89/0.99  fof(f86,plain,(
% 1.89/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 1.89/0.99    inference(equality_resolution,[],[f66])).
% 1.89/0.99  
% 1.89/0.99  fof(f76,plain,(
% 1.89/0.99    ~r2_hidden(sK8,k3_relat_1(sK9)) | ~r2_hidden(sK7,k3_relat_1(sK9))),
% 1.89/0.99    inference(cnf_transformation,[],[f46])).
% 1.89/0.99  
% 1.89/0.99  fof(f75,plain,(
% 1.89/0.99    r2_hidden(k4_tarski(sK7,sK8),sK9)),
% 1.89/0.99    inference(cnf_transformation,[],[f46])).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2,plain,
% 1.89/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.89/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1169,plain,
% 1.89/0.99      ( r2_hidden(sK8,X0)
% 1.89/0.99      | ~ r2_hidden(sK8,k2_relat_1(sK9))
% 1.89/0.99      | ~ r1_tarski(k2_relat_1(sK9),X0) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2875,plain,
% 1.89/0.99      ( r2_hidden(sK8,k3_relat_1(sK9))
% 1.89/0.99      | ~ r2_hidden(sK8,k2_relat_1(sK9))
% 1.89/0.99      | ~ r1_tarski(k2_relat_1(sK9),k3_relat_1(sK9)) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1169]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_19,plain,
% 1.89/0.99      ( ~ v1_relat_1(X0)
% 1.89/0.99      | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 1.89/0.99      inference(cnf_transformation,[],[f85]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_22,negated_conjecture,
% 1.89/0.99      ( v1_relat_1(sK9) ),
% 1.89/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_297,plain,
% 1.89/0.99      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 1.89/0.99      | sK9 != X0 ),
% 1.89/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_298,plain,
% 1.89/0.99      ( k3_tarski(k6_enumset1(k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k2_relat_1(sK9))) = k3_relat_1(sK9) ),
% 1.89/0.99      inference(unflattening,[status(thm)],[c_297]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_4,plain,
% 1.89/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 1.89/0.99      inference(cnf_transformation,[],[f84]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3,plain,
% 1.89/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 1.89/0.99      inference(cnf_transformation,[],[f83]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_965,plain,
% 1.89/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 1.89/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1798,plain,
% 1.89/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 1.89/0.99      inference(superposition,[status(thm)],[c_4,c_965]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2097,plain,
% 1.89/0.99      ( r1_tarski(k2_relat_1(sK9),k3_relat_1(sK9)) = iProver_top ),
% 1.89/0.99      inference(superposition,[status(thm)],[c_298,c_1798]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2102,plain,
% 1.89/0.99      ( r1_tarski(k2_relat_1(sK9),k3_relat_1(sK9)) ),
% 1.89/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2097]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1153,plain,
% 1.89/0.99      ( r2_hidden(sK7,X0)
% 1.89/0.99      | ~ r2_hidden(sK7,k1_relat_1(sK9))
% 1.89/0.99      | ~ r1_tarski(k1_relat_1(sK9),X0) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1922,plain,
% 1.89/0.99      ( r2_hidden(sK7,k3_relat_1(sK9))
% 1.89/0.99      | ~ r2_hidden(sK7,k1_relat_1(sK9))
% 1.89/0.99      | ~ r1_tarski(k1_relat_1(sK9),k3_relat_1(sK9)) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_1153]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1797,plain,
% 1.89/0.99      ( r1_tarski(k1_relat_1(sK9),k3_relat_1(sK9)) = iProver_top ),
% 1.89/0.99      inference(superposition,[status(thm)],[c_298,c_965]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1804,plain,
% 1.89/0.99      ( r1_tarski(k1_relat_1(sK9),k3_relat_1(sK9)) ),
% 1.89/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1797]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_17,plain,
% 1.89/0.99      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 1.89/0.99      inference(cnf_transformation,[],[f88]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1100,plain,
% 1.89/0.99      ( ~ r2_hidden(k4_tarski(sK7,sK8),sK9)
% 1.89/0.99      | r2_hidden(sK8,k2_relat_1(sK9)) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_13,plain,
% 1.89/0.99      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 1.89/0.99      inference(cnf_transformation,[],[f86]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1087,plain,
% 1.89/0.99      ( ~ r2_hidden(k4_tarski(sK7,sK8),sK9)
% 1.89/0.99      | r2_hidden(sK7,k1_relat_1(sK9)) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_20,negated_conjecture,
% 1.89/0.99      ( ~ r2_hidden(sK7,k3_relat_1(sK9))
% 1.89/0.99      | ~ r2_hidden(sK8,k3_relat_1(sK9)) ),
% 1.89/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_21,negated_conjecture,
% 1.89/0.99      ( r2_hidden(k4_tarski(sK7,sK8),sK9) ),
% 1.89/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(contradiction,plain,
% 1.89/0.99      ( $false ),
% 1.89/0.99      inference(minisat,
% 1.89/0.99                [status(thm)],
% 1.89/0.99                [c_2875,c_2102,c_1922,c_1804,c_1100,c_1087,c_20,c_21]) ).
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.89/0.99  
% 1.89/0.99  ------                               Statistics
% 1.89/0.99  
% 1.89/0.99  ------ General
% 1.89/0.99  
% 1.89/0.99  abstr_ref_over_cycles:                  0
% 1.89/0.99  abstr_ref_under_cycles:                 0
% 1.89/0.99  gc_basic_clause_elim:                   0
% 1.89/0.99  forced_gc_time:                         0
% 1.89/0.99  parsing_time:                           0.01
% 1.89/0.99  unif_index_cands_time:                  0.
% 1.89/0.99  unif_index_add_time:                    0.
% 1.89/0.99  orderings_time:                         0.
% 1.89/0.99  out_proof_time:                         0.011
% 1.89/0.99  total_time:                             0.117
% 1.89/0.99  num_of_symbols:                         53
% 1.89/0.99  num_of_terms:                           3223
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing
% 1.89/0.99  
% 1.89/0.99  num_of_splits:                          0
% 1.89/0.99  num_of_split_atoms:                     0
% 1.89/0.99  num_of_reused_defs:                     0
% 1.89/0.99  num_eq_ax_congr_red:                    51
% 1.89/0.99  num_of_sem_filtered_clauses:            1
% 1.89/0.99  num_of_subtypes:                        0
% 1.89/0.99  monotx_restored_types:                  0
% 1.89/0.99  sat_num_of_epr_types:                   0
% 1.89/0.99  sat_num_of_non_cyclic_types:            0
% 1.89/0.99  sat_guarded_non_collapsed_types:        0
% 1.89/0.99  num_pure_diseq_elim:                    0
% 1.89/0.99  simp_replaced_by:                       0
% 1.89/0.99  res_preprocessed:                       101
% 1.89/0.99  prep_upred:                             0
% 1.89/0.99  prep_unflattend:                        26
% 1.89/0.99  smt_new_axioms:                         0
% 1.89/0.99  pred_elim_cands:                        2
% 1.89/0.99  pred_elim:                              3
% 1.89/0.99  pred_elim_cl:                           4
% 1.89/0.99  pred_elim_cycles:                       5
% 1.89/0.99  merged_defs:                            2
% 1.89/0.99  merged_defs_ncl:                        0
% 1.89/0.99  bin_hyper_res:                          2
% 1.89/0.99  prep_cycles:                            4
% 1.89/0.99  pred_elim_time:                         0.004
% 1.89/0.99  splitting_time:                         0.
% 1.89/0.99  sem_filter_time:                        0.
% 1.89/0.99  monotx_time:                            0.
% 1.89/0.99  subtype_inf_time:                       0.
% 1.89/0.99  
% 1.89/0.99  ------ Problem properties
% 1.89/0.99  
% 1.89/0.99  clauses:                                19
% 1.89/0.99  conjectures:                            2
% 1.89/0.99  epr:                                    1
% 1.89/0.99  horn:                                   16
% 1.89/0.99  ground:                                 3
% 1.89/0.99  unary:                                  5
% 1.89/0.99  binary:                                 9
% 1.89/0.99  lits:                                   38
% 1.89/0.99  lits_eq:                                7
% 1.89/0.99  fd_pure:                                0
% 1.89/0.99  fd_pseudo:                              0
% 1.89/0.99  fd_cond:                                0
% 1.89/0.99  fd_pseudo_cond:                         4
% 1.89/0.99  ac_symbols:                             0
% 1.89/0.99  
% 1.89/0.99  ------ Propositional Solver
% 1.89/0.99  
% 1.89/0.99  prop_solver_calls:                      26
% 1.89/0.99  prop_fast_solver_calls:                 535
% 1.89/0.99  smt_solver_calls:                       0
% 1.89/0.99  smt_fast_solver_calls:                  0
% 1.89/0.99  prop_num_of_clauses:                    1058
% 1.89/0.99  prop_preprocess_simplified:             4686
% 1.89/0.99  prop_fo_subsumed:                       0
% 1.89/0.99  prop_solver_time:                       0.
% 1.89/0.99  smt_solver_time:                        0.
% 1.89/0.99  smt_fast_solver_time:                   0.
% 1.89/0.99  prop_fast_solver_time:                  0.
% 1.89/0.99  prop_unsat_core_time:                   0.
% 1.89/0.99  
% 1.89/0.99  ------ QBF
% 1.89/0.99  
% 1.89/0.99  qbf_q_res:                              0
% 1.89/0.99  qbf_num_tautologies:                    0
% 1.89/0.99  qbf_prep_cycles:                        0
% 1.89/0.99  
% 1.89/0.99  ------ BMC1
% 1.89/0.99  
% 1.89/0.99  bmc1_current_bound:                     -1
% 1.89/0.99  bmc1_last_solved_bound:                 -1
% 1.89/0.99  bmc1_unsat_core_size:                   -1
% 1.89/0.99  bmc1_unsat_core_parents_size:           -1
% 1.89/0.99  bmc1_merge_next_fun:                    0
% 1.89/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.89/0.99  
% 1.89/0.99  ------ Instantiation
% 1.89/0.99  
% 1.89/0.99  inst_num_of_clauses:                    294
% 1.89/0.99  inst_num_in_passive:                    167
% 1.89/0.99  inst_num_in_active:                     126
% 1.89/0.99  inst_num_in_unprocessed:                0
% 1.89/0.99  inst_num_of_loops:                      143
% 1.89/0.99  inst_num_of_learning_restarts:          0
% 1.89/0.99  inst_num_moves_active_passive:          15
% 1.89/0.99  inst_lit_activity:                      0
% 1.89/0.99  inst_lit_activity_moves:                0
% 1.89/0.99  inst_num_tautologies:                   0
% 1.89/0.99  inst_num_prop_implied:                  0
% 1.89/0.99  inst_num_existing_simplified:           0
% 1.89/0.99  inst_num_eq_res_simplified:             0
% 1.89/0.99  inst_num_child_elim:                    0
% 1.89/0.99  inst_num_of_dismatching_blockings:      40
% 1.89/0.99  inst_num_of_non_proper_insts:           159
% 1.89/0.99  inst_num_of_duplicates:                 0
% 1.89/0.99  inst_inst_num_from_inst_to_res:         0
% 1.89/0.99  inst_dismatching_checking_time:         0.
% 1.89/0.99  
% 1.89/0.99  ------ Resolution
% 1.89/0.99  
% 1.89/0.99  res_num_of_clauses:                     0
% 1.89/0.99  res_num_in_passive:                     0
% 1.89/0.99  res_num_in_active:                      0
% 1.89/0.99  res_num_of_loops:                       105
% 1.89/0.99  res_forward_subset_subsumed:            0
% 1.89/0.99  res_backward_subset_subsumed:           0
% 1.89/0.99  res_forward_subsumed:                   0
% 1.89/0.99  res_backward_subsumed:                  0
% 1.89/0.99  res_forward_subsumption_resolution:     0
% 1.89/0.99  res_backward_subsumption_resolution:    0
% 1.89/0.99  res_clause_to_clause_subsumption:       99
% 1.89/0.99  res_orphan_elimination:                 0
% 1.89/0.99  res_tautology_del:                      11
% 1.89/0.99  res_num_eq_res_simplified:              0
% 1.89/0.99  res_num_sel_changes:                    0
% 1.89/0.99  res_moves_from_active_to_pass:          0
% 1.89/0.99  
% 1.89/0.99  ------ Superposition
% 1.89/0.99  
% 1.89/0.99  sup_time_total:                         0.
% 1.89/0.99  sup_time_generating:                    0.
% 1.89/0.99  sup_time_sim_full:                      0.
% 1.89/0.99  sup_time_sim_immed:                     0.
% 1.89/0.99  
% 1.89/0.99  sup_num_of_clauses:                     58
% 1.89/0.99  sup_num_in_active:                      28
% 1.89/0.99  sup_num_in_passive:                     30
% 1.89/0.99  sup_num_of_loops:                       28
% 1.89/0.99  sup_fw_superposition:                   27
% 1.89/0.99  sup_bw_superposition:                   18
% 1.89/0.99  sup_immediate_simplified:               0
% 1.89/0.99  sup_given_eliminated:                   0
% 1.89/0.99  comparisons_done:                       0
% 1.89/0.99  comparisons_avoided:                    0
% 1.89/0.99  
% 1.89/0.99  ------ Simplifications
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  sim_fw_subset_subsumed:                 0
% 1.89/0.99  sim_bw_subset_subsumed:                 0
% 1.89/0.99  sim_fw_subsumed:                        0
% 1.89/0.99  sim_bw_subsumed:                        0
% 1.89/0.99  sim_fw_subsumption_res:                 0
% 1.89/0.99  sim_bw_subsumption_res:                 0
% 1.89/0.99  sim_tautology_del:                      4
% 1.89/0.99  sim_eq_tautology_del:                   0
% 1.89/0.99  sim_eq_res_simp:                        0
% 1.89/0.99  sim_fw_demodulated:                     0
% 1.89/0.99  sim_bw_demodulated:                     0
% 1.89/0.99  sim_light_normalised:                   0
% 1.89/0.99  sim_joinable_taut:                      0
% 1.89/0.99  sim_joinable_simp:                      0
% 1.89/0.99  sim_ac_normalised:                      0
% 1.89/0.99  sim_smt_subsumption:                    0
% 1.89/0.99  
%------------------------------------------------------------------------------
