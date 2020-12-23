%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:31 EST 2020

% Result     : Theorem 15.74s
% Output     : CNFRefutation 15.74s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 306 expanded)
%              Number of clauses        :   49 (  71 expanded)
%              Number of leaves         :   28 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  523 ( 887 expanded)
%              Number of equality atoms :  272 ( 474 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f99])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f100])).

fof(f102,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f101])).

fof(f103,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f102])).

fof(f104,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f103])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f104])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f51,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f52,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK9,k1_tarski(sK8))
        | ~ r2_hidden(sK8,k2_relat_1(sK9)) )
      & ( k1_xboole_0 != k10_relat_1(sK9,k1_tarski(sK8))
        | r2_hidden(sK8,k2_relat_1(sK9)) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK9,k1_tarski(sK8))
      | ~ r2_hidden(sK8,k2_relat_1(sK9)) )
    & ( k1_xboole_0 != k10_relat_1(sK9,k1_tarski(sK8))
      | r2_hidden(sK8,k2_relat_1(sK9)) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f51,f52])).

fof(f98,plain,
    ( k1_xboole_0 = k10_relat_1(sK9,k1_tarski(sK8))
    | ~ r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,
    ( k1_xboole_0 = k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
    | ~ r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(definition_unfolding,[],[f98,f104])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f53])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f44,f47,f46,f45])).

fof(f90,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f122,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f41,f40,f39])).

fof(f86,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f110,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f68])).

fof(f13,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5) != X0
            & sK1(X0,X1,X2,X3,X4,X5) != X1
            & sK1(X0,X1,X2,X3,X4,X5) != X2
            & sK1(X0,X1,X2,X3,X4,X5) != X3
            & sK1(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK1(X0,X1,X2,X3,X4,X5) = X0
          | sK1(X0,X1,X2,X3,X4,X5) = X1
          | sK1(X0,X1,X2,X3,X4,X5) = X2
          | sK1(X0,X1,X2,X3,X4,X5) = X3
          | sK1(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5) != X0
              & sK1(X0,X1,X2,X3,X4,X5) != X1
              & sK1(X0,X1,X2,X3,X4,X5) != X2
              & sK1(X0,X1,X2,X3,X4,X5) != X3
              & sK1(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK1(X0,X1,X2,X3,X4,X5) = X0
            | sK1(X0,X1,X2,X3,X4,X5) = X1
            | sK1(X0,X1,X2,X3,X4,X5) = X2
            | sK1(X0,X1,X2,X3,X4,X5) = X3
            | sK1(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f71,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X7,X5) ) ),
    inference(equality_resolution,[],[f71])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f22,f26])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f82,f100])).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f107])).

fof(f97,plain,
    ( k1_xboole_0 != k10_relat_1(sK9,k1_tarski(sK8))
    | r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f53])).

fof(f109,plain,
    ( k1_xboole_0 != k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
    | r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(definition_unfolding,[],[f97,f104])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3638,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3642,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8915,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3638,c_3642])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3639,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_48666,plain,
    ( k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8915,c_3639])).

cnf(c_35,negated_conjecture,
    ( ~ r2_hidden(sK8,k2_relat_1(sK9))
    | k1_xboole_0 = k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3618,plain,
    ( k1_xboole_0 = k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
    | r2_hidden(sK8,k2_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_56873,plain,
    ( k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = k1_xboole_0
    | k4_xboole_0(k2_relat_1(sK9),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = k2_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_48666,c_3618])).

cnf(c_33,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_535,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | k10_relat_1(X0,X1) = k1_xboole_0
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_37])).

cnf(c_536,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK9),X0)
    | k10_relat_1(sK9,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_1687,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK9),X0)
    | k10_relat_1(sK9,X0) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_536])).

cnf(c_4208,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK9),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
    | k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5846,plain,
    ( r1_xboole_0(k2_relat_1(sK9),X0)
    | k4_xboole_0(k2_relat_1(sK9),X0) != k2_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_29292,plain,
    ( r1_xboole_0(k2_relat_1(sK9),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
    | k4_xboole_0(k2_relat_1(sK9),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != k2_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_5846])).

cnf(c_57228,plain,
    ( k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_56873,c_4208,c_29292])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3619,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_577,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK9 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_578,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK9,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK9) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_3609,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK9,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_5666,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top
    | r2_hidden(sK7(sK9,X0),k10_relat_1(sK9,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3619,c_3609])).

cnf(c_57243,plain,
    ( r2_hidden(X0,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top
    | r2_hidden(sK7(sK9,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_57228,c_5666])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3637,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4475,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_3637])).

cnf(c_58509,plain,
    ( r2_hidden(X0,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_57243,c_4475])).

cnf(c_58511,plain,
    ( r2_hidden(sK8,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != iProver_top
    | r2_hidden(sK8,k2_relat_1(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58509])).

cnf(c_2803,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4147,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2803])).

cnf(c_2804,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3932,plain,
    ( k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) ),
    inference(instantiation,[status(thm)],[c_2804])).

cnf(c_4146,plain,
    ( k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3932])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X4,X5) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_22,plain,
    ( sP0(X0,X1,X2,X3,X4,k6_enumset1(X4,X4,X4,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1337,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | k6_enumset1(X4,X4,X4,X4,X5,X7,X9,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_1338,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
    inference(unflattening,[status(thm)],[c_1337])).

cnf(c_1339,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1338])).

cnf(c_1341,plain,
    ( r2_hidden(sK8,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_36,negated_conjecture,
    ( r2_hidden(sK8,k2_relat_1(sK9))
    | k1_xboole_0 != k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_39,plain,
    ( k1_xboole_0 != k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
    | r2_hidden(sK8,k2_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58511,c_57228,c_4147,c_4146,c_1341,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 16:39:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.74/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.74/2.48  
% 15.74/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.74/2.48  
% 15.74/2.48  ------  iProver source info
% 15.74/2.48  
% 15.74/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.74/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.74/2.48  git: non_committed_changes: false
% 15.74/2.48  git: last_make_outside_of_git: false
% 15.74/2.48  
% 15.74/2.48  ------ 
% 15.74/2.48  
% 15.74/2.48  ------ Input Options
% 15.74/2.48  
% 15.74/2.48  --out_options                           all
% 15.74/2.48  --tptp_safe_out                         true
% 15.74/2.48  --problem_path                          ""
% 15.74/2.48  --include_path                          ""
% 15.74/2.48  --clausifier                            res/vclausify_rel
% 15.74/2.48  --clausifier_options                    --mode clausify
% 15.74/2.48  --stdin                                 false
% 15.74/2.48  --stats_out                             all
% 15.74/2.48  
% 15.74/2.48  ------ General Options
% 15.74/2.48  
% 15.74/2.48  --fof                                   false
% 15.74/2.48  --time_out_real                         305.
% 15.74/2.48  --time_out_virtual                      -1.
% 15.74/2.48  --symbol_type_check                     false
% 15.74/2.48  --clausify_out                          false
% 15.74/2.48  --sig_cnt_out                           false
% 15.74/2.48  --trig_cnt_out                          false
% 15.74/2.48  --trig_cnt_out_tolerance                1.
% 15.74/2.48  --trig_cnt_out_sk_spl                   false
% 15.74/2.48  --abstr_cl_out                          false
% 15.74/2.48  
% 15.74/2.48  ------ Global Options
% 15.74/2.48  
% 15.74/2.48  --schedule                              default
% 15.74/2.48  --add_important_lit                     false
% 15.74/2.48  --prop_solver_per_cl                    1000
% 15.74/2.48  --min_unsat_core                        false
% 15.74/2.48  --soft_assumptions                      false
% 15.74/2.48  --soft_lemma_size                       3
% 15.74/2.48  --prop_impl_unit_size                   0
% 15.74/2.48  --prop_impl_unit                        []
% 15.74/2.48  --share_sel_clauses                     true
% 15.74/2.48  --reset_solvers                         false
% 15.74/2.48  --bc_imp_inh                            [conj_cone]
% 15.74/2.48  --conj_cone_tolerance                   3.
% 15.74/2.48  --extra_neg_conj                        none
% 15.74/2.48  --large_theory_mode                     true
% 15.74/2.48  --prolific_symb_bound                   200
% 15.74/2.48  --lt_threshold                          2000
% 15.74/2.48  --clause_weak_htbl                      true
% 15.74/2.48  --gc_record_bc_elim                     false
% 15.74/2.48  
% 15.74/2.48  ------ Preprocessing Options
% 15.74/2.48  
% 15.74/2.48  --preprocessing_flag                    true
% 15.74/2.48  --time_out_prep_mult                    0.1
% 15.74/2.48  --splitting_mode                        input
% 15.74/2.48  --splitting_grd                         true
% 15.74/2.48  --splitting_cvd                         false
% 15.74/2.48  --splitting_cvd_svl                     false
% 15.74/2.48  --splitting_nvd                         32
% 15.74/2.48  --sub_typing                            true
% 15.74/2.48  --prep_gs_sim                           true
% 15.74/2.48  --prep_unflatten                        true
% 15.74/2.48  --prep_res_sim                          true
% 15.74/2.48  --prep_upred                            true
% 15.74/2.48  --prep_sem_filter                       exhaustive
% 15.74/2.48  --prep_sem_filter_out                   false
% 15.74/2.48  --pred_elim                             true
% 15.74/2.48  --res_sim_input                         true
% 15.74/2.48  --eq_ax_congr_red                       true
% 15.74/2.48  --pure_diseq_elim                       true
% 15.74/2.48  --brand_transform                       false
% 15.74/2.48  --non_eq_to_eq                          false
% 15.74/2.48  --prep_def_merge                        true
% 15.74/2.48  --prep_def_merge_prop_impl              false
% 15.74/2.48  --prep_def_merge_mbd                    true
% 15.74/2.48  --prep_def_merge_tr_red                 false
% 15.74/2.48  --prep_def_merge_tr_cl                  false
% 15.74/2.48  --smt_preprocessing                     true
% 15.74/2.48  --smt_ac_axioms                         fast
% 15.74/2.48  --preprocessed_out                      false
% 15.74/2.48  --preprocessed_stats                    false
% 15.74/2.48  
% 15.74/2.48  ------ Abstraction refinement Options
% 15.74/2.48  
% 15.74/2.48  --abstr_ref                             []
% 15.74/2.48  --abstr_ref_prep                        false
% 15.74/2.48  --abstr_ref_until_sat                   false
% 15.74/2.48  --abstr_ref_sig_restrict                funpre
% 15.74/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.74/2.48  --abstr_ref_under                       []
% 15.74/2.48  
% 15.74/2.48  ------ SAT Options
% 15.74/2.48  
% 15.74/2.48  --sat_mode                              false
% 15.74/2.48  --sat_fm_restart_options                ""
% 15.74/2.48  --sat_gr_def                            false
% 15.74/2.48  --sat_epr_types                         true
% 15.74/2.48  --sat_non_cyclic_types                  false
% 15.74/2.48  --sat_finite_models                     false
% 15.74/2.48  --sat_fm_lemmas                         false
% 15.74/2.48  --sat_fm_prep                           false
% 15.74/2.48  --sat_fm_uc_incr                        true
% 15.74/2.48  --sat_out_model                         small
% 15.74/2.48  --sat_out_clauses                       false
% 15.74/2.48  
% 15.74/2.48  ------ QBF Options
% 15.74/2.48  
% 15.74/2.48  --qbf_mode                              false
% 15.74/2.48  --qbf_elim_univ                         false
% 15.74/2.48  --qbf_dom_inst                          none
% 15.74/2.48  --qbf_dom_pre_inst                      false
% 15.74/2.48  --qbf_sk_in                             false
% 15.74/2.48  --qbf_pred_elim                         true
% 15.74/2.48  --qbf_split                             512
% 15.74/2.48  
% 15.74/2.48  ------ BMC1 Options
% 15.74/2.48  
% 15.74/2.48  --bmc1_incremental                      false
% 15.74/2.48  --bmc1_axioms                           reachable_all
% 15.74/2.48  --bmc1_min_bound                        0
% 15.74/2.48  --bmc1_max_bound                        -1
% 15.74/2.48  --bmc1_max_bound_default                -1
% 15.74/2.48  --bmc1_symbol_reachability              true
% 15.74/2.48  --bmc1_property_lemmas                  false
% 15.74/2.48  --bmc1_k_induction                      false
% 15.74/2.48  --bmc1_non_equiv_states                 false
% 15.74/2.48  --bmc1_deadlock                         false
% 15.74/2.48  --bmc1_ucm                              false
% 15.74/2.48  --bmc1_add_unsat_core                   none
% 15.74/2.48  --bmc1_unsat_core_children              false
% 15.74/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.74/2.48  --bmc1_out_stat                         full
% 15.74/2.48  --bmc1_ground_init                      false
% 15.74/2.48  --bmc1_pre_inst_next_state              false
% 15.74/2.48  --bmc1_pre_inst_state                   false
% 15.74/2.48  --bmc1_pre_inst_reach_state             false
% 15.74/2.48  --bmc1_out_unsat_core                   false
% 15.74/2.48  --bmc1_aig_witness_out                  false
% 15.74/2.48  --bmc1_verbose                          false
% 15.74/2.48  --bmc1_dump_clauses_tptp                false
% 15.74/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.74/2.48  --bmc1_dump_file                        -
% 15.74/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.74/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.74/2.48  --bmc1_ucm_extend_mode                  1
% 15.74/2.48  --bmc1_ucm_init_mode                    2
% 15.74/2.48  --bmc1_ucm_cone_mode                    none
% 15.74/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.74/2.48  --bmc1_ucm_relax_model                  4
% 15.74/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.74/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.74/2.48  --bmc1_ucm_layered_model                none
% 15.74/2.48  --bmc1_ucm_max_lemma_size               10
% 15.74/2.48  
% 15.74/2.48  ------ AIG Options
% 15.74/2.48  
% 15.74/2.48  --aig_mode                              false
% 15.74/2.48  
% 15.74/2.48  ------ Instantiation Options
% 15.74/2.48  
% 15.74/2.48  --instantiation_flag                    true
% 15.74/2.48  --inst_sos_flag                         false
% 15.74/2.48  --inst_sos_phase                        true
% 15.74/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.74/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.74/2.48  --inst_lit_sel_side                     num_symb
% 15.74/2.48  --inst_solver_per_active                1400
% 15.74/2.48  --inst_solver_calls_frac                1.
% 15.74/2.48  --inst_passive_queue_type               priority_queues
% 15.74/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.74/2.48  --inst_passive_queues_freq              [25;2]
% 15.74/2.48  --inst_dismatching                      true
% 15.74/2.48  --inst_eager_unprocessed_to_passive     true
% 15.74/2.48  --inst_prop_sim_given                   true
% 15.74/2.48  --inst_prop_sim_new                     false
% 15.74/2.48  --inst_subs_new                         false
% 15.74/2.48  --inst_eq_res_simp                      false
% 15.74/2.48  --inst_subs_given                       false
% 15.74/2.48  --inst_orphan_elimination               true
% 15.74/2.48  --inst_learning_loop_flag               true
% 15.74/2.48  --inst_learning_start                   3000
% 15.74/2.48  --inst_learning_factor                  2
% 15.74/2.48  --inst_start_prop_sim_after_learn       3
% 15.74/2.48  --inst_sel_renew                        solver
% 15.74/2.48  --inst_lit_activity_flag                true
% 15.74/2.48  --inst_restr_to_given                   false
% 15.74/2.48  --inst_activity_threshold               500
% 15.74/2.48  --inst_out_proof                        true
% 15.74/2.48  
% 15.74/2.48  ------ Resolution Options
% 15.74/2.48  
% 15.74/2.48  --resolution_flag                       true
% 15.74/2.48  --res_lit_sel                           adaptive
% 15.74/2.48  --res_lit_sel_side                      none
% 15.74/2.48  --res_ordering                          kbo
% 15.74/2.48  --res_to_prop_solver                    active
% 15.74/2.48  --res_prop_simpl_new                    false
% 15.74/2.48  --res_prop_simpl_given                  true
% 15.74/2.48  --res_passive_queue_type                priority_queues
% 15.74/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.74/2.48  --res_passive_queues_freq               [15;5]
% 15.74/2.48  --res_forward_subs                      full
% 15.74/2.48  --res_backward_subs                     full
% 15.74/2.48  --res_forward_subs_resolution           true
% 15.74/2.48  --res_backward_subs_resolution          true
% 15.74/2.48  --res_orphan_elimination                true
% 15.74/2.48  --res_time_limit                        2.
% 15.74/2.48  --res_out_proof                         true
% 15.74/2.48  
% 15.74/2.48  ------ Superposition Options
% 15.74/2.48  
% 15.74/2.48  --superposition_flag                    true
% 15.74/2.48  --sup_passive_queue_type                priority_queues
% 15.74/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.74/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.74/2.48  --demod_completeness_check              fast
% 15.74/2.48  --demod_use_ground                      true
% 15.74/2.48  --sup_to_prop_solver                    passive
% 15.74/2.48  --sup_prop_simpl_new                    true
% 15.74/2.48  --sup_prop_simpl_given                  true
% 15.74/2.48  --sup_fun_splitting                     false
% 15.74/2.48  --sup_smt_interval                      50000
% 15.74/2.48  
% 15.74/2.48  ------ Superposition Simplification Setup
% 15.74/2.48  
% 15.74/2.48  --sup_indices_passive                   []
% 15.74/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.74/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.74/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.74/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.74/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.74/2.48  --sup_full_bw                           [BwDemod]
% 15.74/2.48  --sup_immed_triv                        [TrivRules]
% 15.74/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.74/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.74/2.48  --sup_immed_bw_main                     []
% 15.74/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.74/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.74/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.74/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.74/2.48  
% 15.74/2.48  ------ Combination Options
% 15.74/2.48  
% 15.74/2.48  --comb_res_mult                         3
% 15.74/2.48  --comb_sup_mult                         2
% 15.74/2.48  --comb_inst_mult                        10
% 15.74/2.48  
% 15.74/2.48  ------ Debug Options
% 15.74/2.48  
% 15.74/2.48  --dbg_backtrace                         false
% 15.74/2.48  --dbg_dump_prop_clauses                 false
% 15.74/2.48  --dbg_dump_prop_clauses_file            -
% 15.74/2.48  --dbg_out_stat                          false
% 15.74/2.48  ------ Parsing...
% 15.74/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.74/2.48  
% 15.74/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.74/2.48  
% 15.74/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.74/2.48  
% 15.74/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.74/2.48  ------ Proving...
% 15.74/2.48  ------ Problem Properties 
% 15.74/2.48  
% 15.74/2.48  
% 15.74/2.48  clauses                                 37
% 15.74/2.48  conjectures                             2
% 15.74/2.48  EPR                                     7
% 15.74/2.48  Horn                                    30
% 15.74/2.48  unary                                   5
% 15.74/2.48  binary                                  18
% 15.74/2.48  lits                                    92
% 15.74/2.48  lits eq                                 32
% 15.74/2.48  fd_pure                                 0
% 15.74/2.48  fd_pseudo                               0
% 15.74/2.48  fd_cond                                 1
% 15.74/2.48  fd_pseudo_cond                          7
% 15.74/2.48  AC symbols                              0
% 15.74/2.48  
% 15.74/2.48  ------ Schedule dynamic 5 is on 
% 15.74/2.48  
% 15.74/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.74/2.48  
% 15.74/2.48  
% 15.74/2.48  ------ 
% 15.74/2.48  Current options:
% 15.74/2.48  ------ 
% 15.74/2.48  
% 15.74/2.48  ------ Input Options
% 15.74/2.48  
% 15.74/2.48  --out_options                           all
% 15.74/2.48  --tptp_safe_out                         true
% 15.74/2.48  --problem_path                          ""
% 15.74/2.48  --include_path                          ""
% 15.74/2.48  --clausifier                            res/vclausify_rel
% 15.74/2.48  --clausifier_options                    --mode clausify
% 15.74/2.48  --stdin                                 false
% 15.74/2.48  --stats_out                             all
% 15.74/2.48  
% 15.74/2.48  ------ General Options
% 15.74/2.48  
% 15.74/2.48  --fof                                   false
% 15.74/2.48  --time_out_real                         305.
% 15.74/2.48  --time_out_virtual                      -1.
% 15.74/2.48  --symbol_type_check                     false
% 15.74/2.48  --clausify_out                          false
% 15.74/2.48  --sig_cnt_out                           false
% 15.74/2.48  --trig_cnt_out                          false
% 15.74/2.48  --trig_cnt_out_tolerance                1.
% 15.74/2.48  --trig_cnt_out_sk_spl                   false
% 15.74/2.48  --abstr_cl_out                          false
% 15.74/2.48  
% 15.74/2.48  ------ Global Options
% 15.74/2.48  
% 15.74/2.48  --schedule                              default
% 15.74/2.48  --add_important_lit                     false
% 15.74/2.48  --prop_solver_per_cl                    1000
% 15.74/2.48  --min_unsat_core                        false
% 15.74/2.48  --soft_assumptions                      false
% 15.74/2.48  --soft_lemma_size                       3
% 15.74/2.48  --prop_impl_unit_size                   0
% 15.74/2.48  --prop_impl_unit                        []
% 15.74/2.48  --share_sel_clauses                     true
% 15.74/2.48  --reset_solvers                         false
% 15.74/2.48  --bc_imp_inh                            [conj_cone]
% 15.74/2.48  --conj_cone_tolerance                   3.
% 15.74/2.48  --extra_neg_conj                        none
% 15.74/2.48  --large_theory_mode                     true
% 15.74/2.48  --prolific_symb_bound                   200
% 15.74/2.48  --lt_threshold                          2000
% 15.74/2.48  --clause_weak_htbl                      true
% 15.74/2.48  --gc_record_bc_elim                     false
% 15.74/2.48  
% 15.74/2.48  ------ Preprocessing Options
% 15.74/2.48  
% 15.74/2.48  --preprocessing_flag                    true
% 15.74/2.48  --time_out_prep_mult                    0.1
% 15.74/2.48  --splitting_mode                        input
% 15.74/2.48  --splitting_grd                         true
% 15.74/2.48  --splitting_cvd                         false
% 15.74/2.48  --splitting_cvd_svl                     false
% 15.74/2.48  --splitting_nvd                         32
% 15.74/2.48  --sub_typing                            true
% 15.74/2.48  --prep_gs_sim                           true
% 15.74/2.48  --prep_unflatten                        true
% 15.74/2.48  --prep_res_sim                          true
% 15.74/2.48  --prep_upred                            true
% 15.74/2.48  --prep_sem_filter                       exhaustive
% 15.74/2.48  --prep_sem_filter_out                   false
% 15.74/2.48  --pred_elim                             true
% 15.74/2.48  --res_sim_input                         true
% 15.74/2.48  --eq_ax_congr_red                       true
% 15.74/2.48  --pure_diseq_elim                       true
% 15.74/2.48  --brand_transform                       false
% 15.74/2.48  --non_eq_to_eq                          false
% 15.74/2.48  --prep_def_merge                        true
% 15.74/2.48  --prep_def_merge_prop_impl              false
% 15.74/2.48  --prep_def_merge_mbd                    true
% 15.74/2.48  --prep_def_merge_tr_red                 false
% 15.74/2.48  --prep_def_merge_tr_cl                  false
% 15.74/2.48  --smt_preprocessing                     true
% 15.74/2.48  --smt_ac_axioms                         fast
% 15.74/2.48  --preprocessed_out                      false
% 15.74/2.48  --preprocessed_stats                    false
% 15.74/2.48  
% 15.74/2.48  ------ Abstraction refinement Options
% 15.74/2.48  
% 15.74/2.48  --abstr_ref                             []
% 15.74/2.48  --abstr_ref_prep                        false
% 15.74/2.48  --abstr_ref_until_sat                   false
% 15.74/2.48  --abstr_ref_sig_restrict                funpre
% 15.74/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.74/2.48  --abstr_ref_under                       []
% 15.74/2.48  
% 15.74/2.48  ------ SAT Options
% 15.74/2.48  
% 15.74/2.48  --sat_mode                              false
% 15.74/2.48  --sat_fm_restart_options                ""
% 15.74/2.48  --sat_gr_def                            false
% 15.74/2.48  --sat_epr_types                         true
% 15.74/2.48  --sat_non_cyclic_types                  false
% 15.74/2.48  --sat_finite_models                     false
% 15.74/2.48  --sat_fm_lemmas                         false
% 15.74/2.48  --sat_fm_prep                           false
% 15.74/2.48  --sat_fm_uc_incr                        true
% 15.74/2.48  --sat_out_model                         small
% 15.74/2.48  --sat_out_clauses                       false
% 15.74/2.48  
% 15.74/2.48  ------ QBF Options
% 15.74/2.48  
% 15.74/2.48  --qbf_mode                              false
% 15.74/2.48  --qbf_elim_univ                         false
% 15.74/2.48  --qbf_dom_inst                          none
% 15.74/2.48  --qbf_dom_pre_inst                      false
% 15.74/2.48  --qbf_sk_in                             false
% 15.74/2.48  --qbf_pred_elim                         true
% 15.74/2.48  --qbf_split                             512
% 15.74/2.48  
% 15.74/2.48  ------ BMC1 Options
% 15.74/2.48  
% 15.74/2.48  --bmc1_incremental                      false
% 15.74/2.48  --bmc1_axioms                           reachable_all
% 15.74/2.48  --bmc1_min_bound                        0
% 15.74/2.48  --bmc1_max_bound                        -1
% 15.74/2.48  --bmc1_max_bound_default                -1
% 15.74/2.48  --bmc1_symbol_reachability              true
% 15.74/2.48  --bmc1_property_lemmas                  false
% 15.74/2.48  --bmc1_k_induction                      false
% 15.74/2.48  --bmc1_non_equiv_states                 false
% 15.74/2.48  --bmc1_deadlock                         false
% 15.74/2.48  --bmc1_ucm                              false
% 15.74/2.48  --bmc1_add_unsat_core                   none
% 15.74/2.48  --bmc1_unsat_core_children              false
% 15.74/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.74/2.48  --bmc1_out_stat                         full
% 15.74/2.48  --bmc1_ground_init                      false
% 15.74/2.48  --bmc1_pre_inst_next_state              false
% 15.74/2.48  --bmc1_pre_inst_state                   false
% 15.74/2.48  --bmc1_pre_inst_reach_state             false
% 15.74/2.48  --bmc1_out_unsat_core                   false
% 15.74/2.48  --bmc1_aig_witness_out                  false
% 15.74/2.48  --bmc1_verbose                          false
% 15.74/2.48  --bmc1_dump_clauses_tptp                false
% 15.74/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.74/2.48  --bmc1_dump_file                        -
% 15.74/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.74/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.74/2.48  --bmc1_ucm_extend_mode                  1
% 15.74/2.48  --bmc1_ucm_init_mode                    2
% 15.74/2.48  --bmc1_ucm_cone_mode                    none
% 15.74/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.74/2.48  --bmc1_ucm_relax_model                  4
% 15.74/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.74/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.74/2.48  --bmc1_ucm_layered_model                none
% 15.74/2.48  --bmc1_ucm_max_lemma_size               10
% 15.74/2.48  
% 15.74/2.48  ------ AIG Options
% 15.74/2.48  
% 15.74/2.48  --aig_mode                              false
% 15.74/2.48  
% 15.74/2.48  ------ Instantiation Options
% 15.74/2.48  
% 15.74/2.48  --instantiation_flag                    true
% 15.74/2.48  --inst_sos_flag                         false
% 15.74/2.48  --inst_sos_phase                        true
% 15.74/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.74/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.74/2.48  --inst_lit_sel_side                     none
% 15.74/2.48  --inst_solver_per_active                1400
% 15.74/2.48  --inst_solver_calls_frac                1.
% 15.74/2.48  --inst_passive_queue_type               priority_queues
% 15.74/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.74/2.48  --inst_passive_queues_freq              [25;2]
% 15.74/2.48  --inst_dismatching                      true
% 15.74/2.48  --inst_eager_unprocessed_to_passive     true
% 15.74/2.48  --inst_prop_sim_given                   true
% 15.74/2.48  --inst_prop_sim_new                     false
% 15.74/2.48  --inst_subs_new                         false
% 15.74/2.48  --inst_eq_res_simp                      false
% 15.74/2.48  --inst_subs_given                       false
% 15.74/2.48  --inst_orphan_elimination               true
% 15.74/2.48  --inst_learning_loop_flag               true
% 15.74/2.48  --inst_learning_start                   3000
% 15.74/2.48  --inst_learning_factor                  2
% 15.74/2.48  --inst_start_prop_sim_after_learn       3
% 15.74/2.48  --inst_sel_renew                        solver
% 15.74/2.48  --inst_lit_activity_flag                true
% 15.74/2.48  --inst_restr_to_given                   false
% 15.74/2.48  --inst_activity_threshold               500
% 15.74/2.48  --inst_out_proof                        true
% 15.74/2.48  
% 15.74/2.48  ------ Resolution Options
% 15.74/2.48  
% 15.74/2.48  --resolution_flag                       false
% 15.74/2.48  --res_lit_sel                           adaptive
% 15.74/2.48  --res_lit_sel_side                      none
% 15.74/2.48  --res_ordering                          kbo
% 15.74/2.48  --res_to_prop_solver                    active
% 15.74/2.48  --res_prop_simpl_new                    false
% 15.74/2.48  --res_prop_simpl_given                  true
% 15.74/2.48  --res_passive_queue_type                priority_queues
% 15.74/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.74/2.48  --res_passive_queues_freq               [15;5]
% 15.74/2.48  --res_forward_subs                      full
% 15.74/2.48  --res_backward_subs                     full
% 15.74/2.48  --res_forward_subs_resolution           true
% 15.74/2.48  --res_backward_subs_resolution          true
% 15.74/2.48  --res_orphan_elimination                true
% 15.74/2.48  --res_time_limit                        2.
% 15.74/2.48  --res_out_proof                         true
% 15.74/2.48  
% 15.74/2.48  ------ Superposition Options
% 15.74/2.48  
% 15.74/2.48  --superposition_flag                    true
% 15.74/2.48  --sup_passive_queue_type                priority_queues
% 15.74/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.74/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.74/2.48  --demod_completeness_check              fast
% 15.74/2.48  --demod_use_ground                      true
% 15.74/2.48  --sup_to_prop_solver                    passive
% 15.74/2.48  --sup_prop_simpl_new                    true
% 15.74/2.48  --sup_prop_simpl_given                  true
% 15.74/2.48  --sup_fun_splitting                     false
% 15.74/2.48  --sup_smt_interval                      50000
% 15.74/2.48  
% 15.74/2.48  ------ Superposition Simplification Setup
% 15.74/2.48  
% 15.74/2.48  --sup_indices_passive                   []
% 15.74/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.74/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.74/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.74/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.74/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.74/2.48  --sup_full_bw                           [BwDemod]
% 15.74/2.48  --sup_immed_triv                        [TrivRules]
% 15.74/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.74/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.74/2.48  --sup_immed_bw_main                     []
% 15.74/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.74/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.74/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.74/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.74/2.48  
% 15.74/2.48  ------ Combination Options
% 15.74/2.48  
% 15.74/2.48  --comb_res_mult                         3
% 15.74/2.48  --comb_sup_mult                         2
% 15.74/2.48  --comb_inst_mult                        10
% 15.74/2.48  
% 15.74/2.48  ------ Debug Options
% 15.74/2.48  
% 15.74/2.48  --dbg_backtrace                         false
% 15.74/2.48  --dbg_dump_prop_clauses                 false
% 15.74/2.48  --dbg_dump_prop_clauses_file            -
% 15.74/2.48  --dbg_out_stat                          false
% 15.74/2.48  
% 15.74/2.48  
% 15.74/2.48  
% 15.74/2.48  
% 15.74/2.48  ------ Proving...
% 15.74/2.48  
% 15.74/2.48  
% 15.74/2.48  % SZS status Theorem for theBenchmark.p
% 15.74/2.48  
% 15.74/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.74/2.48  
% 15.74/2.48  fof(f11,axiom,(
% 15.74/2.48    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f21,plain,(
% 15.74/2.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 15.74/2.48    inference(ennf_transformation,[],[f11])).
% 15.74/2.48  
% 15.74/2.48  fof(f65,plain,(
% 15.74/2.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f21])).
% 15.74/2.48  
% 15.74/2.48  fof(f4,axiom,(
% 15.74/2.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f58,plain,(
% 15.74/2.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f4])).
% 15.74/2.48  
% 15.74/2.48  fof(f5,axiom,(
% 15.74/2.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f59,plain,(
% 15.74/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f5])).
% 15.74/2.48  
% 15.74/2.48  fof(f6,axiom,(
% 15.74/2.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f60,plain,(
% 15.74/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f6])).
% 15.74/2.48  
% 15.74/2.48  fof(f7,axiom,(
% 15.74/2.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f61,plain,(
% 15.74/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f7])).
% 15.74/2.48  
% 15.74/2.48  fof(f8,axiom,(
% 15.74/2.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f62,plain,(
% 15.74/2.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f8])).
% 15.74/2.48  
% 15.74/2.48  fof(f9,axiom,(
% 15.74/2.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f63,plain,(
% 15.74/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f9])).
% 15.74/2.48  
% 15.74/2.48  fof(f10,axiom,(
% 15.74/2.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f64,plain,(
% 15.74/2.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f10])).
% 15.74/2.48  
% 15.74/2.48  fof(f99,plain,(
% 15.74/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 15.74/2.48    inference(definition_unfolding,[],[f63,f64])).
% 15.74/2.48  
% 15.74/2.48  fof(f100,plain,(
% 15.74/2.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 15.74/2.48    inference(definition_unfolding,[],[f62,f99])).
% 15.74/2.48  
% 15.74/2.48  fof(f101,plain,(
% 15.74/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 15.74/2.48    inference(definition_unfolding,[],[f61,f100])).
% 15.74/2.48  
% 15.74/2.48  fof(f102,plain,(
% 15.74/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 15.74/2.48    inference(definition_unfolding,[],[f60,f101])).
% 15.74/2.48  
% 15.74/2.48  fof(f103,plain,(
% 15.74/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 15.74/2.48    inference(definition_unfolding,[],[f59,f102])).
% 15.74/2.48  
% 15.74/2.48  fof(f104,plain,(
% 15.74/2.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 15.74/2.48    inference(definition_unfolding,[],[f58,f103])).
% 15.74/2.48  
% 15.74/2.48  fof(f105,plain,(
% 15.74/2.48    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 15.74/2.48    inference(definition_unfolding,[],[f65,f104])).
% 15.74/2.48  
% 15.74/2.48  fof(f1,axiom,(
% 15.74/2.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f20,plain,(
% 15.74/2.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.74/2.48    inference(ennf_transformation,[],[f1])).
% 15.74/2.48  
% 15.74/2.48  fof(f54,plain,(
% 15.74/2.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f20])).
% 15.74/2.48  
% 15.74/2.48  fof(f3,axiom,(
% 15.74/2.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f28,plain,(
% 15.74/2.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 15.74/2.48    inference(nnf_transformation,[],[f3])).
% 15.74/2.48  
% 15.74/2.48  fof(f56,plain,(
% 15.74/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f28])).
% 15.74/2.48  
% 15.74/2.48  fof(f18,conjecture,(
% 15.74/2.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f19,negated_conjecture,(
% 15.74/2.48    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 15.74/2.48    inference(negated_conjecture,[],[f18])).
% 15.74/2.48  
% 15.74/2.48  fof(f25,plain,(
% 15.74/2.48    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 15.74/2.48    inference(ennf_transformation,[],[f19])).
% 15.74/2.48  
% 15.74/2.48  fof(f50,plain,(
% 15.74/2.48    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 15.74/2.48    inference(nnf_transformation,[],[f25])).
% 15.74/2.48  
% 15.74/2.48  fof(f51,plain,(
% 15.74/2.48    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 15.74/2.48    inference(flattening,[],[f50])).
% 15.74/2.48  
% 15.74/2.48  fof(f52,plain,(
% 15.74/2.48    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK9,k1_tarski(sK8)) | ~r2_hidden(sK8,k2_relat_1(sK9))) & (k1_xboole_0 != k10_relat_1(sK9,k1_tarski(sK8)) | r2_hidden(sK8,k2_relat_1(sK9))) & v1_relat_1(sK9))),
% 15.74/2.48    introduced(choice_axiom,[])).
% 15.74/2.48  
% 15.74/2.48  fof(f53,plain,(
% 15.74/2.48    (k1_xboole_0 = k10_relat_1(sK9,k1_tarski(sK8)) | ~r2_hidden(sK8,k2_relat_1(sK9))) & (k1_xboole_0 != k10_relat_1(sK9,k1_tarski(sK8)) | r2_hidden(sK8,k2_relat_1(sK9))) & v1_relat_1(sK9)),
% 15.74/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f51,f52])).
% 15.74/2.48  
% 15.74/2.48  fof(f98,plain,(
% 15.74/2.48    k1_xboole_0 = k10_relat_1(sK9,k1_tarski(sK8)) | ~r2_hidden(sK8,k2_relat_1(sK9))),
% 15.74/2.48    inference(cnf_transformation,[],[f53])).
% 15.74/2.48  
% 15.74/2.48  fof(f108,plain,(
% 15.74/2.48    k1_xboole_0 = k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) | ~r2_hidden(sK8,k2_relat_1(sK9))),
% 15.74/2.48    inference(definition_unfolding,[],[f98,f104])).
% 15.74/2.48  
% 15.74/2.48  fof(f17,axiom,(
% 15.74/2.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f24,plain,(
% 15.74/2.48    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.74/2.48    inference(ennf_transformation,[],[f17])).
% 15.74/2.48  
% 15.74/2.48  fof(f49,plain,(
% 15.74/2.48    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 15.74/2.48    inference(nnf_transformation,[],[f24])).
% 15.74/2.48  
% 15.74/2.48  fof(f95,plain,(
% 15.74/2.48    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f49])).
% 15.74/2.48  
% 15.74/2.48  fof(f96,plain,(
% 15.74/2.48    v1_relat_1(sK9)),
% 15.74/2.48    inference(cnf_transformation,[],[f53])).
% 15.74/2.48  
% 15.74/2.48  fof(f57,plain,(
% 15.74/2.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 15.74/2.48    inference(cnf_transformation,[],[f28])).
% 15.74/2.48  
% 15.74/2.48  fof(f16,axiom,(
% 15.74/2.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f43,plain,(
% 15.74/2.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 15.74/2.48    inference(nnf_transformation,[],[f16])).
% 15.74/2.48  
% 15.74/2.48  fof(f44,plain,(
% 15.74/2.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.74/2.48    inference(rectify,[],[f43])).
% 15.74/2.48  
% 15.74/2.48  fof(f47,plain,(
% 15.74/2.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 15.74/2.48    introduced(choice_axiom,[])).
% 15.74/2.48  
% 15.74/2.48  fof(f46,plain,(
% 15.74/2.48    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0))) )),
% 15.74/2.48    introduced(choice_axiom,[])).
% 15.74/2.48  
% 15.74/2.48  fof(f45,plain,(
% 15.74/2.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 15.74/2.48    introduced(choice_axiom,[])).
% 15.74/2.48  
% 15.74/2.48  fof(f48,plain,(
% 15.74/2.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.74/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f44,f47,f46,f45])).
% 15.74/2.48  
% 15.74/2.48  fof(f90,plain,(
% 15.74/2.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 15.74/2.48    inference(cnf_transformation,[],[f48])).
% 15.74/2.48  
% 15.74/2.48  fof(f122,plain,(
% 15.74/2.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 15.74/2.48    inference(equality_resolution,[],[f90])).
% 15.74/2.48  
% 15.74/2.48  fof(f15,axiom,(
% 15.74/2.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f23,plain,(
% 15.74/2.48    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 15.74/2.48    inference(ennf_transformation,[],[f15])).
% 15.74/2.48  
% 15.74/2.48  fof(f37,plain,(
% 15.74/2.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 15.74/2.48    inference(nnf_transformation,[],[f23])).
% 15.74/2.48  
% 15.74/2.48  fof(f38,plain,(
% 15.74/2.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 15.74/2.48    inference(rectify,[],[f37])).
% 15.74/2.48  
% 15.74/2.48  fof(f41,plain,(
% 15.74/2.48    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)))),
% 15.74/2.48    introduced(choice_axiom,[])).
% 15.74/2.48  
% 15.74/2.48  fof(f40,plain,(
% 15.74/2.48    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0)))) )),
% 15.74/2.48    introduced(choice_axiom,[])).
% 15.74/2.48  
% 15.74/2.48  fof(f39,plain,(
% 15.74/2.48    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 15.74/2.48    introduced(choice_axiom,[])).
% 15.74/2.48  
% 15.74/2.48  fof(f42,plain,(
% 15.74/2.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 15.74/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f41,f40,f39])).
% 15.74/2.48  
% 15.74/2.48  fof(f86,plain,(
% 15.74/2.48    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f42])).
% 15.74/2.48  
% 15.74/2.48  fof(f118,plain,(
% 15.74/2.48    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 15.74/2.48    inference(equality_resolution,[],[f86])).
% 15.74/2.48  
% 15.74/2.48  fof(f12,axiom,(
% 15.74/2.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f29,plain,(
% 15.74/2.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 15.74/2.48    inference(nnf_transformation,[],[f12])).
% 15.74/2.48  
% 15.74/2.48  fof(f30,plain,(
% 15.74/2.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 15.74/2.48    inference(flattening,[],[f29])).
% 15.74/2.48  
% 15.74/2.48  fof(f68,plain,(
% 15.74/2.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 15.74/2.48    inference(cnf_transformation,[],[f30])).
% 15.74/2.48  
% 15.74/2.48  fof(f110,plain,(
% 15.74/2.48    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.74/2.48    inference(equality_resolution,[],[f68])).
% 15.74/2.48  
% 15.74/2.48  fof(f13,axiom,(
% 15.74/2.48    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f69,plain,(
% 15.74/2.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 15.74/2.48    inference(cnf_transformation,[],[f13])).
% 15.74/2.48  
% 15.74/2.48  fof(f26,plain,(
% 15.74/2.48    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 15.74/2.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 15.74/2.48  
% 15.74/2.48  fof(f31,plain,(
% 15.74/2.48    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 15.74/2.48    inference(nnf_transformation,[],[f26])).
% 15.74/2.48  
% 15.74/2.48  fof(f32,plain,(
% 15.74/2.48    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 15.74/2.48    inference(flattening,[],[f31])).
% 15.74/2.48  
% 15.74/2.48  fof(f33,plain,(
% 15.74/2.48    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 15.74/2.48    inference(rectify,[],[f32])).
% 15.74/2.48  
% 15.74/2.48  fof(f34,plain,(
% 15.74/2.48    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK1(X0,X1,X2,X3,X4,X5) != X0 & sK1(X0,X1,X2,X3,X4,X5) != X1 & sK1(X0,X1,X2,X3,X4,X5) != X2 & sK1(X0,X1,X2,X3,X4,X5) != X3 & sK1(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)) & (sK1(X0,X1,X2,X3,X4,X5) = X0 | sK1(X0,X1,X2,X3,X4,X5) = X1 | sK1(X0,X1,X2,X3,X4,X5) = X2 | sK1(X0,X1,X2,X3,X4,X5) = X3 | sK1(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5))))),
% 15.74/2.48    introduced(choice_axiom,[])).
% 15.74/2.48  
% 15.74/2.48  fof(f35,plain,(
% 15.74/2.48    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK1(X0,X1,X2,X3,X4,X5) != X0 & sK1(X0,X1,X2,X3,X4,X5) != X1 & sK1(X0,X1,X2,X3,X4,X5) != X2 & sK1(X0,X1,X2,X3,X4,X5) != X3 & sK1(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)) & (sK1(X0,X1,X2,X3,X4,X5) = X0 | sK1(X0,X1,X2,X3,X4,X5) = X1 | sK1(X0,X1,X2,X3,X4,X5) = X2 | sK1(X0,X1,X2,X3,X4,X5) = X3 | sK1(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 15.74/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 15.74/2.48  
% 15.74/2.48  fof(f71,plain,(
% 15.74/2.48    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 15.74/2.48    inference(cnf_transformation,[],[f35])).
% 15.74/2.48  
% 15.74/2.48  fof(f116,plain,(
% 15.74/2.48    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X7,X5)) )),
% 15.74/2.48    inference(equality_resolution,[],[f71])).
% 15.74/2.48  
% 15.74/2.48  fof(f14,axiom,(
% 15.74/2.48    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 15.74/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.74/2.48  
% 15.74/2.48  fof(f22,plain,(
% 15.74/2.48    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 15.74/2.48    inference(ennf_transformation,[],[f14])).
% 15.74/2.48  
% 15.74/2.48  fof(f27,plain,(
% 15.74/2.48    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 15.74/2.48    inference(definition_folding,[],[f22,f26])).
% 15.74/2.48  
% 15.74/2.48  fof(f36,plain,(
% 15.74/2.48    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 15.74/2.48    inference(nnf_transformation,[],[f27])).
% 15.74/2.48  
% 15.74/2.48  fof(f82,plain,(
% 15.74/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 15.74/2.48    inference(cnf_transformation,[],[f36])).
% 15.74/2.48  
% 15.74/2.48  fof(f107,plain,(
% 15.74/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 15.74/2.48    inference(definition_unfolding,[],[f82,f100])).
% 15.74/2.48  
% 15.74/2.48  fof(f117,plain,(
% 15.74/2.48    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) )),
% 15.74/2.48    inference(equality_resolution,[],[f107])).
% 15.74/2.48  
% 15.74/2.48  fof(f97,plain,(
% 15.74/2.48    k1_xboole_0 != k10_relat_1(sK9,k1_tarski(sK8)) | r2_hidden(sK8,k2_relat_1(sK9))),
% 15.74/2.48    inference(cnf_transformation,[],[f53])).
% 15.74/2.48  
% 15.74/2.48  fof(f109,plain,(
% 15.74/2.48    k1_xboole_0 != k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) | r2_hidden(sK8,k2_relat_1(sK9))),
% 15.74/2.48    inference(definition_unfolding,[],[f97,f104])).
% 15.74/2.48  
% 15.74/2.48  cnf(c_4,plain,
% 15.74/2.48      ( r2_hidden(X0,X1)
% 15.74/2.48      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 15.74/2.48      inference(cnf_transformation,[],[f105]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_3638,plain,
% 15.74/2.48      ( r2_hidden(X0,X1) = iProver_top
% 15.74/2.48      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 15.74/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_0,plain,
% 15.74/2.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.74/2.48      inference(cnf_transformation,[],[f54]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_3642,plain,
% 15.74/2.48      ( r1_xboole_0(X0,X1) != iProver_top
% 15.74/2.48      | r1_xboole_0(X1,X0) = iProver_top ),
% 15.74/2.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_8915,plain,
% 15.74/2.48      ( r2_hidden(X0,X1) = iProver_top
% 15.74/2.48      | r1_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 15.74/2.48      inference(superposition,[status(thm)],[c_3638,c_3642]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_3,plain,
% 15.74/2.48      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 15.74/2.48      inference(cnf_transformation,[],[f56]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_3639,plain,
% 15.74/2.48      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 15.74/2.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_48666,plain,
% 15.74/2.48      ( k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X0
% 15.74/2.48      | r2_hidden(X1,X0) = iProver_top ),
% 15.74/2.48      inference(superposition,[status(thm)],[c_8915,c_3639]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_35,negated_conjecture,
% 15.74/2.48      ( ~ r2_hidden(sK8,k2_relat_1(sK9))
% 15.74/2.48      | k1_xboole_0 = k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) ),
% 15.74/2.48      inference(cnf_transformation,[],[f108]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_3618,plain,
% 15.74/2.48      ( k1_xboole_0 = k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
% 15.74/2.48      | r2_hidden(sK8,k2_relat_1(sK9)) != iProver_top ),
% 15.74/2.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_56873,plain,
% 15.74/2.48      ( k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = k1_xboole_0
% 15.74/2.48      | k4_xboole_0(k2_relat_1(sK9),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = k2_relat_1(sK9) ),
% 15.74/2.48      inference(superposition,[status(thm)],[c_48666,c_3618]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_33,plain,
% 15.74/2.48      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 15.74/2.48      | ~ v1_relat_1(X0)
% 15.74/2.48      | k10_relat_1(X0,X1) = k1_xboole_0 ),
% 15.74/2.48      inference(cnf_transformation,[],[f95]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_37,negated_conjecture,
% 15.74/2.48      ( v1_relat_1(sK9) ),
% 15.74/2.48      inference(cnf_transformation,[],[f96]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_535,plain,
% 15.74/2.48      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 15.74/2.48      | k10_relat_1(X0,X1) = k1_xboole_0
% 15.74/2.48      | sK9 != X0 ),
% 15.74/2.48      inference(resolution_lifted,[status(thm)],[c_33,c_37]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_536,plain,
% 15.74/2.48      ( ~ r1_xboole_0(k2_relat_1(sK9),X0)
% 15.74/2.48      | k10_relat_1(sK9,X0) = k1_xboole_0 ),
% 15.74/2.48      inference(unflattening,[status(thm)],[c_535]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_1687,plain,
% 15.74/2.48      ( ~ r1_xboole_0(k2_relat_1(sK9),X0)
% 15.74/2.48      | k10_relat_1(sK9,X0) = k1_xboole_0 ),
% 15.74/2.48      inference(prop_impl,[status(thm)],[c_536]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_4208,plain,
% 15.74/2.48      ( ~ r1_xboole_0(k2_relat_1(sK9),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
% 15.74/2.48      | k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = k1_xboole_0 ),
% 15.74/2.48      inference(instantiation,[status(thm)],[c_1687]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_2,plain,
% 15.74/2.48      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 15.74/2.48      inference(cnf_transformation,[],[f57]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_5846,plain,
% 15.74/2.48      ( r1_xboole_0(k2_relat_1(sK9),X0)
% 15.74/2.48      | k4_xboole_0(k2_relat_1(sK9),X0) != k2_relat_1(sK9) ),
% 15.74/2.48      inference(instantiation,[status(thm)],[c_2]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_29292,plain,
% 15.74/2.48      ( r1_xboole_0(k2_relat_1(sK9),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
% 15.74/2.48      | k4_xboole_0(k2_relat_1(sK9),k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != k2_relat_1(sK9) ),
% 15.74/2.48      inference(instantiation,[status(thm)],[c_5846]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_57228,plain,
% 15.74/2.48      ( k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = k1_xboole_0 ),
% 15.74/2.48      inference(global_propositional_subsumption,
% 15.74/2.48                [status(thm)],
% 15.74/2.48                [c_56873,c_4208,c_29292]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_32,plain,
% 15.74/2.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.74/2.48      | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
% 15.74/2.48      inference(cnf_transformation,[],[f122]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_3619,plain,
% 15.74/2.48      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 15.74/2.48      | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) = iProver_top ),
% 15.74/2.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_26,plain,
% 15.74/2.48      ( ~ r2_hidden(X0,X1)
% 15.74/2.48      | r2_hidden(X2,k10_relat_1(X3,X1))
% 15.74/2.48      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 15.74/2.48      | ~ v1_relat_1(X3) ),
% 15.74/2.48      inference(cnf_transformation,[],[f118]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_577,plain,
% 15.74/2.48      ( ~ r2_hidden(X0,X1)
% 15.74/2.48      | r2_hidden(X2,k10_relat_1(X3,X1))
% 15.74/2.48      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 15.74/2.48      | sK9 != X3 ),
% 15.74/2.48      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_578,plain,
% 15.74/2.48      ( ~ r2_hidden(X0,X1)
% 15.74/2.48      | r2_hidden(X2,k10_relat_1(sK9,X1))
% 15.74/2.48      | ~ r2_hidden(k4_tarski(X2,X0),sK9) ),
% 15.74/2.48      inference(unflattening,[status(thm)],[c_577]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_3609,plain,
% 15.74/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.74/2.48      | r2_hidden(X2,k10_relat_1(sK9,X1)) = iProver_top
% 15.74/2.48      | r2_hidden(k4_tarski(X2,X0),sK9) != iProver_top ),
% 15.74/2.48      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_5666,plain,
% 15.74/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.74/2.48      | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top
% 15.74/2.48      | r2_hidden(sK7(sK9,X0),k10_relat_1(sK9,X1)) = iProver_top ),
% 15.74/2.48      inference(superposition,[status(thm)],[c_3619,c_3609]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_57243,plain,
% 15.74/2.48      ( r2_hidden(X0,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != iProver_top
% 15.74/2.48      | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top
% 15.74/2.48      | r2_hidden(sK7(sK9,X0),k1_xboole_0) = iProver_top ),
% 15.74/2.48      inference(superposition,[status(thm)],[c_57228,c_5666]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_5,plain,
% 15.74/2.48      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.74/2.48      inference(cnf_transformation,[],[f110]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_8,plain,
% 15.74/2.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 15.74/2.48      inference(cnf_transformation,[],[f69]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_3637,plain,
% 15.74/2.48      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 15.74/2.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_4475,plain,
% 15.74/2.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.74/2.48      inference(superposition,[status(thm)],[c_5,c_3637]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_58509,plain,
% 15.74/2.48      ( r2_hidden(X0,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != iProver_top
% 15.74/2.48      | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
% 15.74/2.48      inference(forward_subsumption_resolution,
% 15.74/2.48                [status(thm)],
% 15.74/2.48                [c_57243,c_4475]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_58511,plain,
% 15.74/2.48      ( r2_hidden(sK8,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != iProver_top
% 15.74/2.48      | r2_hidden(sK8,k2_relat_1(sK9)) != iProver_top ),
% 15.74/2.48      inference(instantiation,[status(thm)],[c_58509]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_2803,plain,( X0 = X0 ),theory(equality) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_4147,plain,
% 15.74/2.48      ( k1_xboole_0 = k1_xboole_0 ),
% 15.74/2.48      inference(instantiation,[status(thm)],[c_2803]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_2804,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_3932,plain,
% 15.74/2.48      ( k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != X0
% 15.74/2.48      | k1_xboole_0 != X0
% 15.74/2.48      | k1_xboole_0 = k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) ),
% 15.74/2.48      inference(instantiation,[status(thm)],[c_2804]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_4146,plain,
% 15.74/2.48      ( k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) != k1_xboole_0
% 15.74/2.48      | k1_xboole_0 = k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
% 15.74/2.48      | k1_xboole_0 != k1_xboole_0 ),
% 15.74/2.48      inference(instantiation,[status(thm)],[c_3932]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_19,plain,
% 15.74/2.48      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X4,X5) ),
% 15.74/2.48      inference(cnf_transformation,[],[f116]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_22,plain,
% 15.74/2.48      ( sP0(X0,X1,X2,X3,X4,k6_enumset1(X4,X4,X4,X4,X3,X2,X1,X0)) ),
% 15.74/2.48      inference(cnf_transformation,[],[f117]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_1337,plain,
% 15.74/2.48      ( r2_hidden(X0,X1)
% 15.74/2.48      | X2 != X3
% 15.74/2.48      | X4 != X0
% 15.74/2.48      | X5 != X6
% 15.74/2.48      | X7 != X8
% 15.74/2.48      | X9 != X10
% 15.74/2.48      | k6_enumset1(X4,X4,X4,X4,X5,X7,X9,X2) != X1 ),
% 15.74/2.48      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_1338,plain,
% 15.74/2.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
% 15.74/2.48      inference(unflattening,[status(thm)],[c_1337]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_1339,plain,
% 15.74/2.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) = iProver_top ),
% 15.74/2.48      inference(predicate_to_equality,[status(thm)],[c_1338]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_1341,plain,
% 15.74/2.48      ( r2_hidden(sK8,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) = iProver_top ),
% 15.74/2.48      inference(instantiation,[status(thm)],[c_1339]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_36,negated_conjecture,
% 15.74/2.48      ( r2_hidden(sK8,k2_relat_1(sK9))
% 15.74/2.48      | k1_xboole_0 != k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8)) ),
% 15.74/2.48      inference(cnf_transformation,[],[f109]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(c_39,plain,
% 15.74/2.48      ( k1_xboole_0 != k10_relat_1(sK9,k6_enumset1(sK8,sK8,sK8,sK8,sK8,sK8,sK8,sK8))
% 15.74/2.48      | r2_hidden(sK8,k2_relat_1(sK9)) = iProver_top ),
% 15.74/2.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.74/2.48  
% 15.74/2.48  cnf(contradiction,plain,
% 15.74/2.48      ( $false ),
% 15.74/2.48      inference(minisat,
% 15.74/2.48                [status(thm)],
% 15.74/2.48                [c_58511,c_57228,c_4147,c_4146,c_1341,c_39]) ).
% 15.74/2.48  
% 15.74/2.48  
% 15.74/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.74/2.48  
% 15.74/2.48  ------                               Statistics
% 15.74/2.48  
% 15.74/2.48  ------ General
% 15.74/2.48  
% 15.74/2.48  abstr_ref_over_cycles:                  0
% 15.74/2.48  abstr_ref_under_cycles:                 0
% 15.74/2.48  gc_basic_clause_elim:                   0
% 15.74/2.48  forced_gc_time:                         0
% 15.74/2.48  parsing_time:                           0.039
% 15.74/2.48  unif_index_cands_time:                  0.
% 15.74/2.48  unif_index_add_time:                    0.
% 15.74/2.48  orderings_time:                         0.
% 15.74/2.48  out_proof_time:                         0.011
% 15.74/2.48  total_time:                             1.913
% 15.74/2.48  num_of_symbols:                         51
% 15.74/2.48  num_of_terms:                           71015
% 15.74/2.48  
% 15.74/2.48  ------ Preprocessing
% 15.74/2.48  
% 15.74/2.48  num_of_splits:                          0
% 15.74/2.48  num_of_split_atoms:                     0
% 15.74/2.48  num_of_reused_defs:                     0
% 15.74/2.48  num_eq_ax_congr_red:                    81
% 15.74/2.48  num_of_sem_filtered_clauses:            1
% 15.74/2.48  num_of_subtypes:                        0
% 15.74/2.48  monotx_restored_types:                  0
% 15.74/2.48  sat_num_of_epr_types:                   0
% 15.74/2.48  sat_num_of_non_cyclic_types:            0
% 15.74/2.48  sat_guarded_non_collapsed_types:        0
% 15.74/2.48  num_pure_diseq_elim:                    0
% 15.74/2.48  simp_replaced_by:                       0
% 15.74/2.48  res_preprocessed:                       176
% 15.74/2.48  prep_upred:                             0
% 15.74/2.48  prep_unflattend:                        92
% 15.74/2.48  smt_new_axioms:                         0
% 15.74/2.48  pred_elim_cands:                        3
% 15.74/2.48  pred_elim:                              1
% 15.74/2.48  pred_elim_cl:                           1
% 15.74/2.48  pred_elim_cycles:                       3
% 15.74/2.48  merged_defs:                            22
% 15.74/2.48  merged_defs_ncl:                        0
% 15.74/2.48  bin_hyper_res:                          22
% 15.74/2.48  prep_cycles:                            4
% 15.74/2.48  pred_elim_time:                         0.027
% 15.74/2.48  splitting_time:                         0.
% 15.74/2.48  sem_filter_time:                        0.
% 15.74/2.48  monotx_time:                            0.001
% 15.74/2.48  subtype_inf_time:                       0.
% 15.74/2.48  
% 15.74/2.48  ------ Problem properties
% 15.74/2.48  
% 15.74/2.48  clauses:                                37
% 15.74/2.48  conjectures:                            2
% 15.74/2.48  epr:                                    7
% 15.74/2.48  horn:                                   30
% 15.74/2.48  ground:                                 2
% 15.74/2.48  unary:                                  5
% 15.74/2.48  binary:                                 18
% 15.74/2.48  lits:                                   92
% 15.74/2.48  lits_eq:                                32
% 15.74/2.48  fd_pure:                                0
% 15.74/2.48  fd_pseudo:                              0
% 15.74/2.48  fd_cond:                                1
% 15.74/2.48  fd_pseudo_cond:                         7
% 15.74/2.48  ac_symbols:                             0
% 15.74/2.48  
% 15.74/2.48  ------ Propositional Solver
% 15.74/2.48  
% 15.74/2.48  prop_solver_calls:                      30
% 15.74/2.48  prop_fast_solver_calls:                 1990
% 15.74/2.48  smt_solver_calls:                       0
% 15.74/2.48  smt_fast_solver_calls:                  0
% 15.74/2.48  prop_num_of_clauses:                    18280
% 15.74/2.48  prop_preprocess_simplified:             38943
% 15.74/2.48  prop_fo_subsumed:                       2
% 15.74/2.48  prop_solver_time:                       0.
% 15.74/2.48  smt_solver_time:                        0.
% 15.74/2.48  smt_fast_solver_time:                   0.
% 15.74/2.48  prop_fast_solver_time:                  0.
% 15.74/2.48  prop_unsat_core_time:                   0.001
% 15.74/2.48  
% 15.74/2.48  ------ QBF
% 15.74/2.48  
% 15.74/2.48  qbf_q_res:                              0
% 15.74/2.48  qbf_num_tautologies:                    0
% 15.74/2.48  qbf_prep_cycles:                        0
% 15.74/2.48  
% 15.74/2.48  ------ BMC1
% 15.74/2.48  
% 15.74/2.48  bmc1_current_bound:                     -1
% 15.74/2.48  bmc1_last_solved_bound:                 -1
% 15.74/2.48  bmc1_unsat_core_size:                   -1
% 15.74/2.48  bmc1_unsat_core_parents_size:           -1
% 15.74/2.48  bmc1_merge_next_fun:                    0
% 15.74/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.74/2.48  
% 15.74/2.48  ------ Instantiation
% 15.74/2.48  
% 15.74/2.48  inst_num_of_clauses:                    4595
% 15.74/2.48  inst_num_in_passive:                    2601
% 15.74/2.48  inst_num_in_active:                     976
% 15.74/2.48  inst_num_in_unprocessed:                1019
% 15.74/2.49  inst_num_of_loops:                      1320
% 15.74/2.49  inst_num_of_learning_restarts:          0
% 15.74/2.49  inst_num_moves_active_passive:          343
% 15.74/2.49  inst_lit_activity:                      0
% 15.74/2.49  inst_lit_activity_moves:                0
% 15.74/2.49  inst_num_tautologies:                   0
% 15.74/2.49  inst_num_prop_implied:                  0
% 15.74/2.49  inst_num_existing_simplified:           0
% 15.74/2.49  inst_num_eq_res_simplified:             0
% 15.74/2.49  inst_num_child_elim:                    0
% 15.74/2.49  inst_num_of_dismatching_blockings:      7198
% 15.74/2.49  inst_num_of_non_proper_insts:           5880
% 15.74/2.49  inst_num_of_duplicates:                 0
% 15.74/2.49  inst_inst_num_from_inst_to_res:         0
% 15.74/2.49  inst_dismatching_checking_time:         0.
% 15.74/2.49  
% 15.74/2.49  ------ Resolution
% 15.74/2.49  
% 15.74/2.49  res_num_of_clauses:                     0
% 15.74/2.49  res_num_in_passive:                     0
% 15.74/2.49  res_num_in_active:                      0
% 15.74/2.49  res_num_of_loops:                       180
% 15.74/2.49  res_forward_subset_subsumed:            634
% 15.74/2.49  res_backward_subset_subsumed:           2
% 15.74/2.49  res_forward_subsumed:                   0
% 15.74/2.49  res_backward_subsumed:                  0
% 15.74/2.49  res_forward_subsumption_resolution:     0
% 15.74/2.49  res_backward_subsumption_resolution:    0
% 15.74/2.49  res_clause_to_clause_subsumption:       4419
% 15.74/2.49  res_orphan_elimination:                 0
% 15.74/2.49  res_tautology_del:                      196
% 15.74/2.49  res_num_eq_res_simplified:              0
% 15.74/2.49  res_num_sel_changes:                    0
% 15.74/2.49  res_moves_from_active_to_pass:          0
% 15.74/2.49  
% 15.74/2.49  ------ Superposition
% 15.74/2.49  
% 15.74/2.49  sup_time_total:                         0.
% 15.74/2.49  sup_time_generating:                    0.
% 15.74/2.49  sup_time_sim_full:                      0.
% 15.74/2.49  sup_time_sim_immed:                     0.
% 15.74/2.49  
% 15.74/2.49  sup_num_of_clauses:                     861
% 15.74/2.49  sup_num_in_active:                      97
% 15.74/2.49  sup_num_in_passive:                     764
% 15.74/2.49  sup_num_of_loops:                       262
% 15.74/2.49  sup_fw_superposition:                   944
% 15.74/2.49  sup_bw_superposition:                   1992
% 15.74/2.49  sup_immediate_simplified:               1596
% 15.74/2.49  sup_given_eliminated:                   97
% 15.74/2.49  comparisons_done:                       0
% 15.74/2.49  comparisons_avoided:                    0
% 15.74/2.49  
% 15.74/2.49  ------ Simplifications
% 15.74/2.49  
% 15.74/2.49  
% 15.74/2.49  sim_fw_subset_subsumed:                 62
% 15.74/2.49  sim_bw_subset_subsumed:                 0
% 15.74/2.49  sim_fw_subsumed:                        311
% 15.74/2.49  sim_bw_subsumed:                        5
% 15.74/2.49  sim_fw_subsumption_res:                 3
% 15.74/2.49  sim_bw_subsumption_res:                 2
% 15.74/2.49  sim_tautology_del:                      6
% 15.74/2.49  sim_eq_tautology_del:                   255
% 15.74/2.49  sim_eq_res_simp:                        2
% 15.74/2.49  sim_fw_demodulated:                     28
% 15.74/2.49  sim_bw_demodulated:                     1008
% 15.74/2.49  sim_light_normalised:                   767
% 15.74/2.49  sim_joinable_taut:                      0
% 15.74/2.49  sim_joinable_simp:                      0
% 15.74/2.49  sim_ac_normalised:                      0
% 15.74/2.49  sim_smt_subsumption:                    0
% 15.74/2.49  
%------------------------------------------------------------------------------
