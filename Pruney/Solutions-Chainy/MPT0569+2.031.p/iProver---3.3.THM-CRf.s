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
% DateTime   : Thu Dec  3 11:47:32 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 332 expanded)
%              Number of clauses        :   53 (  80 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  367 (1155 expanded)
%              Number of equality atoms :  128 ( 310 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
        | k1_xboole_0 != k10_relat_1(sK7,sK6) )
      & ( r1_xboole_0(k2_relat_1(sK7),sK6)
        | k1_xboole_0 = k10_relat_1(sK7,sK6) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 != k10_relat_1(sK7,sK6) )
    & ( r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 = k10_relat_1(sK7,sK6) )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f43,f44])).

fof(f74,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f28])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
        & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
            & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f76])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f77])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f78])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f80])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f81])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f51,f82])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f80])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f60,f82,f83])).

fof(f88,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(equality_resolution,[],[f86])).

fof(f75,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1162,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1163,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1152,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,sK6)
    | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1161,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_312,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_313,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_1149,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(sK5(X0,X1,sK7),X1) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_1147,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1164,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2466,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1164])).

cnf(c_2759,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r1_xboole_0(k2_relat_1(sK7),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1149,c_2466])).

cnf(c_2898,plain,
    ( k10_relat_1(sK7,X0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_2759])).

cnf(c_12697,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1152,c_2898])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1154,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_280,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_281,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK7,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_293,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_281,c_10])).

cnf(c_1151,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK7,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_2381,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK4(sK7,X0),k10_relat_1(sK7,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1151])).

cnf(c_23417,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK4(sK7,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12697,c_2381])).

cnf(c_4,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1159,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3378,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1159])).

cnf(c_24522,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23417,c_3378])).

cnf(c_24526,plain,
    ( r2_hidden(sK0(X0,k2_relat_1(sK7)),sK6) != iProver_top
    | r1_xboole_0(X0,k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1163,c_24522])).

cnf(c_25753,plain,
    ( r1_xboole_0(sK6,k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_24526])).

cnf(c_1344,plain,
    ( ~ r2_hidden(sK0(X0,X1),X0)
    | ~ r2_hidden(sK0(X0,X1),X2)
    | ~ r1_xboole_0(X2,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_15639,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),X0)
    | ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | ~ r1_xboole_0(X0,k2_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_17336,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6)
    | ~ r1_xboole_0(sK6,k2_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_15639])).

cnf(c_17337,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) != iProver_top
    | r1_xboole_0(sK6,k2_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17336])).

cnf(c_18,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_165,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_403,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k2_relat_1(sK7) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_165])).

cnf(c_404,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6)
    | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_405,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_393,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k2_relat_1(sK7) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_165])).

cnf(c_394,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_395,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25753,c_17337,c_12697,c_405,c_395])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:52:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.08/1.55  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/1.55  
% 7.08/1.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.08/1.55  
% 7.08/1.55  ------  iProver source info
% 7.08/1.55  
% 7.08/1.55  git: date: 2020-06-30 10:37:57 +0100
% 7.08/1.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.08/1.55  git: non_committed_changes: false
% 7.08/1.55  git: last_make_outside_of_git: false
% 7.08/1.55  
% 7.08/1.55  ------ 
% 7.08/1.55  
% 7.08/1.55  ------ Input Options
% 7.08/1.55  
% 7.08/1.55  --out_options                           all
% 7.08/1.55  --tptp_safe_out                         true
% 7.08/1.55  --problem_path                          ""
% 7.08/1.55  --include_path                          ""
% 7.08/1.55  --clausifier                            res/vclausify_rel
% 7.08/1.55  --clausifier_options                    --mode clausify
% 7.08/1.55  --stdin                                 false
% 7.08/1.55  --stats_out                             all
% 7.08/1.55  
% 7.08/1.55  ------ General Options
% 7.08/1.55  
% 7.08/1.55  --fof                                   false
% 7.08/1.55  --time_out_real                         305.
% 7.08/1.55  --time_out_virtual                      -1.
% 7.08/1.55  --symbol_type_check                     false
% 7.08/1.55  --clausify_out                          false
% 7.08/1.55  --sig_cnt_out                           false
% 7.08/1.55  --trig_cnt_out                          false
% 7.08/1.55  --trig_cnt_out_tolerance                1.
% 7.08/1.55  --trig_cnt_out_sk_spl                   false
% 7.08/1.55  --abstr_cl_out                          false
% 7.08/1.55  
% 7.08/1.55  ------ Global Options
% 7.08/1.55  
% 7.08/1.55  --schedule                              default
% 7.08/1.55  --add_important_lit                     false
% 7.08/1.55  --prop_solver_per_cl                    1000
% 7.08/1.55  --min_unsat_core                        false
% 7.08/1.55  --soft_assumptions                      false
% 7.08/1.55  --soft_lemma_size                       3
% 7.08/1.55  --prop_impl_unit_size                   0
% 7.08/1.55  --prop_impl_unit                        []
% 7.08/1.55  --share_sel_clauses                     true
% 7.08/1.55  --reset_solvers                         false
% 7.08/1.55  --bc_imp_inh                            [conj_cone]
% 7.08/1.55  --conj_cone_tolerance                   3.
% 7.08/1.55  --extra_neg_conj                        none
% 7.08/1.55  --large_theory_mode                     true
% 7.08/1.55  --prolific_symb_bound                   200
% 7.08/1.55  --lt_threshold                          2000
% 7.08/1.55  --clause_weak_htbl                      true
% 7.08/1.55  --gc_record_bc_elim                     false
% 7.08/1.55  
% 7.08/1.55  ------ Preprocessing Options
% 7.08/1.55  
% 7.08/1.55  --preprocessing_flag                    true
% 7.08/1.55  --time_out_prep_mult                    0.1
% 7.08/1.55  --splitting_mode                        input
% 7.08/1.55  --splitting_grd                         true
% 7.08/1.55  --splitting_cvd                         false
% 7.08/1.55  --splitting_cvd_svl                     false
% 7.08/1.55  --splitting_nvd                         32
% 7.08/1.55  --sub_typing                            true
% 7.08/1.55  --prep_gs_sim                           true
% 7.08/1.55  --prep_unflatten                        true
% 7.08/1.55  --prep_res_sim                          true
% 7.08/1.55  --prep_upred                            true
% 7.08/1.55  --prep_sem_filter                       exhaustive
% 7.08/1.55  --prep_sem_filter_out                   false
% 7.08/1.55  --pred_elim                             true
% 7.08/1.55  --res_sim_input                         true
% 7.08/1.55  --eq_ax_congr_red                       true
% 7.08/1.55  --pure_diseq_elim                       true
% 7.08/1.55  --brand_transform                       false
% 7.08/1.55  --non_eq_to_eq                          false
% 7.08/1.55  --prep_def_merge                        true
% 7.08/1.55  --prep_def_merge_prop_impl              false
% 7.08/1.55  --prep_def_merge_mbd                    true
% 7.08/1.55  --prep_def_merge_tr_red                 false
% 7.08/1.55  --prep_def_merge_tr_cl                  false
% 7.08/1.55  --smt_preprocessing                     true
% 7.08/1.55  --smt_ac_axioms                         fast
% 7.08/1.55  --preprocessed_out                      false
% 7.08/1.55  --preprocessed_stats                    false
% 7.08/1.55  
% 7.08/1.55  ------ Abstraction refinement Options
% 7.08/1.55  
% 7.08/1.55  --abstr_ref                             []
% 7.08/1.55  --abstr_ref_prep                        false
% 7.08/1.55  --abstr_ref_until_sat                   false
% 7.08/1.55  --abstr_ref_sig_restrict                funpre
% 7.08/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 7.08/1.55  --abstr_ref_under                       []
% 7.08/1.55  
% 7.08/1.55  ------ SAT Options
% 7.08/1.55  
% 7.08/1.55  --sat_mode                              false
% 7.08/1.55  --sat_fm_restart_options                ""
% 7.08/1.55  --sat_gr_def                            false
% 7.08/1.55  --sat_epr_types                         true
% 7.08/1.55  --sat_non_cyclic_types                  false
% 7.08/1.55  --sat_finite_models                     false
% 7.08/1.55  --sat_fm_lemmas                         false
% 7.08/1.55  --sat_fm_prep                           false
% 7.08/1.55  --sat_fm_uc_incr                        true
% 7.08/1.55  --sat_out_model                         small
% 7.08/1.55  --sat_out_clauses                       false
% 7.08/1.55  
% 7.08/1.55  ------ QBF Options
% 7.08/1.55  
% 7.08/1.55  --qbf_mode                              false
% 7.08/1.55  --qbf_elim_univ                         false
% 7.08/1.55  --qbf_dom_inst                          none
% 7.08/1.55  --qbf_dom_pre_inst                      false
% 7.08/1.55  --qbf_sk_in                             false
% 7.08/1.55  --qbf_pred_elim                         true
% 7.08/1.55  --qbf_split                             512
% 7.08/1.55  
% 7.08/1.55  ------ BMC1 Options
% 7.08/1.55  
% 7.08/1.55  --bmc1_incremental                      false
% 7.08/1.55  --bmc1_axioms                           reachable_all
% 7.08/1.55  --bmc1_min_bound                        0
% 7.08/1.55  --bmc1_max_bound                        -1
% 7.08/1.55  --bmc1_max_bound_default                -1
% 7.08/1.55  --bmc1_symbol_reachability              true
% 7.08/1.55  --bmc1_property_lemmas                  false
% 7.08/1.55  --bmc1_k_induction                      false
% 7.08/1.55  --bmc1_non_equiv_states                 false
% 7.08/1.55  --bmc1_deadlock                         false
% 7.08/1.55  --bmc1_ucm                              false
% 7.08/1.55  --bmc1_add_unsat_core                   none
% 7.08/1.55  --bmc1_unsat_core_children              false
% 7.08/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 7.08/1.55  --bmc1_out_stat                         full
% 7.08/1.55  --bmc1_ground_init                      false
% 7.08/1.55  --bmc1_pre_inst_next_state              false
% 7.08/1.55  --bmc1_pre_inst_state                   false
% 7.08/1.55  --bmc1_pre_inst_reach_state             false
% 7.08/1.55  --bmc1_out_unsat_core                   false
% 7.08/1.55  --bmc1_aig_witness_out                  false
% 7.08/1.55  --bmc1_verbose                          false
% 7.08/1.55  --bmc1_dump_clauses_tptp                false
% 7.08/1.55  --bmc1_dump_unsat_core_tptp             false
% 7.08/1.55  --bmc1_dump_file                        -
% 7.08/1.55  --bmc1_ucm_expand_uc_limit              128
% 7.08/1.55  --bmc1_ucm_n_expand_iterations          6
% 7.08/1.55  --bmc1_ucm_extend_mode                  1
% 7.08/1.55  --bmc1_ucm_init_mode                    2
% 7.08/1.55  --bmc1_ucm_cone_mode                    none
% 7.08/1.55  --bmc1_ucm_reduced_relation_type        0
% 7.08/1.55  --bmc1_ucm_relax_model                  4
% 7.08/1.55  --bmc1_ucm_full_tr_after_sat            true
% 7.08/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 7.08/1.55  --bmc1_ucm_layered_model                none
% 7.08/1.55  --bmc1_ucm_max_lemma_size               10
% 7.08/1.55  
% 7.08/1.55  ------ AIG Options
% 7.08/1.55  
% 7.08/1.55  --aig_mode                              false
% 7.08/1.55  
% 7.08/1.55  ------ Instantiation Options
% 7.08/1.55  
% 7.08/1.55  --instantiation_flag                    true
% 7.08/1.55  --inst_sos_flag                         false
% 7.08/1.55  --inst_sos_phase                        true
% 7.08/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.08/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.08/1.55  --inst_lit_sel_side                     num_symb
% 7.08/1.55  --inst_solver_per_active                1400
% 7.08/1.55  --inst_solver_calls_frac                1.
% 7.08/1.55  --inst_passive_queue_type               priority_queues
% 7.08/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.08/1.55  --inst_passive_queues_freq              [25;2]
% 7.08/1.55  --inst_dismatching                      true
% 7.08/1.55  --inst_eager_unprocessed_to_passive     true
% 7.08/1.55  --inst_prop_sim_given                   true
% 7.08/1.55  --inst_prop_sim_new                     false
% 7.08/1.55  --inst_subs_new                         false
% 7.08/1.55  --inst_eq_res_simp                      false
% 7.08/1.55  --inst_subs_given                       false
% 7.08/1.55  --inst_orphan_elimination               true
% 7.08/1.55  --inst_learning_loop_flag               true
% 7.08/1.55  --inst_learning_start                   3000
% 7.08/1.55  --inst_learning_factor                  2
% 7.08/1.55  --inst_start_prop_sim_after_learn       3
% 7.08/1.55  --inst_sel_renew                        solver
% 7.08/1.55  --inst_lit_activity_flag                true
% 7.08/1.55  --inst_restr_to_given                   false
% 7.08/1.55  --inst_activity_threshold               500
% 7.08/1.55  --inst_out_proof                        true
% 7.08/1.55  
% 7.08/1.55  ------ Resolution Options
% 7.08/1.55  
% 7.08/1.55  --resolution_flag                       true
% 7.08/1.55  --res_lit_sel                           adaptive
% 7.08/1.55  --res_lit_sel_side                      none
% 7.08/1.55  --res_ordering                          kbo
% 7.08/1.55  --res_to_prop_solver                    active
% 7.08/1.55  --res_prop_simpl_new                    false
% 7.08/1.55  --res_prop_simpl_given                  true
% 7.08/1.55  --res_passive_queue_type                priority_queues
% 7.08/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.08/1.55  --res_passive_queues_freq               [15;5]
% 7.08/1.55  --res_forward_subs                      full
% 7.08/1.55  --res_backward_subs                     full
% 7.08/1.55  --res_forward_subs_resolution           true
% 7.08/1.55  --res_backward_subs_resolution          true
% 7.08/1.55  --res_orphan_elimination                true
% 7.08/1.55  --res_time_limit                        2.
% 7.08/1.55  --res_out_proof                         true
% 7.08/1.55  
% 7.08/1.55  ------ Superposition Options
% 7.08/1.55  
% 7.08/1.55  --superposition_flag                    true
% 7.08/1.55  --sup_passive_queue_type                priority_queues
% 7.08/1.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.08/1.55  --sup_passive_queues_freq               [8;1;4]
% 7.08/1.55  --demod_completeness_check              fast
% 7.08/1.55  --demod_use_ground                      true
% 7.08/1.55  --sup_to_prop_solver                    passive
% 7.08/1.55  --sup_prop_simpl_new                    true
% 7.08/1.55  --sup_prop_simpl_given                  true
% 7.08/1.55  --sup_fun_splitting                     false
% 7.08/1.55  --sup_smt_interval                      50000
% 7.08/1.55  
% 7.08/1.55  ------ Superposition Simplification Setup
% 7.08/1.55  
% 7.08/1.55  --sup_indices_passive                   []
% 7.08/1.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 7.08/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.55  --sup_full_bw                           [BwDemod]
% 7.08/1.55  --sup_immed_triv                        [TrivRules]
% 7.08/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.08/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.55  --sup_immed_bw_main                     []
% 7.08/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 7.08/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.55  
% 7.08/1.55  ------ Combination Options
% 7.08/1.55  
% 7.08/1.55  --comb_res_mult                         3
% 7.08/1.55  --comb_sup_mult                         2
% 7.08/1.55  --comb_inst_mult                        10
% 7.08/1.55  
% 7.08/1.55  ------ Debug Options
% 7.08/1.55  
% 7.08/1.55  --dbg_backtrace                         false
% 7.08/1.55  --dbg_dump_prop_clauses                 false
% 7.08/1.55  --dbg_dump_prop_clauses_file            -
% 7.08/1.55  --dbg_out_stat                          false
% 7.08/1.55  ------ Parsing...
% 7.08/1.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.08/1.55  
% 7.08/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.08/1.55  
% 7.08/1.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.08/1.55  
% 7.08/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.08/1.55  ------ Proving...
% 7.08/1.55  ------ Problem Properties 
% 7.08/1.55  
% 7.08/1.55  
% 7.08/1.55  clauses                                 19
% 7.08/1.55  conjectures                             2
% 7.08/1.55  EPR                                     1
% 7.08/1.55  Horn                                    13
% 7.08/1.55  unary                                   2
% 7.08/1.55  binary                                  12
% 7.08/1.55  lits                                    41
% 7.08/1.55  lits eq                                 7
% 7.08/1.55  fd_pure                                 0
% 7.08/1.55  fd_pseudo                               0
% 7.08/1.55  fd_cond                                 1
% 7.08/1.55  fd_pseudo_cond                          3
% 7.08/1.55  AC symbols                              0
% 7.08/1.55  
% 7.08/1.55  ------ Schedule dynamic 5 is on 
% 7.08/1.55  
% 7.08/1.55  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.08/1.55  
% 7.08/1.55  
% 7.08/1.55  ------ 
% 7.08/1.55  Current options:
% 7.08/1.55  ------ 
% 7.08/1.55  
% 7.08/1.55  ------ Input Options
% 7.08/1.55  
% 7.08/1.55  --out_options                           all
% 7.08/1.55  --tptp_safe_out                         true
% 7.08/1.55  --problem_path                          ""
% 7.08/1.55  --include_path                          ""
% 7.08/1.55  --clausifier                            res/vclausify_rel
% 7.08/1.55  --clausifier_options                    --mode clausify
% 7.08/1.55  --stdin                                 false
% 7.08/1.55  --stats_out                             all
% 7.08/1.55  
% 7.08/1.55  ------ General Options
% 7.08/1.55  
% 7.08/1.55  --fof                                   false
% 7.08/1.55  --time_out_real                         305.
% 7.08/1.55  --time_out_virtual                      -1.
% 7.08/1.55  --symbol_type_check                     false
% 7.08/1.55  --clausify_out                          false
% 7.08/1.55  --sig_cnt_out                           false
% 7.08/1.55  --trig_cnt_out                          false
% 7.08/1.55  --trig_cnt_out_tolerance                1.
% 7.08/1.55  --trig_cnt_out_sk_spl                   false
% 7.08/1.55  --abstr_cl_out                          false
% 7.08/1.55  
% 7.08/1.55  ------ Global Options
% 7.08/1.55  
% 7.08/1.55  --schedule                              default
% 7.08/1.55  --add_important_lit                     false
% 7.08/1.55  --prop_solver_per_cl                    1000
% 7.08/1.55  --min_unsat_core                        false
% 7.08/1.55  --soft_assumptions                      false
% 7.08/1.55  --soft_lemma_size                       3
% 7.08/1.55  --prop_impl_unit_size                   0
% 7.08/1.55  --prop_impl_unit                        []
% 7.08/1.55  --share_sel_clauses                     true
% 7.08/1.55  --reset_solvers                         false
% 7.08/1.55  --bc_imp_inh                            [conj_cone]
% 7.08/1.55  --conj_cone_tolerance                   3.
% 7.08/1.55  --extra_neg_conj                        none
% 7.08/1.55  --large_theory_mode                     true
% 7.08/1.55  --prolific_symb_bound                   200
% 7.08/1.55  --lt_threshold                          2000
% 7.08/1.55  --clause_weak_htbl                      true
% 7.08/1.55  --gc_record_bc_elim                     false
% 7.08/1.55  
% 7.08/1.55  ------ Preprocessing Options
% 7.08/1.55  
% 7.08/1.55  --preprocessing_flag                    true
% 7.08/1.55  --time_out_prep_mult                    0.1
% 7.08/1.55  --splitting_mode                        input
% 7.08/1.55  --splitting_grd                         true
% 7.08/1.55  --splitting_cvd                         false
% 7.08/1.55  --splitting_cvd_svl                     false
% 7.08/1.55  --splitting_nvd                         32
% 7.08/1.55  --sub_typing                            true
% 7.08/1.55  --prep_gs_sim                           true
% 7.08/1.55  --prep_unflatten                        true
% 7.08/1.55  --prep_res_sim                          true
% 7.08/1.55  --prep_upred                            true
% 7.08/1.55  --prep_sem_filter                       exhaustive
% 7.08/1.55  --prep_sem_filter_out                   false
% 7.08/1.55  --pred_elim                             true
% 7.08/1.55  --res_sim_input                         true
% 7.08/1.55  --eq_ax_congr_red                       true
% 7.08/1.55  --pure_diseq_elim                       true
% 7.08/1.55  --brand_transform                       false
% 7.08/1.55  --non_eq_to_eq                          false
% 7.08/1.55  --prep_def_merge                        true
% 7.08/1.55  --prep_def_merge_prop_impl              false
% 7.08/1.55  --prep_def_merge_mbd                    true
% 7.08/1.55  --prep_def_merge_tr_red                 false
% 7.08/1.55  --prep_def_merge_tr_cl                  false
% 7.08/1.55  --smt_preprocessing                     true
% 7.08/1.55  --smt_ac_axioms                         fast
% 7.08/1.55  --preprocessed_out                      false
% 7.08/1.55  --preprocessed_stats                    false
% 7.08/1.55  
% 7.08/1.55  ------ Abstraction refinement Options
% 7.08/1.55  
% 7.08/1.55  --abstr_ref                             []
% 7.08/1.55  --abstr_ref_prep                        false
% 7.08/1.55  --abstr_ref_until_sat                   false
% 7.08/1.55  --abstr_ref_sig_restrict                funpre
% 7.08/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 7.08/1.55  --abstr_ref_under                       []
% 7.08/1.55  
% 7.08/1.55  ------ SAT Options
% 7.08/1.55  
% 7.08/1.55  --sat_mode                              false
% 7.08/1.55  --sat_fm_restart_options                ""
% 7.08/1.55  --sat_gr_def                            false
% 7.08/1.55  --sat_epr_types                         true
% 7.08/1.55  --sat_non_cyclic_types                  false
% 7.08/1.55  --sat_finite_models                     false
% 7.08/1.55  --sat_fm_lemmas                         false
% 7.08/1.55  --sat_fm_prep                           false
% 7.08/1.55  --sat_fm_uc_incr                        true
% 7.08/1.55  --sat_out_model                         small
% 7.08/1.55  --sat_out_clauses                       false
% 7.08/1.55  
% 7.08/1.55  ------ QBF Options
% 7.08/1.55  
% 7.08/1.55  --qbf_mode                              false
% 7.08/1.55  --qbf_elim_univ                         false
% 7.08/1.55  --qbf_dom_inst                          none
% 7.08/1.55  --qbf_dom_pre_inst                      false
% 7.08/1.55  --qbf_sk_in                             false
% 7.08/1.55  --qbf_pred_elim                         true
% 7.08/1.55  --qbf_split                             512
% 7.08/1.55  
% 7.08/1.55  ------ BMC1 Options
% 7.08/1.55  
% 7.08/1.55  --bmc1_incremental                      false
% 7.08/1.55  --bmc1_axioms                           reachable_all
% 7.08/1.55  --bmc1_min_bound                        0
% 7.08/1.55  --bmc1_max_bound                        -1
% 7.08/1.55  --bmc1_max_bound_default                -1
% 7.08/1.55  --bmc1_symbol_reachability              true
% 7.08/1.55  --bmc1_property_lemmas                  false
% 7.08/1.55  --bmc1_k_induction                      false
% 7.08/1.55  --bmc1_non_equiv_states                 false
% 7.08/1.55  --bmc1_deadlock                         false
% 7.08/1.55  --bmc1_ucm                              false
% 7.08/1.55  --bmc1_add_unsat_core                   none
% 7.08/1.55  --bmc1_unsat_core_children              false
% 7.08/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 7.08/1.55  --bmc1_out_stat                         full
% 7.08/1.55  --bmc1_ground_init                      false
% 7.08/1.55  --bmc1_pre_inst_next_state              false
% 7.08/1.55  --bmc1_pre_inst_state                   false
% 7.08/1.55  --bmc1_pre_inst_reach_state             false
% 7.08/1.55  --bmc1_out_unsat_core                   false
% 7.08/1.55  --bmc1_aig_witness_out                  false
% 7.08/1.55  --bmc1_verbose                          false
% 7.08/1.55  --bmc1_dump_clauses_tptp                false
% 7.08/1.55  --bmc1_dump_unsat_core_tptp             false
% 7.08/1.55  --bmc1_dump_file                        -
% 7.08/1.55  --bmc1_ucm_expand_uc_limit              128
% 7.08/1.55  --bmc1_ucm_n_expand_iterations          6
% 7.08/1.55  --bmc1_ucm_extend_mode                  1
% 7.08/1.55  --bmc1_ucm_init_mode                    2
% 7.08/1.55  --bmc1_ucm_cone_mode                    none
% 7.08/1.55  --bmc1_ucm_reduced_relation_type        0
% 7.08/1.55  --bmc1_ucm_relax_model                  4
% 7.08/1.55  --bmc1_ucm_full_tr_after_sat            true
% 7.08/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 7.08/1.55  --bmc1_ucm_layered_model                none
% 7.08/1.55  --bmc1_ucm_max_lemma_size               10
% 7.08/1.55  
% 7.08/1.55  ------ AIG Options
% 7.08/1.55  
% 7.08/1.55  --aig_mode                              false
% 7.08/1.55  
% 7.08/1.55  ------ Instantiation Options
% 7.08/1.55  
% 7.08/1.55  --instantiation_flag                    true
% 7.08/1.55  --inst_sos_flag                         false
% 7.08/1.55  --inst_sos_phase                        true
% 7.08/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.08/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.08/1.55  --inst_lit_sel_side                     none
% 7.08/1.55  --inst_solver_per_active                1400
% 7.08/1.55  --inst_solver_calls_frac                1.
% 7.08/1.55  --inst_passive_queue_type               priority_queues
% 7.08/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.08/1.55  --inst_passive_queues_freq              [25;2]
% 7.08/1.55  --inst_dismatching                      true
% 7.08/1.55  --inst_eager_unprocessed_to_passive     true
% 7.08/1.55  --inst_prop_sim_given                   true
% 7.08/1.55  --inst_prop_sim_new                     false
% 7.08/1.55  --inst_subs_new                         false
% 7.08/1.55  --inst_eq_res_simp                      false
% 7.08/1.55  --inst_subs_given                       false
% 7.08/1.55  --inst_orphan_elimination               true
% 7.08/1.55  --inst_learning_loop_flag               true
% 7.08/1.55  --inst_learning_start                   3000
% 7.08/1.55  --inst_learning_factor                  2
% 7.08/1.55  --inst_start_prop_sim_after_learn       3
% 7.08/1.55  --inst_sel_renew                        solver
% 7.08/1.55  --inst_lit_activity_flag                true
% 7.08/1.55  --inst_restr_to_given                   false
% 7.08/1.55  --inst_activity_threshold               500
% 7.08/1.55  --inst_out_proof                        true
% 7.08/1.55  
% 7.08/1.55  ------ Resolution Options
% 7.08/1.55  
% 7.08/1.55  --resolution_flag                       false
% 7.08/1.55  --res_lit_sel                           adaptive
% 7.08/1.55  --res_lit_sel_side                      none
% 7.08/1.55  --res_ordering                          kbo
% 7.08/1.55  --res_to_prop_solver                    active
% 7.08/1.55  --res_prop_simpl_new                    false
% 7.08/1.55  --res_prop_simpl_given                  true
% 7.08/1.55  --res_passive_queue_type                priority_queues
% 7.08/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.08/1.55  --res_passive_queues_freq               [15;5]
% 7.08/1.55  --res_forward_subs                      full
% 7.08/1.55  --res_backward_subs                     full
% 7.08/1.55  --res_forward_subs_resolution           true
% 7.08/1.55  --res_backward_subs_resolution          true
% 7.08/1.55  --res_orphan_elimination                true
% 7.08/1.55  --res_time_limit                        2.
% 7.08/1.55  --res_out_proof                         true
% 7.08/1.55  
% 7.08/1.55  ------ Superposition Options
% 7.08/1.55  
% 7.08/1.55  --superposition_flag                    true
% 7.08/1.55  --sup_passive_queue_type                priority_queues
% 7.08/1.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.08/1.55  --sup_passive_queues_freq               [8;1;4]
% 7.08/1.55  --demod_completeness_check              fast
% 7.08/1.55  --demod_use_ground                      true
% 7.08/1.55  --sup_to_prop_solver                    passive
% 7.08/1.55  --sup_prop_simpl_new                    true
% 7.08/1.55  --sup_prop_simpl_given                  true
% 7.08/1.55  --sup_fun_splitting                     false
% 7.08/1.55  --sup_smt_interval                      50000
% 7.08/1.55  
% 7.08/1.55  ------ Superposition Simplification Setup
% 7.08/1.55  
% 7.08/1.55  --sup_indices_passive                   []
% 7.08/1.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 7.08/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.55  --sup_full_bw                           [BwDemod]
% 7.08/1.55  --sup_immed_triv                        [TrivRules]
% 7.08/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.08/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.55  --sup_immed_bw_main                     []
% 7.08/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 7.08/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.55  
% 7.08/1.55  ------ Combination Options
% 7.08/1.55  
% 7.08/1.55  --comb_res_mult                         3
% 7.08/1.55  --comb_sup_mult                         2
% 7.08/1.55  --comb_inst_mult                        10
% 7.08/1.55  
% 7.08/1.55  ------ Debug Options
% 7.08/1.55  
% 7.08/1.55  --dbg_backtrace                         false
% 7.08/1.55  --dbg_dump_prop_clauses                 false
% 7.08/1.55  --dbg_dump_prop_clauses_file            -
% 7.08/1.55  --dbg_out_stat                          false
% 7.08/1.55  
% 7.08/1.55  
% 7.08/1.55  
% 7.08/1.55  
% 7.08/1.55  ------ Proving...
% 7.08/1.55  
% 7.08/1.55  
% 7.08/1.55  % SZS status Theorem for theBenchmark.p
% 7.08/1.55  
% 7.08/1.55  % SZS output start CNFRefutation for theBenchmark.p
% 7.08/1.55  
% 7.08/1.55  fof(f1,axiom,(
% 7.08/1.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f19,plain,(
% 7.08/1.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.08/1.55    inference(rectify,[],[f1])).
% 7.08/1.55  
% 7.08/1.55  fof(f20,plain,(
% 7.08/1.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.08/1.55    inference(ennf_transformation,[],[f19])).
% 7.08/1.55  
% 7.08/1.55  fof(f26,plain,(
% 7.08/1.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.08/1.55    introduced(choice_axiom,[])).
% 7.08/1.55  
% 7.08/1.55  fof(f27,plain,(
% 7.08/1.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.08/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f26])).
% 7.08/1.55  
% 7.08/1.55  fof(f46,plain,(
% 7.08/1.55    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f27])).
% 7.08/1.55  
% 7.08/1.55  fof(f47,plain,(
% 7.08/1.55    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f27])).
% 7.08/1.55  
% 7.08/1.55  fof(f17,conjecture,(
% 7.08/1.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f18,negated_conjecture,(
% 7.08/1.55    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.08/1.55    inference(negated_conjecture,[],[f17])).
% 7.08/1.55  
% 7.08/1.55  fof(f25,plain,(
% 7.08/1.55    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 7.08/1.55    inference(ennf_transformation,[],[f18])).
% 7.08/1.55  
% 7.08/1.55  fof(f42,plain,(
% 7.08/1.55    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 7.08/1.55    inference(nnf_transformation,[],[f25])).
% 7.08/1.55  
% 7.08/1.55  fof(f43,plain,(
% 7.08/1.55    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.08/1.55    inference(flattening,[],[f42])).
% 7.08/1.55  
% 7.08/1.55  fof(f44,plain,(
% 7.08/1.55    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)) & (r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)) & v1_relat_1(sK7))),
% 7.08/1.55    introduced(choice_axiom,[])).
% 7.08/1.55  
% 7.08/1.55  fof(f45,plain,(
% 7.08/1.55    (~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)) & (r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)) & v1_relat_1(sK7)),
% 7.08/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f43,f44])).
% 7.08/1.55  
% 7.08/1.55  fof(f74,plain,(
% 7.08/1.55    r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)),
% 7.08/1.55    inference(cnf_transformation,[],[f45])).
% 7.08/1.55  
% 7.08/1.55  fof(f2,axiom,(
% 7.08/1.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f21,plain,(
% 7.08/1.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.08/1.55    inference(ennf_transformation,[],[f2])).
% 7.08/1.55  
% 7.08/1.55  fof(f28,plain,(
% 7.08/1.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.08/1.55    introduced(choice_axiom,[])).
% 7.08/1.55  
% 7.08/1.55  fof(f29,plain,(
% 7.08/1.55    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 7.08/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f28])).
% 7.08/1.55  
% 7.08/1.55  fof(f49,plain,(
% 7.08/1.55    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.08/1.55    inference(cnf_transformation,[],[f29])).
% 7.08/1.55  
% 7.08/1.55  fof(f15,axiom,(
% 7.08/1.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f22,plain,(
% 7.08/1.55    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.08/1.55    inference(ennf_transformation,[],[f15])).
% 7.08/1.55  
% 7.08/1.55  fof(f38,plain,(
% 7.08/1.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.08/1.55    inference(nnf_transformation,[],[f22])).
% 7.08/1.55  
% 7.08/1.55  fof(f39,plain,(
% 7.08/1.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.08/1.55    inference(rectify,[],[f38])).
% 7.08/1.55  
% 7.08/1.55  fof(f40,plain,(
% 7.08/1.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))))),
% 7.08/1.55    introduced(choice_axiom,[])).
% 7.08/1.55  
% 7.08/1.55  fof(f41,plain,(
% 7.08/1.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.08/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 7.08/1.55  
% 7.08/1.55  fof(f67,plain,(
% 7.08/1.55    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f41])).
% 7.08/1.55  
% 7.08/1.55  fof(f73,plain,(
% 7.08/1.55    v1_relat_1(sK7)),
% 7.08/1.55    inference(cnf_transformation,[],[f45])).
% 7.08/1.55  
% 7.08/1.55  fof(f69,plain,(
% 7.08/1.55    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f41])).
% 7.08/1.55  
% 7.08/1.55  fof(f48,plain,(
% 7.08/1.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f27])).
% 7.08/1.55  
% 7.08/1.55  fof(f14,axiom,(
% 7.08/1.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f32,plain,(
% 7.08/1.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.08/1.55    inference(nnf_transformation,[],[f14])).
% 7.08/1.55  
% 7.08/1.55  fof(f33,plain,(
% 7.08/1.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.08/1.55    inference(rectify,[],[f32])).
% 7.08/1.55  
% 7.08/1.55  fof(f36,plain,(
% 7.08/1.55    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 7.08/1.55    introduced(choice_axiom,[])).
% 7.08/1.55  
% 7.08/1.55  fof(f35,plain,(
% 7.08/1.55    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0))) )),
% 7.08/1.55    introduced(choice_axiom,[])).
% 7.08/1.55  
% 7.08/1.55  fof(f34,plain,(
% 7.08/1.55    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.08/1.55    introduced(choice_axiom,[])).
% 7.08/1.55  
% 7.08/1.55  fof(f37,plain,(
% 7.08/1.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.08/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).
% 7.08/1.55  
% 7.08/1.55  fof(f63,plain,(
% 7.08/1.55    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 7.08/1.55    inference(cnf_transformation,[],[f37])).
% 7.08/1.55  
% 7.08/1.55  fof(f90,plain,(
% 7.08/1.55    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 7.08/1.55    inference(equality_resolution,[],[f63])).
% 7.08/1.55  
% 7.08/1.55  fof(f70,plain,(
% 7.08/1.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f41])).
% 7.08/1.55  
% 7.08/1.55  fof(f64,plain,(
% 7.08/1.55    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 7.08/1.55    inference(cnf_transformation,[],[f37])).
% 7.08/1.55  
% 7.08/1.55  fof(f89,plain,(
% 7.08/1.55    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 7.08/1.55    inference(equality_resolution,[],[f64])).
% 7.08/1.55  
% 7.08/1.55  fof(f4,axiom,(
% 7.08/1.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f51,plain,(
% 7.08/1.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f4])).
% 7.08/1.55  
% 7.08/1.55  fof(f3,axiom,(
% 7.08/1.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f50,plain,(
% 7.08/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.08/1.55    inference(cnf_transformation,[],[f3])).
% 7.08/1.55  
% 7.08/1.55  fof(f13,axiom,(
% 7.08/1.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f62,plain,(
% 7.08/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.08/1.55    inference(cnf_transformation,[],[f13])).
% 7.08/1.55  
% 7.08/1.55  fof(f6,axiom,(
% 7.08/1.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f53,plain,(
% 7.08/1.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f6])).
% 7.08/1.55  
% 7.08/1.55  fof(f7,axiom,(
% 7.08/1.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f54,plain,(
% 7.08/1.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f7])).
% 7.08/1.55  
% 7.08/1.55  fof(f8,axiom,(
% 7.08/1.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f55,plain,(
% 7.08/1.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f8])).
% 7.08/1.55  
% 7.08/1.55  fof(f9,axiom,(
% 7.08/1.55    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f56,plain,(
% 7.08/1.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f9])).
% 7.08/1.55  
% 7.08/1.55  fof(f10,axiom,(
% 7.08/1.55    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f57,plain,(
% 7.08/1.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f10])).
% 7.08/1.55  
% 7.08/1.55  fof(f11,axiom,(
% 7.08/1.55    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f58,plain,(
% 7.08/1.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f11])).
% 7.08/1.55  
% 7.08/1.55  fof(f76,plain,(
% 7.08/1.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.08/1.55    inference(definition_unfolding,[],[f57,f58])).
% 7.08/1.55  
% 7.08/1.55  fof(f77,plain,(
% 7.08/1.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.08/1.55    inference(definition_unfolding,[],[f56,f76])).
% 7.08/1.55  
% 7.08/1.55  fof(f78,plain,(
% 7.08/1.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.08/1.55    inference(definition_unfolding,[],[f55,f77])).
% 7.08/1.55  
% 7.08/1.55  fof(f79,plain,(
% 7.08/1.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.08/1.55    inference(definition_unfolding,[],[f54,f78])).
% 7.08/1.55  
% 7.08/1.55  fof(f80,plain,(
% 7.08/1.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.08/1.55    inference(definition_unfolding,[],[f53,f79])).
% 7.08/1.55  
% 7.08/1.55  fof(f81,plain,(
% 7.08/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.08/1.55    inference(definition_unfolding,[],[f62,f80])).
% 7.08/1.55  
% 7.08/1.55  fof(f82,plain,(
% 7.08/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.08/1.55    inference(definition_unfolding,[],[f50,f81])).
% 7.08/1.55  
% 7.08/1.55  fof(f84,plain,(
% 7.08/1.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 7.08/1.55    inference(definition_unfolding,[],[f51,f82])).
% 7.08/1.55  
% 7.08/1.55  fof(f12,axiom,(
% 7.08/1.55    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f30,plain,(
% 7.08/1.55    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.08/1.55    inference(nnf_transformation,[],[f12])).
% 7.08/1.55  
% 7.08/1.55  fof(f31,plain,(
% 7.08/1.55    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.08/1.55    inference(flattening,[],[f30])).
% 7.08/1.55  
% 7.08/1.55  fof(f60,plain,(
% 7.08/1.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 7.08/1.55    inference(cnf_transformation,[],[f31])).
% 7.08/1.55  
% 7.08/1.55  fof(f5,axiom,(
% 7.08/1.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.55  
% 7.08/1.55  fof(f52,plain,(
% 7.08/1.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.08/1.55    inference(cnf_transformation,[],[f5])).
% 7.08/1.55  
% 7.08/1.55  fof(f83,plain,(
% 7.08/1.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.08/1.55    inference(definition_unfolding,[],[f52,f80])).
% 7.08/1.55  
% 7.08/1.55  fof(f86,plain,(
% 7.08/1.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) )),
% 7.08/1.55    inference(definition_unfolding,[],[f60,f82,f83])).
% 7.08/1.55  
% 7.08/1.55  fof(f88,plain,(
% 7.08/1.55    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) )),
% 7.08/1.55    inference(equality_resolution,[],[f86])).
% 7.08/1.55  
% 7.08/1.55  fof(f75,plain,(
% 7.08/1.55    ~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)),
% 7.08/1.55    inference(cnf_transformation,[],[f45])).
% 7.08/1.55  
% 7.08/1.55  cnf(c_2,plain,
% 7.08/1.55      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.08/1.55      inference(cnf_transformation,[],[f46]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1162,plain,
% 7.08/1.55      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.08/1.55      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1,plain,
% 7.08/1.55      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 7.08/1.55      inference(cnf_transformation,[],[f47]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1163,plain,
% 7.08/1.55      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 7.08/1.55      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_19,negated_conjecture,
% 7.08/1.55      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.08/1.55      | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
% 7.08/1.55      inference(cnf_transformation,[],[f74]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1152,plain,
% 7.08/1.55      ( k1_xboole_0 = k10_relat_1(sK7,sK6)
% 7.08/1.55      | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_3,plain,
% 7.08/1.55      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.08/1.55      inference(cnf_transformation,[],[f49]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1161,plain,
% 7.08/1.55      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_15,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.08/1.55      | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
% 7.08/1.55      | ~ v1_relat_1(X1) ),
% 7.08/1.55      inference(cnf_transformation,[],[f67]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_20,negated_conjecture,
% 7.08/1.55      ( v1_relat_1(sK7) ),
% 7.08/1.55      inference(cnf_transformation,[],[f73]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_312,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.08/1.55      | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
% 7.08/1.55      | sK7 != X1 ),
% 7.08/1.55      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_313,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
% 7.08/1.55      | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) ),
% 7.08/1.55      inference(unflattening,[status(thm)],[c_312]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1149,plain,
% 7.08/1.55      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.08/1.55      | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) = iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_13,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.08/1.55      | r2_hidden(sK5(X0,X2,X1),X2)
% 7.08/1.55      | ~ v1_relat_1(X1) ),
% 7.08/1.55      inference(cnf_transformation,[],[f69]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_336,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.08/1.55      | r2_hidden(sK5(X0,X2,X1),X2)
% 7.08/1.55      | sK7 != X1 ),
% 7.08/1.55      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_337,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
% 7.08/1.55      | r2_hidden(sK5(X0,X1,sK7),X1) ),
% 7.08/1.55      inference(unflattening,[status(thm)],[c_336]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1147,plain,
% 7.08/1.55      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.08/1.55      | r2_hidden(sK5(X0,X1,sK7),X1) = iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_0,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.08/1.55      inference(cnf_transformation,[],[f48]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1164,plain,
% 7.08/1.55      ( r2_hidden(X0,X1) != iProver_top
% 7.08/1.55      | r2_hidden(X0,X2) != iProver_top
% 7.08/1.55      | r1_xboole_0(X2,X1) != iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_2466,plain,
% 7.08/1.55      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.08/1.55      | r2_hidden(sK5(X0,X1,sK7),X2) != iProver_top
% 7.08/1.55      | r1_xboole_0(X2,X1) != iProver_top ),
% 7.08/1.55      inference(superposition,[status(thm)],[c_1147,c_1164]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_2759,plain,
% 7.08/1.55      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.08/1.55      | r1_xboole_0(k2_relat_1(sK7),X1) != iProver_top ),
% 7.08/1.55      inference(superposition,[status(thm)],[c_1149,c_2466]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_2898,plain,
% 7.08/1.55      ( k10_relat_1(sK7,X0) = k1_xboole_0
% 7.08/1.55      | r1_xboole_0(k2_relat_1(sK7),X0) != iProver_top ),
% 7.08/1.55      inference(superposition,[status(thm)],[c_1161,c_2759]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_12697,plain,
% 7.08/1.55      ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
% 7.08/1.55      inference(superposition,[status(thm)],[c_1152,c_2898]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_11,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.08/1.55      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
% 7.08/1.55      inference(cnf_transformation,[],[f90]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1154,plain,
% 7.08/1.55      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.08/1.55      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) = iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_12,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,X1)
% 7.08/1.55      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.08/1.55      | ~ r2_hidden(X0,k2_relat_1(X3))
% 7.08/1.55      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.08/1.55      | ~ v1_relat_1(X3) ),
% 7.08/1.55      inference(cnf_transformation,[],[f70]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_280,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,X1)
% 7.08/1.55      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.08/1.55      | ~ r2_hidden(X0,k2_relat_1(X3))
% 7.08/1.55      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.08/1.55      | sK7 != X3 ),
% 7.08/1.55      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_281,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,X1)
% 7.08/1.55      | r2_hidden(X2,k10_relat_1(sK7,X1))
% 7.08/1.55      | ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.08/1.55      | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
% 7.08/1.55      inference(unflattening,[status(thm)],[c_280]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_10,plain,
% 7.08/1.55      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 7.08/1.55      inference(cnf_transformation,[],[f89]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_293,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,X1)
% 7.08/1.55      | r2_hidden(X2,k10_relat_1(sK7,X1))
% 7.08/1.55      | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
% 7.08/1.55      inference(forward_subsumption_resolution,
% 7.08/1.55                [status(thm)],
% 7.08/1.55                [c_281,c_10]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1151,plain,
% 7.08/1.55      ( r2_hidden(X0,X1) != iProver_top
% 7.08/1.55      | r2_hidden(X2,k10_relat_1(sK7,X1)) = iProver_top
% 7.08/1.55      | r2_hidden(k4_tarski(X2,X0),sK7) != iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_2381,plain,
% 7.08/1.55      ( r2_hidden(X0,X1) != iProver_top
% 7.08/1.55      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 7.08/1.55      | r2_hidden(sK4(sK7,X0),k10_relat_1(sK7,X1)) = iProver_top ),
% 7.08/1.55      inference(superposition,[status(thm)],[c_1154,c_1151]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_23417,plain,
% 7.08/1.55      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 7.08/1.55      | r2_hidden(X0,sK6) != iProver_top
% 7.08/1.55      | r2_hidden(sK4(sK7,X0),k1_xboole_0) = iProver_top ),
% 7.08/1.55      inference(superposition,[status(thm)],[c_12697,c_2381]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_4,plain,
% 7.08/1.55      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
% 7.08/1.55      inference(cnf_transformation,[],[f84]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_6,plain,
% 7.08/1.55      ( ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
% 7.08/1.55      inference(cnf_transformation,[],[f88]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1159,plain,
% 7.08/1.55      ( r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_3378,plain,
% 7.08/1.55      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.08/1.55      inference(superposition,[status(thm)],[c_4,c_1159]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_24522,plain,
% 7.08/1.55      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 7.08/1.55      | r2_hidden(X0,sK6) != iProver_top ),
% 7.08/1.55      inference(forward_subsumption_resolution,
% 7.08/1.55                [status(thm)],
% 7.08/1.55                [c_23417,c_3378]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_24526,plain,
% 7.08/1.55      ( r2_hidden(sK0(X0,k2_relat_1(sK7)),sK6) != iProver_top
% 7.08/1.55      | r1_xboole_0(X0,k2_relat_1(sK7)) = iProver_top ),
% 7.08/1.55      inference(superposition,[status(thm)],[c_1163,c_24522]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_25753,plain,
% 7.08/1.55      ( r1_xboole_0(sK6,k2_relat_1(sK7)) = iProver_top ),
% 7.08/1.55      inference(superposition,[status(thm)],[c_1162,c_24526]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_1344,plain,
% 7.08/1.55      ( ~ r2_hidden(sK0(X0,X1),X0)
% 7.08/1.55      | ~ r2_hidden(sK0(X0,X1),X2)
% 7.08/1.55      | ~ r1_xboole_0(X2,X0) ),
% 7.08/1.55      inference(instantiation,[status(thm)],[c_0]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_15639,plain,
% 7.08/1.55      ( ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),X0)
% 7.08/1.55      | ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 7.08/1.55      | ~ r1_xboole_0(X0,k2_relat_1(sK7)) ),
% 7.08/1.55      inference(instantiation,[status(thm)],[c_1344]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_17336,plain,
% 7.08/1.55      ( ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 7.08/1.55      | ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6)
% 7.08/1.55      | ~ r1_xboole_0(sK6,k2_relat_1(sK7)) ),
% 7.08/1.55      inference(instantiation,[status(thm)],[c_15639]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_17337,plain,
% 7.08/1.55      ( r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) != iProver_top
% 7.08/1.55      | r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) != iProver_top
% 7.08/1.55      | r1_xboole_0(sK6,k2_relat_1(sK7)) != iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_17336]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_18,negated_conjecture,
% 7.08/1.55      ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.08/1.55      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 7.08/1.55      inference(cnf_transformation,[],[f75]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_165,plain,
% 7.08/1.55      ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.08/1.55      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 7.08/1.55      inference(prop_impl,[status(thm)],[c_18]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_403,plain,
% 7.08/1.55      ( r2_hidden(sK0(X0,X1),X1)
% 7.08/1.55      | k10_relat_1(sK7,sK6) != k1_xboole_0
% 7.08/1.55      | k2_relat_1(sK7) != X0
% 7.08/1.55      | sK6 != X1 ),
% 7.08/1.55      inference(resolution_lifted,[status(thm)],[c_1,c_165]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_404,plain,
% 7.08/1.55      ( r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6)
% 7.08/1.55      | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
% 7.08/1.55      inference(unflattening,[status(thm)],[c_403]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_405,plain,
% 7.08/1.55      ( k10_relat_1(sK7,sK6) != k1_xboole_0
% 7.08/1.55      | r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) = iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_393,plain,
% 7.08/1.55      ( r2_hidden(sK0(X0,X1),X0)
% 7.08/1.55      | k10_relat_1(sK7,sK6) != k1_xboole_0
% 7.08/1.55      | k2_relat_1(sK7) != X0
% 7.08/1.55      | sK6 != X1 ),
% 7.08/1.55      inference(resolution_lifted,[status(thm)],[c_2,c_165]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_394,plain,
% 7.08/1.55      ( r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 7.08/1.55      | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
% 7.08/1.55      inference(unflattening,[status(thm)],[c_393]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(c_395,plain,
% 7.08/1.55      ( k10_relat_1(sK7,sK6) != k1_xboole_0
% 7.08/1.55      | r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) = iProver_top ),
% 7.08/1.55      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 7.08/1.55  
% 7.08/1.55  cnf(contradiction,plain,
% 7.08/1.55      ( $false ),
% 7.08/1.55      inference(minisat,
% 7.08/1.55                [status(thm)],
% 7.08/1.55                [c_25753,c_17337,c_12697,c_405,c_395]) ).
% 7.08/1.55  
% 7.08/1.55  
% 7.08/1.55  % SZS output end CNFRefutation for theBenchmark.p
% 7.08/1.55  
% 7.08/1.55  ------                               Statistics
% 7.08/1.55  
% 7.08/1.55  ------ General
% 7.08/1.55  
% 7.08/1.55  abstr_ref_over_cycles:                  0
% 7.08/1.55  abstr_ref_under_cycles:                 0
% 7.08/1.55  gc_basic_clause_elim:                   0
% 7.08/1.55  forced_gc_time:                         0
% 7.08/1.55  parsing_time:                           0.005
% 7.08/1.55  unif_index_cands_time:                  0.
% 7.08/1.55  unif_index_add_time:                    0.
% 7.08/1.55  orderings_time:                         0.
% 7.08/1.55  out_proof_time:                         0.01
% 7.08/1.55  total_time:                             0.824
% 7.08/1.55  num_of_symbols:                         50
% 7.08/1.55  num_of_terms:                           23537
% 7.08/1.55  
% 7.08/1.55  ------ Preprocessing
% 7.08/1.55  
% 7.08/1.55  num_of_splits:                          0
% 7.08/1.55  num_of_split_atoms:                     0
% 7.08/1.55  num_of_reused_defs:                     0
% 7.08/1.55  num_eq_ax_congr_red:                    35
% 7.08/1.55  num_of_sem_filtered_clauses:            1
% 7.08/1.55  num_of_subtypes:                        0
% 7.08/1.55  monotx_restored_types:                  0
% 7.08/1.55  sat_num_of_epr_types:                   0
% 7.08/1.55  sat_num_of_non_cyclic_types:            0
% 7.08/1.55  sat_guarded_non_collapsed_types:        0
% 7.08/1.55  num_pure_diseq_elim:                    0
% 7.08/1.55  simp_replaced_by:                       0
% 7.08/1.55  res_preprocessed:                       102
% 7.08/1.55  prep_upred:                             0
% 7.08/1.55  prep_unflattend:                        25
% 7.08/1.55  smt_new_axioms:                         0
% 7.08/1.55  pred_elim_cands:                        2
% 7.08/1.55  pred_elim:                              1
% 7.08/1.55  pred_elim_cl:                           1
% 7.08/1.55  pred_elim_cycles:                       3
% 7.08/1.55  merged_defs:                            8
% 7.08/1.55  merged_defs_ncl:                        0
% 7.08/1.55  bin_hyper_res:                          8
% 7.08/1.55  prep_cycles:                            4
% 7.08/1.55  pred_elim_time:                         0.003
% 7.08/1.55  splitting_time:                         0.
% 7.08/1.55  sem_filter_time:                        0.
% 7.08/1.55  monotx_time:                            0.
% 7.08/1.55  subtype_inf_time:                       0.
% 7.08/1.55  
% 7.08/1.55  ------ Problem properties
% 7.08/1.55  
% 7.08/1.55  clauses:                                19
% 7.08/1.55  conjectures:                            2
% 7.08/1.55  epr:                                    1
% 7.08/1.55  horn:                                   13
% 7.08/1.55  ground:                                 2
% 7.08/1.55  unary:                                  2
% 7.08/1.55  binary:                                 12
% 7.08/1.55  lits:                                   41
% 7.08/1.55  lits_eq:                                7
% 7.08/1.55  fd_pure:                                0
% 7.08/1.55  fd_pseudo:                              0
% 7.08/1.55  fd_cond:                                1
% 7.08/1.55  fd_pseudo_cond:                         3
% 7.08/1.55  ac_symbols:                             0
% 7.08/1.55  
% 7.08/1.55  ------ Propositional Solver
% 7.08/1.55  
% 7.08/1.55  prop_solver_calls:                      29
% 7.08/1.55  prop_fast_solver_calls:                 1028
% 7.08/1.55  smt_solver_calls:                       0
% 7.08/1.55  smt_fast_solver_calls:                  0
% 7.08/1.55  prop_num_of_clauses:                    10734
% 7.08/1.55  prop_preprocess_simplified:             13278
% 7.08/1.55  prop_fo_subsumed:                       4
% 7.08/1.55  prop_solver_time:                       0.
% 7.08/1.55  smt_solver_time:                        0.
% 7.08/1.55  smt_fast_solver_time:                   0.
% 7.08/1.55  prop_fast_solver_time:                  0.
% 7.08/1.55  prop_unsat_core_time:                   0.
% 7.08/1.55  
% 7.08/1.55  ------ QBF
% 7.08/1.55  
% 7.08/1.55  qbf_q_res:                              0
% 7.08/1.55  qbf_num_tautologies:                    0
% 7.08/1.55  qbf_prep_cycles:                        0
% 7.08/1.55  
% 7.08/1.55  ------ BMC1
% 7.08/1.55  
% 7.08/1.55  bmc1_current_bound:                     -1
% 7.08/1.55  bmc1_last_solved_bound:                 -1
% 7.08/1.55  bmc1_unsat_core_size:                   -1
% 7.08/1.55  bmc1_unsat_core_parents_size:           -1
% 7.08/1.55  bmc1_merge_next_fun:                    0
% 7.08/1.55  bmc1_unsat_core_clauses_time:           0.
% 7.08/1.55  
% 7.08/1.55  ------ Instantiation
% 7.08/1.55  
% 7.08/1.55  inst_num_of_clauses:                    1919
% 7.08/1.55  inst_num_in_passive:                    326
% 7.08/1.55  inst_num_in_active:                     918
% 7.08/1.55  inst_num_in_unprocessed:                675
% 7.08/1.55  inst_num_of_loops:                      1130
% 7.08/1.55  inst_num_of_learning_restarts:          0
% 7.08/1.55  inst_num_moves_active_passive:          209
% 7.08/1.55  inst_lit_activity:                      0
% 7.08/1.55  inst_lit_activity_moves:                0
% 7.08/1.55  inst_num_tautologies:                   0
% 7.08/1.55  inst_num_prop_implied:                  0
% 7.08/1.55  inst_num_existing_simplified:           0
% 7.08/1.55  inst_num_eq_res_simplified:             0
% 7.08/1.55  inst_num_child_elim:                    0
% 7.08/1.55  inst_num_of_dismatching_blockings:      824
% 7.08/1.55  inst_num_of_non_proper_insts:           1232
% 7.08/1.55  inst_num_of_duplicates:                 0
% 7.08/1.55  inst_inst_num_from_inst_to_res:         0
% 7.08/1.55  inst_dismatching_checking_time:         0.
% 7.08/1.55  
% 7.08/1.55  ------ Resolution
% 7.08/1.55  
% 7.08/1.55  res_num_of_clauses:                     0
% 7.08/1.55  res_num_in_passive:                     0
% 7.08/1.55  res_num_in_active:                      0
% 7.08/1.55  res_num_of_loops:                       106
% 7.08/1.55  res_forward_subset_subsumed:            55
% 7.08/1.55  res_backward_subset_subsumed:           0
% 7.08/1.55  res_forward_subsumed:                   0
% 7.08/1.55  res_backward_subsumed:                  0
% 7.08/1.55  res_forward_subsumption_resolution:     1
% 7.08/1.55  res_backward_subsumption_resolution:    0
% 7.08/1.55  res_clause_to_clause_subsumption:       17697
% 7.08/1.55  res_orphan_elimination:                 0
% 7.08/1.55  res_tautology_del:                      96
% 7.08/1.55  res_num_eq_res_simplified:              0
% 7.08/1.55  res_num_sel_changes:                    0
% 7.08/1.55  res_moves_from_active_to_pass:          0
% 7.08/1.55  
% 7.08/1.55  ------ Superposition
% 7.08/1.55  
% 7.08/1.55  sup_time_total:                         0.
% 7.08/1.55  sup_time_generating:                    0.
% 7.08/1.55  sup_time_sim_full:                      0.
% 7.08/1.55  sup_time_sim_immed:                     0.
% 7.08/1.55  
% 7.08/1.55  sup_num_of_clauses:                     1175
% 7.08/1.55  sup_num_in_active:                      215
% 7.08/1.55  sup_num_in_passive:                     960
% 7.08/1.55  sup_num_of_loops:                       224
% 7.08/1.55  sup_fw_superposition:                   1328
% 7.08/1.55  sup_bw_superposition:                   633
% 7.08/1.55  sup_immediate_simplified:               479
% 7.08/1.55  sup_given_eliminated:                   8
% 7.08/1.55  comparisons_done:                       0
% 7.08/1.55  comparisons_avoided:                    0
% 7.08/1.55  
% 7.08/1.55  ------ Simplifications
% 7.08/1.55  
% 7.08/1.55  
% 7.08/1.55  sim_fw_subset_subsumed:                 91
% 7.08/1.55  sim_bw_subset_subsumed:                 0
% 7.08/1.55  sim_fw_subsumed:                        229
% 7.08/1.55  sim_bw_subsumed:                        2
% 7.08/1.55  sim_fw_subsumption_res:                 1
% 7.08/1.55  sim_bw_subsumption_res:                 0
% 7.08/1.55  sim_tautology_del:                      6
% 7.08/1.55  sim_eq_tautology_del:                   13
% 7.08/1.55  sim_eq_res_simp:                        1
% 7.08/1.55  sim_fw_demodulated:                     3
% 7.08/1.55  sim_bw_demodulated:                     34
% 7.08/1.55  sim_light_normalised:                   263
% 7.08/1.55  sim_joinable_taut:                      0
% 7.08/1.55  sim_joinable_simp:                      0
% 7.08/1.55  sim_ac_normalised:                      0
% 7.08/1.55  sim_smt_subsumption:                    0
% 7.08/1.55  
%------------------------------------------------------------------------------
