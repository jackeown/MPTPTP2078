%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:29 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 458 expanded)
%              Number of clauses        :   72 ( 170 expanded)
%              Number of leaves         :   25 ( 115 expanded)
%              Depth                    :   19
%              Number of atoms          :  460 (1559 expanded)
%              Number of equality atoms :  123 ( 499 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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
    inference(rectify,[],[f1])).

fof(f15,plain,(
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

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f68,f53])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

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
   => ( ( ~ r1_xboole_0(k2_relat_1(sK10),sK9)
        | k1_xboole_0 != k10_relat_1(sK10,sK9) )
      & ( r1_xboole_0(k2_relat_1(sK10),sK9)
        | k1_xboole_0 = k10_relat_1(sK10,sK9) )
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK10),sK9)
      | k1_xboole_0 != k10_relat_1(sK10,sK9) )
    & ( r1_xboole_0(k2_relat_1(sK10),sK9)
      | k1_xboole_0 = k10_relat_1(sK10,sK9) )
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f43,f44])).

fof(f72,plain,
    ( r1_xboole_0(k2_relat_1(sK10),sK9)
    | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

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
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f36,f35,f34])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f19])).

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
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
        & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
            & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK10),sK9)
    | k1_xboole_0 != k10_relat_1(sK10,sK9) ),
    inference(cnf_transformation,[],[f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
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

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f30,f29,f28])).

fof(f56,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f60,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_462,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_13046,plain,
    ( sK7(sK10,sK0(k2_relat_1(sK10),sK9)) = sK7(sK10,sK0(k2_relat_1(sK10),sK9)) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_465,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9212,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
    | X0 != sK7(sK10,sK0(k2_relat_1(sK10),sK9))
    | X1 != k10_relat_1(sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_13045,plain,
    ( r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),X0)
    | ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
    | X0 != k10_relat_1(sK10,sK9)
    | sK7(sK10,sK0(k2_relat_1(sK10),sK9)) != sK7(sK10,sK0(k2_relat_1(sK10),sK9)) ),
    inference(instantiation,[status(thm)],[c_9212])).

cnf(c_13048,plain,
    ( ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
    | r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k1_xboole_0)
    | sK7(sK10,sK0(k2_relat_1(sK10),sK9)) != sK7(sK10,sK0(k2_relat_1(sK10),sK9))
    | k1_xboole_0 != k10_relat_1(sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_13045])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9220,plain,
    ( ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),X0)
    | ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
    | ~ r1_xboole_0(k10_relat_1(sK10,sK9),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_9222,plain,
    ( ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
    | ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k1_xboole_0)
    | ~ r1_xboole_0(k10_relat_1(sK10,sK9),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9220])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_463,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK10),sK9)
    | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2218,plain,
    ( r1_xboole_0(k2_relat_1(sK10),sK9)
    | X0 != k10_relat_1(sK10,sK9)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_463,c_25])).

cnf(c_3017,plain,
    ( r1_xboole_0(k2_relat_1(sK10),sK9)
    | ~ v1_relat_1(sK10)
    | k1_xboole_0 = k10_relat_1(sK10,k1_setfam_1(k2_tarski(k2_relat_1(sK10),sK9))) ),
    inference(resolution,[status(thm)],[c_21,c_2218])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3369,plain,
    ( r1_xboole_0(k2_relat_1(sK10),sK9)
    | k1_xboole_0 = k10_relat_1(sK10,k1_setfam_1(k2_tarski(k2_relat_1(sK10),sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3017,c_26])).

cnf(c_3387,plain,
    ( r1_xboole_0(k2_relat_1(sK10),sK9)
    | X0 != k10_relat_1(sK10,k1_setfam_1(k2_tarski(k2_relat_1(sK10),sK9)))
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_3369,c_463])).

cnf(c_2220,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_463,c_462])).

cnf(c_2550,plain,
    ( r1_xboole_0(k2_relat_1(sK10),sK9)
    | k10_relat_1(sK10,sK9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2220,c_25])).

cnf(c_2564,plain,
    ( r1_xboole_0(k2_relat_1(sK10),sK9)
    | X0 != k1_xboole_0
    | k10_relat_1(sK10,sK9) = X0 ),
    inference(resolution,[status(thm)],[c_2550,c_463])).

cnf(c_3723,plain,
    ( r1_xboole_0(k2_relat_1(sK10),sK9)
    | k10_relat_1(sK10,k1_setfam_1(k2_tarski(k2_relat_1(sK10),sK9))) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
    inference(resolution,[status(thm)],[c_3387,c_2564])).

cnf(c_2655,plain,
    ( r1_xboole_0(k2_relat_1(sK10),sK9)
    | k10_relat_1(sK10,sK9) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
    inference(resolution,[status(thm)],[c_2564,c_2218])).

cnf(c_483,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_1399,plain,
    ( k10_relat_1(sK10,sK9) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_1400,plain,
    ( k10_relat_1(sK10,sK9) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK10,sK9)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_2658,plain,
    ( k10_relat_1(sK10,sK9) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2655,c_483,c_1400])).

cnf(c_996,plain,
    ( k1_xboole_0 = k10_relat_1(sK10,sK9)
    | r1_xboole_0(k2_relat_1(sK10),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( r2_hidden(sK5(X0,X1),X1)
    | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1004,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK5(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1013,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1012,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1337,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1013,c_1012])).

cnf(c_2925,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1004,c_1337])).

cnf(c_22,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2956,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2925,c_22])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1015,plain,
    ( r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3054,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2956,c_1015])).

cnf(c_3624,plain,
    ( k10_relat_1(sK10,sK9) = k1_xboole_0
    | k1_setfam_1(k2_tarski(k2_relat_1(sK10),sK9)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_996,c_3054])).

cnf(c_995,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_998,plain,
    ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1432,plain,
    ( k10_relat_1(sK10,k1_setfam_1(k2_tarski(k2_relat_1(sK10),X0))) = k10_relat_1(sK10,X0) ),
    inference(superposition,[status(thm)],[c_995,c_998])).

cnf(c_3747,plain,
    ( k10_relat_1(sK10,sK9) = k1_xboole_0
    | k10_relat_1(sK10,k1_xboole_0) = k10_relat_1(sK10,sK9) ),
    inference(superposition,[status(thm)],[c_3624,c_1432])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK8(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1001,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK8(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2166,plain,
    ( r2_hidden(X0,k10_relat_1(X1,k1_xboole_0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_1337])).

cnf(c_3058,plain,
    ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2956,c_2166])).

cnf(c_3525,plain,
    ( k10_relat_1(sK10,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_995,c_3058])).

cnf(c_3750,plain,
    ( k10_relat_1(sK10,sK9) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3747,c_3525])).

cnf(c_3760,plain,
    ( k1_xboole_0 = k10_relat_1(sK10,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3723,c_483,c_1400,c_3750])).

cnf(c_24,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK10),sK9)
    | k1_xboole_0 != k10_relat_1(sK10,sK9) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3766,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK10),sK9) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3760,c_24])).

cnf(c_464,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3179,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK10,sK9))
    | ~ r1_xboole_0(X1,k1_xboole_0)
    | r1_xboole_0(k2_relat_1(sK10),sK9)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_464,c_2550])).

cnf(c_3535,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK10,sK9))
    | r1_xboole_0(k2_relat_1(sK10),sK9)
    | X0 != X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3179,c_5])).

cnf(c_3582,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK10,sK9))
    | r1_xboole_0(k2_relat_1(sK10),sK9) ),
    inference(resolution,[status(thm)],[c_3535,c_462])).

cnf(c_3787,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK10,sK9)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3766,c_3582])).

cnf(c_4116,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK10,sK9)) ),
    inference(resolution,[status(thm)],[c_3787,c_6])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6340,plain,
    ( r1_xboole_0(k10_relat_1(sK10,sK9),X0) ),
    inference(resolution,[status(thm)],[c_4116,c_2])).

cnf(c_6342,plain,
    ( r1_xboole_0(k10_relat_1(sK10,sK9),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6340])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1698,plain,
    ( r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,X0))
    | ~ r2_hidden(k4_tarski(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),sK0(k2_relat_1(sK10),sK9)),sK10)
    | ~ r2_hidden(sK0(k2_relat_1(sK10),sK9),X0)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_6163,plain,
    ( r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
    | ~ r2_hidden(k4_tarski(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),sK0(k2_relat_1(sK10),sK9)),sK10)
    | ~ r2_hidden(sK0(k2_relat_1(sK10),sK9),sK9)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1331,plain,
    ( r2_hidden(k4_tarski(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),sK0(k2_relat_1(sK10),sK9)),sK10)
    | ~ r2_hidden(sK0(k2_relat_1(sK10),sK9),k2_relat_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1237,plain,
    ( r2_hidden(sK0(k2_relat_1(sK10),sK9),k2_relat_1(sK10))
    | r1_xboole_0(k2_relat_1(sK10),sK9) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1234,plain,
    ( r2_hidden(sK0(k2_relat_1(sK10),sK9),sK9)
    | r1_xboole_0(k2_relat_1(sK10),sK9) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13046,c_13048,c_9222,c_6342,c_6163,c_3750,c_2658,c_1331,c_1237,c_1234,c_24,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.96/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/0.99  
% 3.96/0.99  ------  iProver source info
% 3.96/0.99  
% 3.96/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.96/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/0.99  git: non_committed_changes: false
% 3.96/0.99  git: last_make_outside_of_git: false
% 3.96/0.99  
% 3.96/0.99  ------ 
% 3.96/0.99  ------ Parsing...
% 3.96/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/0.99  ------ Proving...
% 3.96/0.99  ------ Problem Properties 
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  clauses                                 26
% 3.96/0.99  conjectures                             3
% 3.96/0.99  EPR                                     3
% 3.96/0.99  Horn                                    19
% 3.96/0.99  unary                                   4
% 3.96/0.99  binary                                  10
% 3.96/0.99  lits                                    65
% 3.96/0.99  lits eq                                 10
% 3.96/0.99  fd_pure                                 0
% 3.96/0.99  fd_pseudo                               0
% 3.96/0.99  fd_cond                                 0
% 3.96/0.99  fd_pseudo_cond                          5
% 3.96/0.99  AC symbols                              0
% 3.96/0.99  
% 3.96/0.99  ------ Input Options Time Limit: Unbounded
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  ------ 
% 3.96/0.99  Current options:
% 3.96/0.99  ------ 
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  ------ Proving...
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  % SZS status Theorem for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  fof(f1,axiom,(
% 3.96/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f13,plain,(
% 3.96/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.96/0.99    inference(rectify,[],[f1])).
% 3.96/0.99  
% 3.96/0.99  fof(f15,plain,(
% 3.96/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.96/0.99    inference(ennf_transformation,[],[f13])).
% 3.96/0.99  
% 3.96/0.99  fof(f22,plain,(
% 3.96/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f23,plain,(
% 3.96/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f22])).
% 3.96/0.99  
% 3.96/0.99  fof(f48,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f23])).
% 3.96/0.99  
% 3.96/0.99  fof(f9,axiom,(
% 3.96/0.99    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f20,plain,(
% 3.96/0.99    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f9])).
% 3.96/0.99  
% 3.96/0.99  fof(f68,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f20])).
% 3.96/0.99  
% 3.96/0.99  fof(f5,axiom,(
% 3.96/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f53,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.96/0.99    inference(cnf_transformation,[],[f5])).
% 3.96/0.99  
% 3.96/0.99  fof(f76,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(definition_unfolding,[],[f68,f53])).
% 3.96/0.99  
% 3.96/0.99  fof(f11,conjecture,(
% 3.96/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f12,negated_conjecture,(
% 3.96/0.99    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.96/0.99    inference(negated_conjecture,[],[f11])).
% 3.96/0.99  
% 3.96/0.99  fof(f21,plain,(
% 3.96/0.99    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f12])).
% 3.96/0.99  
% 3.96/0.99  fof(f42,plain,(
% 3.96/0.99    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.96/0.99    inference(nnf_transformation,[],[f21])).
% 3.96/0.99  
% 3.96/0.99  fof(f43,plain,(
% 3.96/0.99    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.96/0.99    inference(flattening,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f44,plain,(
% 3.96/0.99    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK10),sK9) | k1_xboole_0 != k10_relat_1(sK10,sK9)) & (r1_xboole_0(k2_relat_1(sK10),sK9) | k1_xboole_0 = k10_relat_1(sK10,sK9)) & v1_relat_1(sK10))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f45,plain,(
% 3.96/0.99    (~r1_xboole_0(k2_relat_1(sK10),sK9) | k1_xboole_0 != k10_relat_1(sK10,sK9)) & (r1_xboole_0(k2_relat_1(sK10),sK9) | k1_xboole_0 = k10_relat_1(sK10,sK9)) & v1_relat_1(sK10)),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f43,f44])).
% 3.96/0.99  
% 3.96/0.99  fof(f72,plain,(
% 3.96/0.99    r1_xboole_0(k2_relat_1(sK10),sK9) | k1_xboole_0 = k10_relat_1(sK10,sK9)),
% 3.96/0.99    inference(cnf_transformation,[],[f45])).
% 3.96/0.99  
% 3.96/0.99  fof(f71,plain,(
% 3.96/0.99    v1_relat_1(sK10)),
% 3.96/0.99    inference(cnf_transformation,[],[f45])).
% 3.96/0.99  
% 3.96/0.99  fof(f7,axiom,(
% 3.96/0.99    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f32,plain,(
% 3.96/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.96/0.99    inference(nnf_transformation,[],[f7])).
% 3.96/0.99  
% 3.96/0.99  fof(f33,plain,(
% 3.96/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.96/0.99    inference(rectify,[],[f32])).
% 3.96/0.99  
% 3.96/0.99  fof(f36,plain,(
% 3.96/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f35,plain,(
% 3.96/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0))) )),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f34,plain,(
% 3.96/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f37,plain,(
% 3.96/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f36,f35,f34])).
% 3.96/0.99  
% 3.96/0.99  fof(f62,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f37])).
% 3.96/0.99  
% 3.96/0.99  fof(f3,axiom,(
% 3.96/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f51,plain,(
% 3.96/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f3])).
% 3.96/0.99  
% 3.96/0.99  fof(f4,axiom,(
% 3.96/0.99    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f17,plain,(
% 3.96/0.99    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f4])).
% 3.96/0.99  
% 3.96/0.99  fof(f52,plain,(
% 3.96/0.99    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f17])).
% 3.96/0.99  
% 3.96/0.99  fof(f10,axiom,(
% 3.96/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f70,plain,(
% 3.96/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.96/0.99    inference(cnf_transformation,[],[f10])).
% 3.96/0.99  
% 3.96/0.99  fof(f2,axiom,(
% 3.96/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f14,plain,(
% 3.96/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.96/0.99    inference(rectify,[],[f2])).
% 3.96/0.99  
% 3.96/0.99  fof(f16,plain,(
% 3.96/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.96/0.99    inference(ennf_transformation,[],[f14])).
% 3.96/0.99  
% 3.96/0.99  fof(f24,plain,(
% 3.96/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f25,plain,(
% 3.96/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).
% 3.96/0.99  
% 3.96/0.99  fof(f50,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.96/0.99    inference(cnf_transformation,[],[f25])).
% 3.96/0.99  
% 3.96/0.99  fof(f74,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.96/0.99    inference(definition_unfolding,[],[f50,f53])).
% 3.96/0.99  
% 3.96/0.99  fof(f8,axiom,(
% 3.96/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f19,plain,(
% 3.96/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.96/0.99    inference(ennf_transformation,[],[f8])).
% 3.96/0.99  
% 3.96/0.99  fof(f38,plain,(
% 3.96/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.96/0.99    inference(nnf_transformation,[],[f19])).
% 3.96/0.99  
% 3.96/0.99  fof(f39,plain,(
% 3.96/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.96/0.99    inference(rectify,[],[f38])).
% 3.96/0.99  
% 3.96/0.99  fof(f40,plain,(
% 3.96/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2))))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f41,plain,(
% 3.96/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).
% 3.96/0.99  
% 3.96/0.99  fof(f66,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f41])).
% 3.96/0.99  
% 3.96/0.99  fof(f73,plain,(
% 3.96/0.99    ~r1_xboole_0(k2_relat_1(sK10),sK9) | k1_xboole_0 != k10_relat_1(sK10,sK9)),
% 3.96/0.99    inference(cnf_transformation,[],[f45])).
% 3.96/0.99  
% 3.96/0.99  fof(f46,plain,(
% 3.96/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f23])).
% 3.96/0.99  
% 3.96/0.99  fof(f6,axiom,(
% 3.96/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 3.96/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f18,plain,(
% 3.96/0.99    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 3.96/0.99    inference(ennf_transformation,[],[f6])).
% 3.96/0.99  
% 3.96/0.99  fof(f26,plain,(
% 3.96/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.96/0.99    inference(nnf_transformation,[],[f18])).
% 3.96/0.99  
% 3.96/0.99  fof(f27,plain,(
% 3.96/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.96/0.99    inference(rectify,[],[f26])).
% 3.96/0.99  
% 3.96/0.99  fof(f30,plain,(
% 3.96/0.99    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f29,plain,(
% 3.96/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0)))) )),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f28,plain,(
% 3.96/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f31,plain,(
% 3.96/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f30,f29,f28])).
% 3.96/0.99  
% 3.96/0.99  fof(f56,plain,(
% 3.96/0.99    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f31])).
% 3.96/0.99  
% 3.96/0.99  fof(f77,plain,(
% 3.96/0.99    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 3.96/0.99    inference(equality_resolution,[],[f56])).
% 3.96/0.99  
% 3.96/0.99  fof(f60,plain,(
% 3.96/0.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.96/0.99    inference(cnf_transformation,[],[f37])).
% 3.96/0.99  
% 3.96/0.99  fof(f81,plain,(
% 3.96/0.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.96/0.99    inference(equality_resolution,[],[f60])).
% 3.96/0.99  
% 3.96/0.99  fof(f47,plain,(
% 3.96/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f23])).
% 3.96/0.99  
% 3.96/0.99  cnf(c_462,plain,( X0 = X0 ),theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_13046,plain,
% 3.96/0.99      ( sK7(sK10,sK0(k2_relat_1(sK10),sK9)) = sK7(sK10,sK0(k2_relat_1(sK10),sK9)) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_462]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_465,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.96/0.99      theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9212,plain,
% 3.96/0.99      ( r2_hidden(X0,X1)
% 3.96/0.99      | ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
% 3.96/0.99      | X0 != sK7(sK10,sK0(k2_relat_1(sK10),sK9))
% 3.96/0.99      | X1 != k10_relat_1(sK10,sK9) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_465]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_13045,plain,
% 3.96/0.99      ( r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),X0)
% 3.96/0.99      | ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
% 3.96/0.99      | X0 != k10_relat_1(sK10,sK9)
% 3.96/0.99      | sK7(sK10,sK0(k2_relat_1(sK10),sK9)) != sK7(sK10,sK0(k2_relat_1(sK10),sK9)) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_9212]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_13048,plain,
% 3.96/0.99      ( ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
% 3.96/0.99      | r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k1_xboole_0)
% 3.96/0.99      | sK7(sK10,sK0(k2_relat_1(sK10),sK9)) != sK7(sK10,sK0(k2_relat_1(sK10),sK9))
% 3.96/0.99      | k1_xboole_0 != k10_relat_1(sK10,sK9) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_13045]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_0,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9220,plain,
% 3.96/0.99      ( ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),X0)
% 3.96/0.99      | ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
% 3.96/0.99      | ~ r1_xboole_0(k10_relat_1(sK10,sK9),X0) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9222,plain,
% 3.96/0.99      ( ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
% 3.96/0.99      | ~ r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k1_xboole_0)
% 3.96/0.99      | ~ r1_xboole_0(k10_relat_1(sK10,sK9),k1_xboole_0) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_9220]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_21,plain,
% 3.96/0.99      ( ~ v1_relat_1(X0)
% 3.96/0.99      | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_463,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_25,negated_conjecture,
% 3.96/0.99      ( r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
% 3.96/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2218,plain,
% 3.96/0.99      ( r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | X0 != k10_relat_1(sK10,sK9)
% 3.96/0.99      | k1_xboole_0 = X0 ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_463,c_25]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3017,plain,
% 3.96/0.99      ( r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | ~ v1_relat_1(sK10)
% 3.96/0.99      | k1_xboole_0 = k10_relat_1(sK10,k1_setfam_1(k2_tarski(k2_relat_1(sK10),sK9))) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_21,c_2218]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_26,negated_conjecture,
% 3.96/0.99      ( v1_relat_1(sK10) ),
% 3.96/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3369,plain,
% 3.96/0.99      ( r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | k1_xboole_0 = k10_relat_1(sK10,k1_setfam_1(k2_tarski(k2_relat_1(sK10),sK9))) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3017,c_26]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3387,plain,
% 3.96/0.99      ( r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | X0 != k10_relat_1(sK10,k1_setfam_1(k2_tarski(k2_relat_1(sK10),sK9)))
% 3.96/0.99      | k1_xboole_0 = X0 ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_3369,c_463]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2220,plain,
% 3.96/0.99      ( X0 != X1 | X1 = X0 ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_463,c_462]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2550,plain,
% 3.96/0.99      ( r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | k10_relat_1(sK10,sK9) = k1_xboole_0 ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_2220,c_25]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2564,plain,
% 3.96/0.99      ( r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | X0 != k1_xboole_0
% 3.96/0.99      | k10_relat_1(sK10,sK9) = X0 ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_2550,c_463]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3723,plain,
% 3.96/0.99      ( r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | k10_relat_1(sK10,k1_setfam_1(k2_tarski(k2_relat_1(sK10),sK9))) != k1_xboole_0
% 3.96/0.99      | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_3387,c_2564]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2655,plain,
% 3.96/0.99      ( r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | k10_relat_1(sK10,sK9) != k1_xboole_0
% 3.96/0.99      | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_2564,c_2218]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_483,plain,
% 3.96/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_462]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1399,plain,
% 3.96/0.99      ( k10_relat_1(sK10,sK9) != X0
% 3.96/0.99      | k1_xboole_0 != X0
% 3.96/0.99      | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_463]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1400,plain,
% 3.96/0.99      ( k10_relat_1(sK10,sK9) != k1_xboole_0
% 3.96/0.99      | k1_xboole_0 = k10_relat_1(sK10,sK9)
% 3.96/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1399]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2658,plain,
% 3.96/0.99      ( k10_relat_1(sK10,sK9) != k1_xboole_0
% 3.96/0.99      | k1_xboole_0 = k10_relat_1(sK10,sK9) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_2655,c_483,c_1400]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_996,plain,
% 3.96/0.99      ( k1_xboole_0 = k10_relat_1(sK10,sK9)
% 3.96/0.99      | r1_xboole_0(k2_relat_1(sK10),sK9) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_14,plain,
% 3.96/0.99      ( r2_hidden(sK5(X0,X1),X1)
% 3.96/0.99      | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
% 3.96/0.99      | k2_relat_1(X0) = X1 ),
% 3.96/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1004,plain,
% 3.96/0.99      ( k2_relat_1(X0) = X1
% 3.96/0.99      | r2_hidden(sK5(X0,X1),X1) = iProver_top
% 3.96/0.99      | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_5,plain,
% 3.96/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1013,plain,
% 3.96/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k1_tarski(X0),X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1012,plain,
% 3.96/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.96/0.99      | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1337,plain,
% 3.96/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1013,c_1012]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2925,plain,
% 3.96/0.99      ( k2_relat_1(k1_xboole_0) = X0
% 3.96/0.99      | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1004,c_1337]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_22,plain,
% 3.96/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.96/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2956,plain,
% 3.96/0.99      ( k1_xboole_0 = X0
% 3.96/0.99      | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_2925,c_22]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 3.96/0.99      | ~ r1_xboole_0(X1,X2) ),
% 3.96/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1015,plain,
% 3.96/0.99      ( r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top
% 3.96/0.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3054,plain,
% 3.96/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 3.96/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_2956,c_1015]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3624,plain,
% 3.96/0.99      ( k10_relat_1(sK10,sK9) = k1_xboole_0
% 3.96/0.99      | k1_setfam_1(k2_tarski(k2_relat_1(sK10),sK9)) = k1_xboole_0 ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_996,c_3054]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_995,plain,
% 3.96/0.99      ( v1_relat_1(sK10) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_998,plain,
% 3.96/0.99      ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 3.96/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1432,plain,
% 3.96/0.99      ( k10_relat_1(sK10,k1_setfam_1(k2_tarski(k2_relat_1(sK10),X0))) = k10_relat_1(sK10,X0) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_995,c_998]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3747,plain,
% 3.96/0.99      ( k10_relat_1(sK10,sK9) = k1_xboole_0
% 3.96/0.99      | k10_relat_1(sK10,k1_xboole_0) = k10_relat_1(sK10,sK9) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_3624,c_1432]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_18,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.96/0.99      | r2_hidden(sK8(X0,X2,X1),X2)
% 3.96/0.99      | ~ v1_relat_1(X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1001,plain,
% 3.96/0.99      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.96/0.99      | r2_hidden(sK8(X0,X2,X1),X2) = iProver_top
% 3.96/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2166,plain,
% 3.96/0.99      ( r2_hidden(X0,k10_relat_1(X1,k1_xboole_0)) != iProver_top
% 3.96/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1001,c_1337]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3058,plain,
% 3.96/0.99      ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.96/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_2956,c_2166]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3525,plain,
% 3.96/0.99      ( k10_relat_1(sK10,k1_xboole_0) = k1_xboole_0 ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_995,c_3058]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3750,plain,
% 3.96/0.99      ( k10_relat_1(sK10,sK9) = k1_xboole_0 ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_3747,c_3525]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3760,plain,
% 3.96/0.99      ( k1_xboole_0 = k10_relat_1(sK10,sK9) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3723,c_483,c_1400,c_3750]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_24,negated_conjecture,
% 3.96/0.99      ( ~ r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | k1_xboole_0 != k10_relat_1(sK10,sK9) ),
% 3.96/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3766,plain,
% 3.96/0.99      ( ~ r1_xboole_0(k2_relat_1(sK10),sK9) ),
% 3.96/0.99      inference(backward_subsumption_resolution,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3760,c_24]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_464,plain,
% 3.96/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.96/0.99      theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3179,plain,
% 3.96/0.99      ( r1_xboole_0(X0,k10_relat_1(sK10,sK9))
% 3.96/0.99      | ~ r1_xboole_0(X1,k1_xboole_0)
% 3.96/0.99      | r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | X0 != X1 ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_464,c_2550]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3535,plain,
% 3.96/0.99      ( r1_xboole_0(X0,k10_relat_1(sK10,sK9))
% 3.96/0.99      | r1_xboole_0(k2_relat_1(sK10),sK9)
% 3.96/0.99      | X0 != X1 ),
% 3.96/0.99      inference(forward_subsumption_resolution,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3179,c_5]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3582,plain,
% 3.96/0.99      ( r1_xboole_0(X0,k10_relat_1(sK10,sK9))
% 3.96/0.99      | r1_xboole_0(k2_relat_1(sK10),sK9) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_3535,c_462]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3787,plain,
% 3.96/0.99      ( r1_xboole_0(X0,k10_relat_1(sK10,sK9)) ),
% 3.96/0.99      inference(backward_subsumption_resolution,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3766,c_3582]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4116,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,k10_relat_1(sK10,sK9)) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_3787,c_6]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2,plain,
% 3.96/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6340,plain,
% 3.96/0.99      ( r1_xboole_0(k10_relat_1(sK10,sK9),X0) ),
% 3.96/0.99      inference(resolution,[status(thm)],[c_4116,c_2]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6342,plain,
% 3.96/0.99      ( r1_xboole_0(k10_relat_1(sK10,sK9),k1_xboole_0) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_6340]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,X1)
% 3.96/0.99      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.96/0.99      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.96/0.99      | ~ v1_relat_1(X3) ),
% 3.96/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1698,plain,
% 3.96/0.99      ( r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,X0))
% 3.96/0.99      | ~ r2_hidden(k4_tarski(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),sK0(k2_relat_1(sK10),sK9)),sK10)
% 3.96/0.99      | ~ r2_hidden(sK0(k2_relat_1(sK10),sK9),X0)
% 3.96/0.99      | ~ v1_relat_1(sK10) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6163,plain,
% 3.96/0.99      ( r2_hidden(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),k10_relat_1(sK10,sK9))
% 3.96/0.99      | ~ r2_hidden(k4_tarski(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),sK0(k2_relat_1(sK10),sK9)),sK10)
% 3.96/0.99      | ~ r2_hidden(sK0(k2_relat_1(sK10),sK9),sK9)
% 3.96/0.99      | ~ v1_relat_1(sK10) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1698]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_16,plain,
% 3.96/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.96/0.99      | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1331,plain,
% 3.96/0.99      ( r2_hidden(k4_tarski(sK7(sK10,sK0(k2_relat_1(sK10),sK9)),sK0(k2_relat_1(sK10),sK9)),sK10)
% 3.96/0.99      | ~ r2_hidden(sK0(k2_relat_1(sK10),sK9),k2_relat_1(sK10)) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1237,plain,
% 3.96/0.99      ( r2_hidden(sK0(k2_relat_1(sK10),sK9),k2_relat_1(sK10))
% 3.96/0.99      | r1_xboole_0(k2_relat_1(sK10),sK9) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1,plain,
% 3.96/0.99      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1234,plain,
% 3.96/0.99      ( r2_hidden(sK0(k2_relat_1(sK10),sK9),sK9)
% 3.96/0.99      | r1_xboole_0(k2_relat_1(sK10),sK9) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(contradiction,plain,
% 3.96/0.99      ( $false ),
% 3.96/0.99      inference(minisat,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_13046,c_13048,c_9222,c_6342,c_6163,c_3750,c_2658,
% 3.96/0.99                 c_1331,c_1237,c_1234,c_24,c_26]) ).
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  ------                               Statistics
% 3.96/0.99  
% 3.96/0.99  ------ Selected
% 3.96/0.99  
% 3.96/0.99  total_time:                             0.354
% 3.96/0.99  
%------------------------------------------------------------------------------
