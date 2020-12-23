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
% DateTime   : Thu Dec  3 11:47:30 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 317 expanded)
%              Number of clauses        :   66 ( 103 expanded)
%              Number of leaves         :   22 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  439 (1276 expanded)
%              Number of equality atoms :  111 ( 238 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
        & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
            & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f35,f38,f37,f36])).

fof(f62,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
        | k1_xboole_0 != k10_relat_1(sK11,sK10) )
      & ( r1_xboole_0(k2_relat_1(sK11),sK10)
        | k1_xboole_0 = k10_relat_1(sK11,sK10) )
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
      | k1_xboole_0 != k10_relat_1(sK11,sK10) )
    & ( r1_xboole_0(k2_relat_1(sK11),sK10)
      | k1_xboole_0 = k10_relat_1(sK11,sK10) )
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f45,f46])).

fof(f71,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f26])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f58,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1036,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1041,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1025,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK9(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1026,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1042,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1891,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK8(X1,X0),X0),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_1042])).

cnf(c_6970,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r1_xboole_0(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_1891])).

cnf(c_7162,plain,
    ( r2_hidden(X0,k10_relat_1(X1,k2_relat_1(X2))) != iProver_top
    | r1_xboole_0(X2,X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_6970])).

cnf(c_27000,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r1_xboole_0(X1,k10_relat_1(X2,k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1041,c_7162])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_23,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1243,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | ~ r1_xboole_0(sK10,k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1246,plain,
    ( r2_hidden(sK0(k2_relat_1(sK11),sK10),sK10)
    | r1_xboole_0(k2_relat_1(sK11),sK10) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1265,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_7])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1269,plain,
    ( r2_hidden(sK0(k2_relat_1(sK11),sK10),k2_relat_1(sK11))
    | r1_xboole_0(k2_relat_1(sK11),sK10) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_24,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1020,plain,
    ( k1_xboole_0 = k10_relat_1(sK11,sK10)
    | r1_xboole_0(k2_relat_1(sK11),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1043,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1307,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r1_xboole_0(sK10,k2_relat_1(sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1020,c_1043])).

cnf(c_1315,plain,
    ( r1_xboole_0(sK10,k2_relat_1(sK11))
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1307])).

cnf(c_1441,plain,
    ( r2_hidden(k4_tarski(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),sK0(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK0(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_480,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2985,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | X0 != k10_relat_1(sK11,sK10)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_480,c_24])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1350,plain,
    ( r2_hidden(sK2(k10_relat_1(sK11,sK10)),k10_relat_1(sK11,sK10))
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1399,plain,
    ( r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),sK10)
    | ~ r2_hidden(sK2(k10_relat_1(sK11,sK10)),k10_relat_1(sK11,sK10))
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1398,plain,
    ( r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),k2_relat_1(sK11))
    | ~ r2_hidden(sK2(k10_relat_1(sK11,sK10)),k10_relat_1(sK11,sK10))
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1737,plain,
    ( ~ r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),X0)
    | ~ r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),k2_relat_1(sK11))
    | ~ r1_xboole_0(k2_relat_1(sK11),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2765,plain,
    ( ~ r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),k2_relat_1(sK11))
    | ~ r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),sK10)
    | ~ r1_xboole_0(k2_relat_1(sK11),sK10) ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_3234,plain,
    ( X0 != k10_relat_1(sK11,sK10)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2985,c_25,c_23,c_1350,c_1399,c_1398,c_2765])).

cnf(c_479,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3251,plain,
    ( k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(resolution,[status(thm)],[c_3234,c_479])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1411,plain,
    ( r2_hidden(X0,k10_relat_1(X1,sK10))
    | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK11),sK10)),X1)
    | ~ r2_hidden(sK0(k2_relat_1(sK11),sK10),sK10)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3945,plain,
    ( r2_hidden(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
    | ~ r2_hidden(k4_tarski(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),sK0(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK0(k2_relat_1(sK11),sK10),sK10)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_1411])).

cnf(c_2561,plain,
    ( ~ r2_hidden(sK2(X0),X0)
    | ~ r2_hidden(sK2(X0),X1)
    | ~ r1_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5430,plain,
    ( ~ r2_hidden(sK2(X0),X0)
    | ~ r2_hidden(sK2(X0),k1_xboole_0)
    | ~ r1_xboole_0(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_1037,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1890,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X1) != iProver_top
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1042])).

cnf(c_6395,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1890])).

cnf(c_2989,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_480,c_479])).

cnf(c_6882,plain,
    ( r2_hidden(sK2(X0),X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2989,c_6])).

cnf(c_6955,plain,
    ( sK2(X0) = sK2(X0) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_6894,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2989,c_3251])).

cnf(c_7064,plain,
    ( X0 != k1_xboole_0
    | k10_relat_1(sK11,sK10) = X0 ),
    inference(resolution,[status(thm)],[c_6894,c_480])).

cnf(c_8684,plain,
    ( ~ r2_hidden(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),X0)
    | ~ r2_hidden(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
    | ~ r1_xboole_0(k10_relat_1(sK11,sK10),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_12887,plain,
    ( ~ r2_hidden(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
    | ~ r1_xboole_0(k10_relat_1(sK11,sK10),k10_relat_1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_8684])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2552,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(X2),X2)
    | X1 != X2
    | X0 != sK2(X2) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_6954,plain,
    ( ~ r2_hidden(sK2(X0),X0)
    | r2_hidden(sK2(X0),X1)
    | X1 != X0
    | sK2(X0) != sK2(X0) ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_19774,plain,
    ( ~ r2_hidden(sK2(X0),X0)
    | r2_hidden(sK2(X0),k1_xboole_0)
    | sK2(X0) != sK2(X0)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_6954])).

cnf(c_481,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2144,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k1_xboole_0,X2)
    | X1 != X2
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_7115,plain,
    ( r1_xboole_0(k10_relat_1(X0,X1),X2)
    | ~ r1_xboole_0(k1_xboole_0,X3)
    | X2 != X3
    | k10_relat_1(X0,X1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_19792,plain,
    ( r1_xboole_0(k10_relat_1(sK11,sK10),X0)
    | ~ r1_xboole_0(k1_xboole_0,X1)
    | X0 != X1
    | k10_relat_1(sK11,sK10) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7115])).

cnf(c_27401,plain,
    ( r1_xboole_0(k10_relat_1(sK11,sK10),k10_relat_1(sK11,sK10))
    | ~ r1_xboole_0(k1_xboole_0,X0)
    | k10_relat_1(sK11,sK10) != X0
    | k10_relat_1(sK11,sK10) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19792])).

cnf(c_27419,plain,
    ( r1_xboole_0(X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27000,c_25,c_23,c_7,c_1243,c_1246,c_1265,c_1269,c_1315,c_1350,c_1399,c_1398,c_1441,c_2765,c_3945,c_5430,c_6395,c_6882,c_6955,c_7064,c_12887,c_19774,c_27401])).

cnf(c_27426,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1036,c_27419])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.64/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.64/1.49  
% 7.64/1.49  ------  iProver source info
% 7.64/1.49  
% 7.64/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.64/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.64/1.49  git: non_committed_changes: false
% 7.64/1.49  git: last_make_outside_of_git: false
% 7.64/1.49  
% 7.64/1.49  ------ 
% 7.64/1.49  
% 7.64/1.49  ------ Input Options
% 7.64/1.49  
% 7.64/1.49  --out_options                           all
% 7.64/1.49  --tptp_safe_out                         true
% 7.64/1.49  --problem_path                          ""
% 7.64/1.49  --include_path                          ""
% 7.64/1.49  --clausifier                            res/vclausify_rel
% 7.64/1.49  --clausifier_options                    --mode clausify
% 7.64/1.49  --stdin                                 false
% 7.64/1.49  --stats_out                             sel
% 7.64/1.49  
% 7.64/1.49  ------ General Options
% 7.64/1.49  
% 7.64/1.49  --fof                                   false
% 7.64/1.49  --time_out_real                         604.99
% 7.64/1.49  --time_out_virtual                      -1.
% 7.64/1.49  --symbol_type_check                     false
% 7.64/1.49  --clausify_out                          false
% 7.64/1.49  --sig_cnt_out                           false
% 7.64/1.49  --trig_cnt_out                          false
% 7.64/1.49  --trig_cnt_out_tolerance                1.
% 7.64/1.49  --trig_cnt_out_sk_spl                   false
% 7.64/1.49  --abstr_cl_out                          false
% 7.64/1.49  
% 7.64/1.49  ------ Global Options
% 7.64/1.49  
% 7.64/1.49  --schedule                              none
% 7.64/1.49  --add_important_lit                     false
% 7.64/1.49  --prop_solver_per_cl                    1000
% 7.64/1.49  --min_unsat_core                        false
% 7.64/1.49  --soft_assumptions                      false
% 7.64/1.49  --soft_lemma_size                       3
% 7.64/1.49  --prop_impl_unit_size                   0
% 7.64/1.49  --prop_impl_unit                        []
% 7.64/1.49  --share_sel_clauses                     true
% 7.64/1.49  --reset_solvers                         false
% 7.64/1.49  --bc_imp_inh                            [conj_cone]
% 7.64/1.49  --conj_cone_tolerance                   3.
% 7.64/1.49  --extra_neg_conj                        none
% 7.64/1.49  --large_theory_mode                     true
% 7.64/1.49  --prolific_symb_bound                   200
% 7.64/1.49  --lt_threshold                          2000
% 7.64/1.49  --clause_weak_htbl                      true
% 7.64/1.49  --gc_record_bc_elim                     false
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing Options
% 7.64/1.49  
% 7.64/1.49  --preprocessing_flag                    true
% 7.64/1.49  --time_out_prep_mult                    0.1
% 7.64/1.49  --splitting_mode                        input
% 7.64/1.49  --splitting_grd                         true
% 7.64/1.49  --splitting_cvd                         false
% 7.64/1.49  --splitting_cvd_svl                     false
% 7.64/1.49  --splitting_nvd                         32
% 7.64/1.49  --sub_typing                            true
% 7.64/1.49  --prep_gs_sim                           false
% 7.64/1.49  --prep_unflatten                        true
% 7.64/1.49  --prep_res_sim                          true
% 7.64/1.49  --prep_upred                            true
% 7.64/1.49  --prep_sem_filter                       exhaustive
% 7.64/1.49  --prep_sem_filter_out                   false
% 7.64/1.49  --pred_elim                             false
% 7.64/1.49  --res_sim_input                         true
% 7.64/1.49  --eq_ax_congr_red                       true
% 7.64/1.49  --pure_diseq_elim                       true
% 7.64/1.49  --brand_transform                       false
% 7.64/1.49  --non_eq_to_eq                          false
% 7.64/1.49  --prep_def_merge                        true
% 7.64/1.49  --prep_def_merge_prop_impl              false
% 7.64/1.49  --prep_def_merge_mbd                    true
% 7.64/1.49  --prep_def_merge_tr_red                 false
% 7.64/1.49  --prep_def_merge_tr_cl                  false
% 7.64/1.49  --smt_preprocessing                     true
% 7.64/1.49  --smt_ac_axioms                         fast
% 7.64/1.49  --preprocessed_out                      false
% 7.64/1.49  --preprocessed_stats                    false
% 7.64/1.49  
% 7.64/1.49  ------ Abstraction refinement Options
% 7.64/1.49  
% 7.64/1.49  --abstr_ref                             []
% 7.64/1.49  --abstr_ref_prep                        false
% 7.64/1.49  --abstr_ref_until_sat                   false
% 7.64/1.49  --abstr_ref_sig_restrict                funpre
% 7.64/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.49  --abstr_ref_under                       []
% 7.64/1.49  
% 7.64/1.49  ------ SAT Options
% 7.64/1.49  
% 7.64/1.49  --sat_mode                              false
% 7.64/1.49  --sat_fm_restart_options                ""
% 7.64/1.49  --sat_gr_def                            false
% 7.64/1.49  --sat_epr_types                         true
% 7.64/1.49  --sat_non_cyclic_types                  false
% 7.64/1.49  --sat_finite_models                     false
% 7.64/1.49  --sat_fm_lemmas                         false
% 7.64/1.49  --sat_fm_prep                           false
% 7.64/1.49  --sat_fm_uc_incr                        true
% 7.64/1.49  --sat_out_model                         small
% 7.64/1.49  --sat_out_clauses                       false
% 7.64/1.49  
% 7.64/1.49  ------ QBF Options
% 7.64/1.49  
% 7.64/1.49  --qbf_mode                              false
% 7.64/1.49  --qbf_elim_univ                         false
% 7.64/1.49  --qbf_dom_inst                          none
% 7.64/1.49  --qbf_dom_pre_inst                      false
% 7.64/1.49  --qbf_sk_in                             false
% 7.64/1.49  --qbf_pred_elim                         true
% 7.64/1.49  --qbf_split                             512
% 7.64/1.49  
% 7.64/1.49  ------ BMC1 Options
% 7.64/1.49  
% 7.64/1.49  --bmc1_incremental                      false
% 7.64/1.49  --bmc1_axioms                           reachable_all
% 7.64/1.49  --bmc1_min_bound                        0
% 7.64/1.49  --bmc1_max_bound                        -1
% 7.64/1.49  --bmc1_max_bound_default                -1
% 7.64/1.49  --bmc1_symbol_reachability              true
% 7.64/1.49  --bmc1_property_lemmas                  false
% 7.64/1.49  --bmc1_k_induction                      false
% 7.64/1.49  --bmc1_non_equiv_states                 false
% 7.64/1.49  --bmc1_deadlock                         false
% 7.64/1.49  --bmc1_ucm                              false
% 7.64/1.49  --bmc1_add_unsat_core                   none
% 7.64/1.49  --bmc1_unsat_core_children              false
% 7.64/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.49  --bmc1_out_stat                         full
% 7.64/1.49  --bmc1_ground_init                      false
% 7.64/1.49  --bmc1_pre_inst_next_state              false
% 7.64/1.49  --bmc1_pre_inst_state                   false
% 7.64/1.49  --bmc1_pre_inst_reach_state             false
% 7.64/1.49  --bmc1_out_unsat_core                   false
% 7.64/1.49  --bmc1_aig_witness_out                  false
% 7.64/1.49  --bmc1_verbose                          false
% 7.64/1.49  --bmc1_dump_clauses_tptp                false
% 7.64/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.49  --bmc1_dump_file                        -
% 7.64/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.49  --bmc1_ucm_extend_mode                  1
% 7.64/1.49  --bmc1_ucm_init_mode                    2
% 7.64/1.49  --bmc1_ucm_cone_mode                    none
% 7.64/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.49  --bmc1_ucm_relax_model                  4
% 7.64/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.49  --bmc1_ucm_layered_model                none
% 7.64/1.49  --bmc1_ucm_max_lemma_size               10
% 7.64/1.49  
% 7.64/1.49  ------ AIG Options
% 7.64/1.49  
% 7.64/1.49  --aig_mode                              false
% 7.64/1.49  
% 7.64/1.49  ------ Instantiation Options
% 7.64/1.49  
% 7.64/1.49  --instantiation_flag                    true
% 7.64/1.49  --inst_sos_flag                         false
% 7.64/1.49  --inst_sos_phase                        true
% 7.64/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel_side                     num_symb
% 7.64/1.49  --inst_solver_per_active                1400
% 7.64/1.49  --inst_solver_calls_frac                1.
% 7.64/1.49  --inst_passive_queue_type               priority_queues
% 7.64/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.49  --inst_passive_queues_freq              [25;2]
% 7.64/1.49  --inst_dismatching                      true
% 7.64/1.49  --inst_eager_unprocessed_to_passive     true
% 7.64/1.49  --inst_prop_sim_given                   true
% 7.64/1.49  --inst_prop_sim_new                     false
% 7.64/1.49  --inst_subs_new                         false
% 7.64/1.49  --inst_eq_res_simp                      false
% 7.64/1.49  --inst_subs_given                       false
% 7.64/1.49  --inst_orphan_elimination               true
% 7.64/1.49  --inst_learning_loop_flag               true
% 7.64/1.49  --inst_learning_start                   3000
% 7.64/1.49  --inst_learning_factor                  2
% 7.64/1.49  --inst_start_prop_sim_after_learn       3
% 7.64/1.49  --inst_sel_renew                        solver
% 7.64/1.49  --inst_lit_activity_flag                true
% 7.64/1.49  --inst_restr_to_given                   false
% 7.64/1.49  --inst_activity_threshold               500
% 7.64/1.49  --inst_out_proof                        true
% 7.64/1.49  
% 7.64/1.49  ------ Resolution Options
% 7.64/1.49  
% 7.64/1.49  --resolution_flag                       true
% 7.64/1.49  --res_lit_sel                           adaptive
% 7.64/1.49  --res_lit_sel_side                      none
% 7.64/1.49  --res_ordering                          kbo
% 7.64/1.49  --res_to_prop_solver                    active
% 7.64/1.49  --res_prop_simpl_new                    false
% 7.64/1.49  --res_prop_simpl_given                  true
% 7.64/1.49  --res_passive_queue_type                priority_queues
% 7.64/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.49  --res_passive_queues_freq               [15;5]
% 7.64/1.49  --res_forward_subs                      full
% 7.64/1.49  --res_backward_subs                     full
% 7.64/1.49  --res_forward_subs_resolution           true
% 7.64/1.49  --res_backward_subs_resolution          true
% 7.64/1.49  --res_orphan_elimination                true
% 7.64/1.49  --res_time_limit                        2.
% 7.64/1.49  --res_out_proof                         true
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Options
% 7.64/1.49  
% 7.64/1.49  --superposition_flag                    true
% 7.64/1.49  --sup_passive_queue_type                priority_queues
% 7.64/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.49  --sup_passive_queues_freq               [1;4]
% 7.64/1.49  --demod_completeness_check              fast
% 7.64/1.49  --demod_use_ground                      true
% 7.64/1.49  --sup_to_prop_solver                    passive
% 7.64/1.49  --sup_prop_simpl_new                    true
% 7.64/1.49  --sup_prop_simpl_given                  true
% 7.64/1.49  --sup_fun_splitting                     false
% 7.64/1.49  --sup_smt_interval                      50000
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Simplification Setup
% 7.64/1.49  
% 7.64/1.49  --sup_indices_passive                   []
% 7.64/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_full_bw                           [BwDemod]
% 7.64/1.49  --sup_immed_triv                        [TrivRules]
% 7.64/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_immed_bw_main                     []
% 7.64/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.49  
% 7.64/1.49  ------ Combination Options
% 7.64/1.49  
% 7.64/1.49  --comb_res_mult                         3
% 7.64/1.49  --comb_sup_mult                         2
% 7.64/1.49  --comb_inst_mult                        10
% 7.64/1.49  
% 7.64/1.49  ------ Debug Options
% 7.64/1.49  
% 7.64/1.49  --dbg_backtrace                         false
% 7.64/1.49  --dbg_dump_prop_clauses                 false
% 7.64/1.49  --dbg_dump_prop_clauses_file            -
% 7.64/1.49  --dbg_out_stat                          false
% 7.64/1.49  ------ Parsing...
% 7.64/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.64/1.49  ------ Proving...
% 7.64/1.49  ------ Problem Properties 
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  clauses                                 25
% 7.64/1.49  conjectures                             3
% 7.64/1.49  EPR                                     4
% 7.64/1.49  Horn                                    17
% 7.64/1.49  unary                                   2
% 7.64/1.49  binary                                  11
% 7.64/1.49  lits                                    65
% 7.64/1.49  lits eq                                 9
% 7.64/1.49  fd_pure                                 0
% 7.64/1.49  fd_pseudo                               0
% 7.64/1.49  fd_cond                                 1
% 7.64/1.49  fd_pseudo_cond                          5
% 7.64/1.49  AC symbols                              0
% 7.64/1.49  
% 7.64/1.49  ------ Input Options Time Limit: Unbounded
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  ------ 
% 7.64/1.49  Current options:
% 7.64/1.49  ------ 
% 7.64/1.49  
% 7.64/1.49  ------ Input Options
% 7.64/1.49  
% 7.64/1.49  --out_options                           all
% 7.64/1.49  --tptp_safe_out                         true
% 7.64/1.49  --problem_path                          ""
% 7.64/1.49  --include_path                          ""
% 7.64/1.49  --clausifier                            res/vclausify_rel
% 7.64/1.49  --clausifier_options                    --mode clausify
% 7.64/1.49  --stdin                                 false
% 7.64/1.49  --stats_out                             sel
% 7.64/1.49  
% 7.64/1.49  ------ General Options
% 7.64/1.49  
% 7.64/1.49  --fof                                   false
% 7.64/1.49  --time_out_real                         604.99
% 7.64/1.49  --time_out_virtual                      -1.
% 7.64/1.49  --symbol_type_check                     false
% 7.64/1.49  --clausify_out                          false
% 7.64/1.49  --sig_cnt_out                           false
% 7.64/1.49  --trig_cnt_out                          false
% 7.64/1.49  --trig_cnt_out_tolerance                1.
% 7.64/1.49  --trig_cnt_out_sk_spl                   false
% 7.64/1.49  --abstr_cl_out                          false
% 7.64/1.49  
% 7.64/1.49  ------ Global Options
% 7.64/1.49  
% 7.64/1.49  --schedule                              none
% 7.64/1.49  --add_important_lit                     false
% 7.64/1.49  --prop_solver_per_cl                    1000
% 7.64/1.49  --min_unsat_core                        false
% 7.64/1.49  --soft_assumptions                      false
% 7.64/1.49  --soft_lemma_size                       3
% 7.64/1.49  --prop_impl_unit_size                   0
% 7.64/1.49  --prop_impl_unit                        []
% 7.64/1.49  --share_sel_clauses                     true
% 7.64/1.49  --reset_solvers                         false
% 7.64/1.49  --bc_imp_inh                            [conj_cone]
% 7.64/1.49  --conj_cone_tolerance                   3.
% 7.64/1.49  --extra_neg_conj                        none
% 7.64/1.49  --large_theory_mode                     true
% 7.64/1.49  --prolific_symb_bound                   200
% 7.64/1.49  --lt_threshold                          2000
% 7.64/1.49  --clause_weak_htbl                      true
% 7.64/1.49  --gc_record_bc_elim                     false
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing Options
% 7.64/1.49  
% 7.64/1.49  --preprocessing_flag                    true
% 7.64/1.49  --time_out_prep_mult                    0.1
% 7.64/1.49  --splitting_mode                        input
% 7.64/1.49  --splitting_grd                         true
% 7.64/1.49  --splitting_cvd                         false
% 7.64/1.49  --splitting_cvd_svl                     false
% 7.64/1.49  --splitting_nvd                         32
% 7.64/1.49  --sub_typing                            true
% 7.64/1.49  --prep_gs_sim                           false
% 7.64/1.49  --prep_unflatten                        true
% 7.64/1.49  --prep_res_sim                          true
% 7.64/1.49  --prep_upred                            true
% 7.64/1.49  --prep_sem_filter                       exhaustive
% 7.64/1.49  --prep_sem_filter_out                   false
% 7.64/1.49  --pred_elim                             false
% 7.64/1.49  --res_sim_input                         true
% 7.64/1.49  --eq_ax_congr_red                       true
% 7.64/1.49  --pure_diseq_elim                       true
% 7.64/1.49  --brand_transform                       false
% 7.64/1.49  --non_eq_to_eq                          false
% 7.64/1.49  --prep_def_merge                        true
% 7.64/1.49  --prep_def_merge_prop_impl              false
% 7.64/1.49  --prep_def_merge_mbd                    true
% 7.64/1.49  --prep_def_merge_tr_red                 false
% 7.64/1.49  --prep_def_merge_tr_cl                  false
% 7.64/1.49  --smt_preprocessing                     true
% 7.64/1.49  --smt_ac_axioms                         fast
% 7.64/1.49  --preprocessed_out                      false
% 7.64/1.49  --preprocessed_stats                    false
% 7.64/1.49  
% 7.64/1.49  ------ Abstraction refinement Options
% 7.64/1.49  
% 7.64/1.49  --abstr_ref                             []
% 7.64/1.49  --abstr_ref_prep                        false
% 7.64/1.49  --abstr_ref_until_sat                   false
% 7.64/1.49  --abstr_ref_sig_restrict                funpre
% 7.64/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.49  --abstr_ref_under                       []
% 7.64/1.49  
% 7.64/1.49  ------ SAT Options
% 7.64/1.49  
% 7.64/1.49  --sat_mode                              false
% 7.64/1.49  --sat_fm_restart_options                ""
% 7.64/1.49  --sat_gr_def                            false
% 7.64/1.49  --sat_epr_types                         true
% 7.64/1.49  --sat_non_cyclic_types                  false
% 7.64/1.49  --sat_finite_models                     false
% 7.64/1.49  --sat_fm_lemmas                         false
% 7.64/1.49  --sat_fm_prep                           false
% 7.64/1.49  --sat_fm_uc_incr                        true
% 7.64/1.49  --sat_out_model                         small
% 7.64/1.49  --sat_out_clauses                       false
% 7.64/1.49  
% 7.64/1.49  ------ QBF Options
% 7.64/1.49  
% 7.64/1.49  --qbf_mode                              false
% 7.64/1.49  --qbf_elim_univ                         false
% 7.64/1.49  --qbf_dom_inst                          none
% 7.64/1.49  --qbf_dom_pre_inst                      false
% 7.64/1.49  --qbf_sk_in                             false
% 7.64/1.49  --qbf_pred_elim                         true
% 7.64/1.49  --qbf_split                             512
% 7.64/1.49  
% 7.64/1.49  ------ BMC1 Options
% 7.64/1.49  
% 7.64/1.49  --bmc1_incremental                      false
% 7.64/1.49  --bmc1_axioms                           reachable_all
% 7.64/1.49  --bmc1_min_bound                        0
% 7.64/1.49  --bmc1_max_bound                        -1
% 7.64/1.49  --bmc1_max_bound_default                -1
% 7.64/1.49  --bmc1_symbol_reachability              true
% 7.64/1.49  --bmc1_property_lemmas                  false
% 7.64/1.49  --bmc1_k_induction                      false
% 7.64/1.49  --bmc1_non_equiv_states                 false
% 7.64/1.49  --bmc1_deadlock                         false
% 7.64/1.49  --bmc1_ucm                              false
% 7.64/1.49  --bmc1_add_unsat_core                   none
% 7.64/1.49  --bmc1_unsat_core_children              false
% 7.64/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.49  --bmc1_out_stat                         full
% 7.64/1.49  --bmc1_ground_init                      false
% 7.64/1.49  --bmc1_pre_inst_next_state              false
% 7.64/1.49  --bmc1_pre_inst_state                   false
% 7.64/1.49  --bmc1_pre_inst_reach_state             false
% 7.64/1.49  --bmc1_out_unsat_core                   false
% 7.64/1.49  --bmc1_aig_witness_out                  false
% 7.64/1.49  --bmc1_verbose                          false
% 7.64/1.49  --bmc1_dump_clauses_tptp                false
% 7.64/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.49  --bmc1_dump_file                        -
% 7.64/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.49  --bmc1_ucm_extend_mode                  1
% 7.64/1.49  --bmc1_ucm_init_mode                    2
% 7.64/1.49  --bmc1_ucm_cone_mode                    none
% 7.64/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.49  --bmc1_ucm_relax_model                  4
% 7.64/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.49  --bmc1_ucm_layered_model                none
% 7.64/1.49  --bmc1_ucm_max_lemma_size               10
% 7.64/1.49  
% 7.64/1.49  ------ AIG Options
% 7.64/1.49  
% 7.64/1.49  --aig_mode                              false
% 7.64/1.49  
% 7.64/1.49  ------ Instantiation Options
% 7.64/1.49  
% 7.64/1.49  --instantiation_flag                    true
% 7.64/1.49  --inst_sos_flag                         false
% 7.64/1.49  --inst_sos_phase                        true
% 7.64/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel_side                     num_symb
% 7.64/1.49  --inst_solver_per_active                1400
% 7.64/1.49  --inst_solver_calls_frac                1.
% 7.64/1.49  --inst_passive_queue_type               priority_queues
% 7.64/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.49  --inst_passive_queues_freq              [25;2]
% 7.64/1.49  --inst_dismatching                      true
% 7.64/1.49  --inst_eager_unprocessed_to_passive     true
% 7.64/1.49  --inst_prop_sim_given                   true
% 7.64/1.49  --inst_prop_sim_new                     false
% 7.64/1.49  --inst_subs_new                         false
% 7.64/1.49  --inst_eq_res_simp                      false
% 7.64/1.49  --inst_subs_given                       false
% 7.64/1.49  --inst_orphan_elimination               true
% 7.64/1.49  --inst_learning_loop_flag               true
% 7.64/1.49  --inst_learning_start                   3000
% 7.64/1.49  --inst_learning_factor                  2
% 7.64/1.49  --inst_start_prop_sim_after_learn       3
% 7.64/1.49  --inst_sel_renew                        solver
% 7.64/1.49  --inst_lit_activity_flag                true
% 7.64/1.49  --inst_restr_to_given                   false
% 7.64/1.49  --inst_activity_threshold               500
% 7.64/1.49  --inst_out_proof                        true
% 7.64/1.49  
% 7.64/1.49  ------ Resolution Options
% 7.64/1.49  
% 7.64/1.49  --resolution_flag                       true
% 7.64/1.49  --res_lit_sel                           adaptive
% 7.64/1.49  --res_lit_sel_side                      none
% 7.64/1.49  --res_ordering                          kbo
% 7.64/1.49  --res_to_prop_solver                    active
% 7.64/1.49  --res_prop_simpl_new                    false
% 7.64/1.49  --res_prop_simpl_given                  true
% 7.64/1.49  --res_passive_queue_type                priority_queues
% 7.64/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.49  --res_passive_queues_freq               [15;5]
% 7.64/1.49  --res_forward_subs                      full
% 7.64/1.49  --res_backward_subs                     full
% 7.64/1.49  --res_forward_subs_resolution           true
% 7.64/1.49  --res_backward_subs_resolution          true
% 7.64/1.49  --res_orphan_elimination                true
% 7.64/1.49  --res_time_limit                        2.
% 7.64/1.49  --res_out_proof                         true
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Options
% 7.64/1.49  
% 7.64/1.49  --superposition_flag                    true
% 7.64/1.49  --sup_passive_queue_type                priority_queues
% 7.64/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.49  --sup_passive_queues_freq               [1;4]
% 7.64/1.49  --demod_completeness_check              fast
% 7.64/1.49  --demod_use_ground                      true
% 7.64/1.49  --sup_to_prop_solver                    passive
% 7.64/1.49  --sup_prop_simpl_new                    true
% 7.64/1.49  --sup_prop_simpl_given                  true
% 7.64/1.49  --sup_fun_splitting                     false
% 7.64/1.49  --sup_smt_interval                      50000
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Simplification Setup
% 7.64/1.49  
% 7.64/1.49  --sup_indices_passive                   []
% 7.64/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_full_bw                           [BwDemod]
% 7.64/1.49  --sup_immed_triv                        [TrivRules]
% 7.64/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_immed_bw_main                     []
% 7.64/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.49  
% 7.64/1.49  ------ Combination Options
% 7.64/1.49  
% 7.64/1.49  --comb_res_mult                         3
% 7.64/1.49  --comb_sup_mult                         2
% 7.64/1.49  --comb_inst_mult                        10
% 7.64/1.49  
% 7.64/1.49  ------ Debug Options
% 7.64/1.49  
% 7.64/1.49  --dbg_backtrace                         false
% 7.64/1.49  --dbg_dump_prop_clauses                 false
% 7.64/1.49  --dbg_dump_prop_clauses_file            -
% 7.64/1.49  --dbg_out_stat                          false
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  ------ Proving...
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  % SZS status Theorem for theBenchmark.p
% 7.64/1.49  
% 7.64/1.49   Resolution empty clause
% 7.64/1.49  
% 7.64/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  fof(f5,axiom,(
% 7.64/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f55,plain,(
% 7.64/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f5])).
% 7.64/1.49  
% 7.64/1.49  fof(f2,axiom,(
% 7.64/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f12,plain,(
% 7.64/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.64/1.49    inference(rectify,[],[f2])).
% 7.64/1.49  
% 7.64/1.49  fof(f15,plain,(
% 7.64/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.64/1.49    inference(ennf_transformation,[],[f12])).
% 7.64/1.49  
% 7.64/1.49  fof(f22,plain,(
% 7.64/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f23,plain,(
% 7.64/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.64/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f22])).
% 7.64/1.49  
% 7.64/1.49  fof(f50,plain,(
% 7.64/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f23])).
% 7.64/1.49  
% 7.64/1.49  fof(f8,axiom,(
% 7.64/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f19,plain,(
% 7.64/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.64/1.49    inference(ennf_transformation,[],[f8])).
% 7.64/1.49  
% 7.64/1.49  fof(f40,plain,(
% 7.64/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.64/1.49    inference(nnf_transformation,[],[f19])).
% 7.64/1.49  
% 7.64/1.49  fof(f41,plain,(
% 7.64/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.64/1.49    inference(rectify,[],[f40])).
% 7.64/1.49  
% 7.64/1.49  fof(f42,plain,(
% 7.64/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f43,plain,(
% 7.64/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.64/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).
% 7.64/1.49  
% 7.64/1.49  fof(f68,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f43])).
% 7.64/1.49  
% 7.64/1.49  fof(f7,axiom,(
% 7.64/1.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f34,plain,(
% 7.64/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.64/1.49    inference(nnf_transformation,[],[f7])).
% 7.64/1.49  
% 7.64/1.49  fof(f35,plain,(
% 7.64/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.64/1.49    inference(rectify,[],[f34])).
% 7.64/1.49  
% 7.64/1.49  fof(f38,plain,(
% 7.64/1.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f37,plain,(
% 7.64/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0))) )),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f36,plain,(
% 7.64/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f39,plain,(
% 7.64/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.64/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f35,f38,f37,f36])).
% 7.64/1.49  
% 7.64/1.49  fof(f62,plain,(
% 7.64/1.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 7.64/1.49    inference(cnf_transformation,[],[f39])).
% 7.64/1.49  
% 7.64/1.49  fof(f78,plain,(
% 7.64/1.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 7.64/1.49    inference(equality_resolution,[],[f62])).
% 7.64/1.49  
% 7.64/1.49  fof(f51,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f23])).
% 7.64/1.49  
% 7.64/1.49  fof(f10,conjecture,(
% 7.64/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f11,negated_conjecture,(
% 7.64/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.64/1.49    inference(negated_conjecture,[],[f10])).
% 7.64/1.49  
% 7.64/1.49  fof(f21,plain,(
% 7.64/1.49    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 7.64/1.49    inference(ennf_transformation,[],[f11])).
% 7.64/1.49  
% 7.64/1.49  fof(f44,plain,(
% 7.64/1.49    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 7.64/1.49    inference(nnf_transformation,[],[f21])).
% 7.64/1.49  
% 7.64/1.49  fof(f45,plain,(
% 7.64/1.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.64/1.49    inference(flattening,[],[f44])).
% 7.64/1.49  
% 7.64/1.49  fof(f46,plain,(
% 7.64/1.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)) & (r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)) & v1_relat_1(sK11))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f47,plain,(
% 7.64/1.49    (~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)) & (r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)) & v1_relat_1(sK11)),
% 7.64/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f45,f46])).
% 7.64/1.49  
% 7.64/1.49  fof(f71,plain,(
% 7.64/1.49    v1_relat_1(sK11)),
% 7.64/1.49    inference(cnf_transformation,[],[f47])).
% 7.64/1.49  
% 7.64/1.49  fof(f73,plain,(
% 7.64/1.49    ~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)),
% 7.64/1.49    inference(cnf_transformation,[],[f47])).
% 7.64/1.49  
% 7.64/1.49  fof(f1,axiom,(
% 7.64/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f14,plain,(
% 7.64/1.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.64/1.49    inference(ennf_transformation,[],[f1])).
% 7.64/1.49  
% 7.64/1.49  fof(f48,plain,(
% 7.64/1.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f14])).
% 7.64/1.49  
% 7.64/1.49  fof(f49,plain,(
% 7.64/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f23])).
% 7.64/1.49  
% 7.64/1.49  fof(f72,plain,(
% 7.64/1.49    r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)),
% 7.64/1.49    inference(cnf_transformation,[],[f47])).
% 7.64/1.49  
% 7.64/1.49  fof(f4,axiom,(
% 7.64/1.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f17,plain,(
% 7.64/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.64/1.49    inference(ennf_transformation,[],[f4])).
% 7.64/1.49  
% 7.64/1.49  fof(f26,plain,(
% 7.64/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f27,plain,(
% 7.64/1.49    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 7.64/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f26])).
% 7.64/1.49  
% 7.64/1.49  fof(f54,plain,(
% 7.64/1.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 7.64/1.49    inference(cnf_transformation,[],[f27])).
% 7.64/1.49  
% 7.64/1.49  fof(f66,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f43])).
% 7.64/1.49  
% 7.64/1.49  fof(f6,axiom,(
% 7.64/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f18,plain,(
% 7.64/1.49    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f6])).
% 7.64/1.49  
% 7.64/1.49  fof(f28,plain,(
% 7.64/1.49    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.64/1.49    inference(nnf_transformation,[],[f18])).
% 7.64/1.49  
% 7.64/1.49  fof(f29,plain,(
% 7.64/1.49    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.64/1.49    inference(rectify,[],[f28])).
% 7.64/1.49  
% 7.64/1.49  fof(f32,plain,(
% 7.64/1.49    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f31,plain,(
% 7.64/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f30,plain,(
% 7.64/1.49    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f33,plain,(
% 7.64/1.49    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.64/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).
% 7.64/1.49  
% 7.64/1.49  fof(f58,plain,(
% 7.64/1.49    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f33])).
% 7.64/1.49  
% 7.64/1.49  fof(f74,plain,(
% 7.64/1.49    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 7.64/1.49    inference(equality_resolution,[],[f58])).
% 7.64/1.49  
% 7.64/1.49  cnf(c_7,plain,
% 7.64/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1036,plain,
% 7.64/1.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2,plain,
% 7.64/1.49      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1041,plain,
% 7.64/1.49      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 7.64/1.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_19,plain,
% 7.64/1.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.64/1.49      | r2_hidden(sK9(X0,X2,X1),X2)
% 7.64/1.49      | ~ v1_relat_1(X1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1025,plain,
% 7.64/1.49      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 7.64/1.49      | r2_hidden(sK9(X0,X2,X1),X2) = iProver_top
% 7.64/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_17,plain,
% 7.64/1.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.64/1.49      | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1026,plain,
% 7.64/1.49      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.64/1.49      | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1,plain,
% 7.64/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1042,plain,
% 7.64/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.64/1.49      | r2_hidden(X0,X2) != iProver_top
% 7.64/1.49      | r1_xboole_0(X2,X1) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1891,plain,
% 7.64/1.49      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.64/1.49      | r2_hidden(k4_tarski(sK8(X1,X0),X0),X2) != iProver_top
% 7.64/1.49      | r1_xboole_0(X2,X1) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1026,c_1042]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_6970,plain,
% 7.64/1.49      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.64/1.49      | r1_xboole_0(X1,X1) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1026,c_1891]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_7162,plain,
% 7.64/1.49      ( r2_hidden(X0,k10_relat_1(X1,k2_relat_1(X2))) != iProver_top
% 7.64/1.49      | r1_xboole_0(X2,X2) != iProver_top
% 7.64/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1025,c_6970]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_27000,plain,
% 7.64/1.49      ( r1_xboole_0(X0,X0) != iProver_top
% 7.64/1.49      | r1_xboole_0(X1,k10_relat_1(X2,k2_relat_1(X0))) = iProver_top
% 7.64/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1041,c_7162]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_25,negated_conjecture,
% 7.64/1.49      ( v1_relat_1(sK11) ),
% 7.64/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_23,negated_conjecture,
% 7.64/1.49      ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.64/1.49      | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
% 7.64/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_0,plain,
% 7.64/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1243,plain,
% 7.64/1.49      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.64/1.49      | ~ r1_xboole_0(sK10,k2_relat_1(sK11)) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1246,plain,
% 7.64/1.49      ( r2_hidden(sK0(k2_relat_1(sK11),sK10),sK10)
% 7.64/1.49      | r1_xboole_0(k2_relat_1(sK11),sK10) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1265,plain,
% 7.64/1.49      ( r1_xboole_0(k1_xboole_0,X0) ),
% 7.64/1.49      inference(resolution,[status(thm)],[c_0,c_7]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_3,plain,
% 7.64/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1269,plain,
% 7.64/1.49      ( r2_hidden(sK0(k2_relat_1(sK11),sK10),k2_relat_1(sK11))
% 7.64/1.49      | r1_xboole_0(k2_relat_1(sK11),sK10) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_24,negated_conjecture,
% 7.64/1.49      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.64/1.49      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.64/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1020,plain,
% 7.64/1.49      ( k1_xboole_0 = k10_relat_1(sK11,sK10)
% 7.64/1.49      | r1_xboole_0(k2_relat_1(sK11),sK10) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1043,plain,
% 7.64/1.49      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1307,plain,
% 7.64/1.49      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 7.64/1.49      | r1_xboole_0(sK10,k2_relat_1(sK11)) = iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1020,c_1043]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1315,plain,
% 7.64/1.49      ( r1_xboole_0(sK10,k2_relat_1(sK11))
% 7.64/1.49      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 7.64/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1307]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1441,plain,
% 7.64/1.49      ( r2_hidden(k4_tarski(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),sK0(k2_relat_1(sK11),sK10)),sK11)
% 7.64/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_480,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2985,plain,
% 7.64/1.49      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.64/1.49      | X0 != k10_relat_1(sK11,sK10)
% 7.64/1.49      | k1_xboole_0 = X0 ),
% 7.64/1.49      inference(resolution,[status(thm)],[c_480,c_24]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_6,plain,
% 7.64/1.49      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 7.64/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1350,plain,
% 7.64/1.49      ( r2_hidden(sK2(k10_relat_1(sK11,sK10)),k10_relat_1(sK11,sK10))
% 7.64/1.49      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1399,plain,
% 7.64/1.49      ( r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),sK10)
% 7.64/1.49      | ~ r2_hidden(sK2(k10_relat_1(sK11,sK10)),k10_relat_1(sK11,sK10))
% 7.64/1.49      | ~ v1_relat_1(sK11) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_21,plain,
% 7.64/1.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.64/1.49      | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1))
% 7.64/1.49      | ~ v1_relat_1(X1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1398,plain,
% 7.64/1.49      ( r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),k2_relat_1(sK11))
% 7.64/1.49      | ~ r2_hidden(sK2(k10_relat_1(sK11,sK10)),k10_relat_1(sK11,sK10))
% 7.64/1.49      | ~ v1_relat_1(sK11) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_21]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1737,plain,
% 7.64/1.49      ( ~ r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),X0)
% 7.64/1.49      | ~ r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),k2_relat_1(sK11))
% 7.64/1.49      | ~ r1_xboole_0(k2_relat_1(sK11),X0) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2765,plain,
% 7.64/1.49      ( ~ r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),k2_relat_1(sK11))
% 7.64/1.49      | ~ r2_hidden(sK9(sK2(k10_relat_1(sK11,sK10)),sK10,sK11),sK10)
% 7.64/1.49      | ~ r1_xboole_0(k2_relat_1(sK11),sK10) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_1737]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_3234,plain,
% 7.64/1.49      ( X0 != k10_relat_1(sK11,sK10) | k1_xboole_0 = X0 ),
% 7.64/1.49      inference(global_propositional_subsumption,
% 7.64/1.49                [status(thm)],
% 7.64/1.49                [c_2985,c_25,c_23,c_1350,c_1399,c_1398,c_2765]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_479,plain,( X0 = X0 ),theory(equality) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_3251,plain,
% 7.64/1.49      ( k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.64/1.49      inference(resolution,[status(thm)],[c_3234,c_479]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11,plain,
% 7.64/1.49      ( ~ r2_hidden(X0,X1)
% 7.64/1.49      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.64/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.64/1.49      | ~ v1_relat_1(X3) ),
% 7.64/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1411,plain,
% 7.64/1.49      ( r2_hidden(X0,k10_relat_1(X1,sK10))
% 7.64/1.49      | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK11),sK10)),X1)
% 7.64/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK11),sK10),sK10)
% 7.64/1.49      | ~ v1_relat_1(X1) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_3945,plain,
% 7.64/1.49      ( r2_hidden(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
% 7.64/1.49      | ~ r2_hidden(k4_tarski(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),sK0(k2_relat_1(sK11),sK10)),sK11)
% 7.64/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK11),sK10),sK10)
% 7.64/1.49      | ~ v1_relat_1(sK11) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_1411]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2561,plain,
% 7.64/1.49      ( ~ r2_hidden(sK2(X0),X0)
% 7.64/1.49      | ~ r2_hidden(sK2(X0),X1)
% 7.64/1.49      | ~ r1_xboole_0(X0,X1) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_5430,plain,
% 7.64/1.49      ( ~ r2_hidden(sK2(X0),X0)
% 7.64/1.49      | ~ r2_hidden(sK2(X0),k1_xboole_0)
% 7.64/1.49      | ~ r1_xboole_0(X0,k1_xboole_0) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_2561]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1037,plain,
% 7.64/1.49      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1890,plain,
% 7.64/1.49      ( k1_xboole_0 = X0
% 7.64/1.49      | r2_hidden(sK2(X0),X1) != iProver_top
% 7.64/1.49      | r1_xboole_0(X1,X0) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1037,c_1042]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_6395,plain,
% 7.64/1.49      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1037,c_1890]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2989,plain,
% 7.64/1.49      ( X0 != X1 | X1 = X0 ),
% 7.64/1.49      inference(resolution,[status(thm)],[c_480,c_479]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_6882,plain,
% 7.64/1.49      ( r2_hidden(sK2(X0),X0) | X0 = k1_xboole_0 ),
% 7.64/1.49      inference(resolution,[status(thm)],[c_2989,c_6]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_6955,plain,
% 7.64/1.49      ( sK2(X0) = sK2(X0) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_479]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_6894,plain,
% 7.64/1.49      ( k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 7.64/1.49      inference(resolution,[status(thm)],[c_2989,c_3251]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_7064,plain,
% 7.64/1.49      ( X0 != k1_xboole_0 | k10_relat_1(sK11,sK10) = X0 ),
% 7.64/1.49      inference(resolution,[status(thm)],[c_6894,c_480]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_8684,plain,
% 7.64/1.49      ( ~ r2_hidden(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),X0)
% 7.64/1.49      | ~ r2_hidden(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
% 7.64/1.49      | ~ r1_xboole_0(k10_relat_1(sK11,sK10),X0) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_12887,plain,
% 7.64/1.49      ( ~ r2_hidden(sK8(sK11,sK0(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
% 7.64/1.49      | ~ r1_xboole_0(k10_relat_1(sK11,sK10),k10_relat_1(sK11,sK10)) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_8684]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_482,plain,
% 7.64/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.64/1.49      theory(equality) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2552,plain,
% 7.64/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(sK2(X2),X2) | X1 != X2 | X0 != sK2(X2) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_482]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_6954,plain,
% 7.64/1.49      ( ~ r2_hidden(sK2(X0),X0)
% 7.64/1.49      | r2_hidden(sK2(X0),X1)
% 7.64/1.49      | X1 != X0
% 7.64/1.49      | sK2(X0) != sK2(X0) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_2552]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_19774,plain,
% 7.64/1.49      ( ~ r2_hidden(sK2(X0),X0)
% 7.64/1.49      | r2_hidden(sK2(X0),k1_xboole_0)
% 7.64/1.49      | sK2(X0) != sK2(X0)
% 7.64/1.49      | k1_xboole_0 != X0 ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_6954]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_481,plain,
% 7.64/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.64/1.49      theory(equality) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2144,plain,
% 7.64/1.49      ( r1_xboole_0(X0,X1)
% 7.64/1.49      | ~ r1_xboole_0(k1_xboole_0,X2)
% 7.64/1.49      | X1 != X2
% 7.64/1.49      | X0 != k1_xboole_0 ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_481]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_7115,plain,
% 7.64/1.49      ( r1_xboole_0(k10_relat_1(X0,X1),X2)
% 7.64/1.49      | ~ r1_xboole_0(k1_xboole_0,X3)
% 7.64/1.49      | X2 != X3
% 7.64/1.49      | k10_relat_1(X0,X1) != k1_xboole_0 ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_2144]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_19792,plain,
% 7.64/1.49      ( r1_xboole_0(k10_relat_1(sK11,sK10),X0)
% 7.64/1.49      | ~ r1_xboole_0(k1_xboole_0,X1)
% 7.64/1.49      | X0 != X1
% 7.64/1.49      | k10_relat_1(sK11,sK10) != k1_xboole_0 ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_7115]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_27401,plain,
% 7.64/1.49      ( r1_xboole_0(k10_relat_1(sK11,sK10),k10_relat_1(sK11,sK10))
% 7.64/1.49      | ~ r1_xboole_0(k1_xboole_0,X0)
% 7.64/1.49      | k10_relat_1(sK11,sK10) != X0
% 7.64/1.49      | k10_relat_1(sK11,sK10) != k1_xboole_0 ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_19792]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_27419,plain,
% 7.64/1.49      ( r1_xboole_0(X0,X0) != iProver_top ),
% 7.64/1.49      inference(global_propositional_subsumption,
% 7.64/1.49                [status(thm)],
% 7.64/1.49                [c_27000,c_25,c_23,c_7,c_1243,c_1246,c_1265,c_1269,c_1315,
% 7.64/1.49                 c_1350,c_1399,c_1398,c_1441,c_2765,c_3945,c_5430,c_6395,
% 7.64/1.49                 c_6882,c_6955,c_7064,c_12887,c_19774,c_27401]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_27426,plain,
% 7.64/1.49      ( $false ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1036,c_27419]) ).
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  ------                               Statistics
% 7.64/1.49  
% 7.64/1.49  ------ Selected
% 7.64/1.49  
% 7.64/1.49  total_time:                             0.805
% 7.64/1.49  
%------------------------------------------------------------------------------
