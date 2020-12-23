%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0579+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:39 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 135 expanded)
%              Number of clauses        :   30 (  37 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  387 ( 628 expanded)
%              Number of equality atoms :   48 (  69 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19,f18,f17])).

fof(f42,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f35,f36])).

fof(f59,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f29,f32,f31,f30])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f14,f38])).

fof(f64,plain,(
    ~ r1_tarski(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_894,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK11,sK10))
    | r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))
    | ~ r2_hidden(k4_tarski(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),X0),k4_relat_1(sK11))
    | ~ v1_relat_1(k4_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_19900,plain,
    ( ~ r2_hidden(sK7(sK11,sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))),k10_relat_1(sK11,sK10))
    | r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))
    | ~ r2_hidden(k4_tarski(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),sK7(sK11,sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))))),k4_relat_1(sK11))
    | ~ v1_relat_1(k4_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_20,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_14622,plain,
    ( ~ r2_hidden(k4_tarski(sK7(sK11,sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))),sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))),sK11)
    | r2_hidden(k4_tarski(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),sK7(sK11,sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))))),k4_relat_1(sK11))
    | ~ v1_relat_1(k4_relat_1(sK11))
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_949,plain,
    ( r2_hidden(X0,k10_relat_1(sK11,sK10))
    | ~ r2_hidden(X1,sK10)
    | ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2570,plain,
    ( r2_hidden(X0,k10_relat_1(sK11,sK10))
    | ~ r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),sK10)
    | ~ r2_hidden(k4_tarski(X0,sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))),sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_5383,plain,
    ( r2_hidden(sK7(sK11,sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))),k10_relat_1(sK11,sK10))
    | ~ r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),sK10)
    | ~ r2_hidden(k4_tarski(sK7(sK11,sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))),sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))),sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_2570])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4863,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),k2_relat_1(sK11))
    | r2_hidden(k4_tarski(sK7(sK11,sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))),sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)))),sK11) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_285,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | k3_xboole_0(k2_relat_1(sK11),sK10) != X0
    | k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_286,plain,
    ( r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),k3_xboole_0(k2_relat_1(sK11),sK10)) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_834,plain,
    ( r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),k3_xboole_0(k2_relat_1(sK11),sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_846,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1563,plain,
    ( r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_846])).

cnf(c_1564,plain,
    ( r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),sK10) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1563])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_845,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1422,plain,
    ( r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),k2_relat_1(sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_845])).

cnf(c_1423,plain,
    ( r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),k2_relat_1(sK11)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1422])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_292,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | k3_xboole_0(k2_relat_1(sK11),sK10) != X0
    | k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_293,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(k2_relat_1(sK11),sK10),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))),k10_relat_1(k4_relat_1(sK11),k10_relat_1(sK11,sK10))) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,plain,
    ( v1_relat_1(k4_relat_1(sK11))
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19900,c_14622,c_5383,c_4863,c_1564,c_1423,c_293,c_28,c_24])).


%------------------------------------------------------------------------------
