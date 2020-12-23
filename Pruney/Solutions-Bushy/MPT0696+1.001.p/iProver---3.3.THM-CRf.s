%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0696+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:55 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.45s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 150 expanded)
%              Number of clauses        :   34 (  38 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  391 ( 769 expanded)
%              Number of equality atoms :   40 (  74 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f23,f22,f21])).

fof(f43,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f12,f32])).

fof(f55,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f37,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f11,f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ~ r1_tarski(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_364,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK10 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_365,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK10,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK10) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_1450,plain,
    ( ~ r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),X0)
    | r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),k10_relat_1(sK10,X0))
    | ~ r2_hidden(k4_tarski(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))))),sK10) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_18526,plain,
    ( ~ r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),k3_xboole_0(k9_relat_1(sK10,sK8),sK9))
    | r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))
    | ~ r2_hidden(k4_tarski(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))))),sK10) ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2898,plain,
    ( ~ r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),X0)
    | ~ r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),k9_relat_1(sK10,sK8))
    | r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),k3_xboole_0(k9_relat_1(sK10,sK8),X0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_9899,plain,
    ( ~ r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),k9_relat_1(sK10,sK8))
    | r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),k3_xboole_0(k9_relat_1(sK10,sK8),sK9))
    | ~ r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),sK9) ),
    inference(instantiation,[status(thm)],[c_2898])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_379,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | sK10 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_380,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK10,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK10) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_1455,plain,
    ( r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),k9_relat_1(sK10,X0))
    | ~ r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),X0)
    | ~ r2_hidden(k4_tarski(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))))),sK10) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_1536,plain,
    ( r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),k9_relat_1(sK10,sK8))
    | ~ r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),sK8)
    | ~ r2_hidden(k4_tarski(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))))),sK10) ),
    inference(instantiation,[status(thm)],[c_1455])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_406,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_407,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK10,X1))
    | r2_hidden(sK5(sK10,X1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_1295,plain,
    ( r2_hidden(sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)))),sK9)
    | ~ r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),k10_relat_1(sK10,sK9)) ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK5(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_394,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK5(X1,X2,X0)),X1)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_395,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK10,X1))
    | r2_hidden(k4_tarski(X0,sK5(sK10,X1,X0)),sK10) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_1296,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),k10_relat_1(sK10,sK9))
    | r2_hidden(k4_tarski(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),sK5(sK10,sK9,sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))))),sK10) ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1201,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),k3_xboole_0(sK8,k10_relat_1(sK10,sK9)))
    | r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),sK8) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1198,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),k10_relat_1(sK10,sK9))
    | ~ r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),k3_xboole_0(sK8,k10_relat_1(sK10,sK9))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK6(X0,X1),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_257,plain,
    ( ~ r2_hidden(sK6(X0,X1),X1)
    | k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)) != X1
    | k3_xboole_0(sK8,k10_relat_1(sK10,sK9)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_258,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK6(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_250,plain,
    ( r2_hidden(sK6(X0,X1),X0)
    | k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9)) != X1
    | k3_xboole_0(sK8,k10_relat_1(sK10,sK9)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_251,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK8,k10_relat_1(sK10,sK9)),k10_relat_1(sK10,k3_xboole_0(k9_relat_1(sK10,sK8),sK9))),k3_xboole_0(sK8,k10_relat_1(sK10,sK9))) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18526,c_9899,c_1536,c_1295,c_1296,c_1201,c_1198,c_258,c_251])).


%------------------------------------------------------------------------------
