%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:28 EST 2020

% Result     : Theorem 27.37s
% Output     : CNFRefutation 27.37s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 340 expanded)
%              Number of clauses        :   63 ( 105 expanded)
%              Number of leaves         :   22 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  465 (1275 expanded)
%              Number of equality atoms :  122 ( 394 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f26])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f7,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f16])).

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
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0) ) ) ),
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
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).

fof(f59,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f8])).

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
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f35,f38,f37,f36])).

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
        | k1_xboole_0 != k10_relat_1(sK9,sK8) )
      & ( r1_xboole_0(k2_relat_1(sK9),sK8)
        | k1_xboole_0 = k10_relat_1(sK9,sK8) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
      | k1_xboole_0 != k10_relat_1(sK9,sK8) )
    & ( r1_xboole_0(k2_relat_1(sK9),sK8)
      | k1_xboole_0 = k10_relat_1(sK9,sK8) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f41,f42])).

fof(f70,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f56])).

fof(f69,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f67,f56])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_122130,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK9,sK8),X0)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k10_relat_1(sK9,sK8),X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_122132,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK9,sK8),k1_xboole_0)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k10_relat_1(sK9,sK8),k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_122130])).

cnf(c_313,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_99911,plain,
    ( sK7(sK9,sK1(k2_relat_1(sK9),sK8)) = sK7(sK9,sK1(k2_relat_1(sK9),sK8)) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_317,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_27537,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | X0 != sK7(sK9,sK1(k2_relat_1(sK9),sK8))
    | X1 != k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_99910,plain,
    ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | X0 != k10_relat_1(sK9,sK8)
    | sK7(sK9,sK1(k2_relat_1(sK9),sK8)) != sK7(sK9,sK1(k2_relat_1(sK9),sK8)) ),
    inference(instantiation,[status(thm)],[c_27537])).

cnf(c_99913,plain,
    ( ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_xboole_0)
    | sK7(sK9,sK1(k2_relat_1(sK9),sK8)) != sK7(sK9,sK1(k2_relat_1(sK9),sK8))
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_99910])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_27553,plain,
    ( ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k10_relat_1(sK9,sK8),X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_27555,plain,
    ( ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k10_relat_1(sK9,sK8),k1_xboole_0)))
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_27553])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4351,plain,
    ( r2_hidden(X0,k10_relat_1(X1,sK8))
    | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK9),sK8)),X1)
    | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_8179,plain,
    ( r2_hidden(X0,k10_relat_1(sK9,sK8))
    | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_4351])).

cnf(c_12640,plain,
    ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | ~ r2_hidden(k4_tarski(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),sK1(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_8179])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4583,plain,
    ( r2_hidden(k4_tarski(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),sK1(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3960,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | ~ r2_hidden(X0,k10_relat_1(sK9,sK8))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_317,c_25])).

cnf(c_24,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_925,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_928,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1226,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_925,c_928])).

cnf(c_927,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3102,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_927])).

cnf(c_3112,plain,
    ( ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3102])).

cnf(c_314,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2618,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_314,c_313])).

cnf(c_3383,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k10_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2618,c_25])).

cnf(c_3396,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | X0 != k1_xboole_0
    | k10_relat_1(sK9,sK8) = X0 ),
    inference(resolution,[status(thm)],[c_3383,c_314])).

cnf(c_2616,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | X0 != k10_relat_1(sK9,sK8)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_314,c_25])).

cnf(c_3623,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k10_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(resolution,[status(thm)],[c_3396,c_2616])).

cnf(c_332,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_1299,plain,
    ( k10_relat_1(sK9,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_1300,plain,
    ( k10_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK9,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_3626,plain,
    ( k10_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3623,c_332,c_1300])).

cnf(c_910,plain,
    ( k1_xboole_0 = k10_relat_1(sK9,sK8)
    | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1227,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_910,c_928])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_909,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_913,plain,
    ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1529,plain,
    ( k10_relat_1(sK9,k1_setfam_1(k2_tarski(k2_relat_1(sK9),X0))) = k10_relat_1(sK9,X0) ),
    inference(superposition,[status(thm)],[c_909,c_913])).

cnf(c_3761,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | k10_relat_1(sK9,k1_xboole_0) = k10_relat_1(sK9,sK8) ),
    inference(superposition,[status(thm)],[c_1227,c_1529])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_912,plain,
    ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1187,plain,
    ( k10_relat_1(sK9,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_909,c_912])).

cnf(c_3762,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3761,c_1187])).

cnf(c_4250,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK9,sK8))
    | X1 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3960,c_24,c_10,c_332,c_1300,c_3112,c_3762])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1392,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_5,c_9])).

cnf(c_4284,plain,
    ( r1_xboole_0(k10_relat_1(sK9,sK8),X0)
    | X1 != sK1(k10_relat_1(sK9,sK8),X0) ),
    inference(resolution,[status(thm)],[c_4250,c_1392])).

cnf(c_4551,plain,
    ( r1_xboole_0(k10_relat_1(sK9,sK8),X0) ),
    inference(resolution,[status(thm)],[c_4284,c_313])).

cnf(c_4553,plain,
    ( r1_xboole_0(k10_relat_1(sK9,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4551])).

cnf(c_1520,plain,
    ( r2_hidden(sK1(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
    | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1517,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8)))
    | r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1176,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_122132,c_99911,c_99913,c_27555,c_12640,c_4583,c_4553,c_3762,c_3626,c_1520,c_1517,c_1176,c_24,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.37/4.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.37/4.02  
% 27.37/4.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.37/4.02  
% 27.37/4.02  ------  iProver source info
% 27.37/4.02  
% 27.37/4.02  git: date: 2020-06-30 10:37:57 +0100
% 27.37/4.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.37/4.02  git: non_committed_changes: false
% 27.37/4.02  git: last_make_outside_of_git: false
% 27.37/4.02  
% 27.37/4.02  ------ 
% 27.37/4.02  
% 27.37/4.02  ------ Input Options
% 27.37/4.02  
% 27.37/4.02  --out_options                           all
% 27.37/4.02  --tptp_safe_out                         true
% 27.37/4.02  --problem_path                          ""
% 27.37/4.02  --include_path                          ""
% 27.37/4.02  --clausifier                            res/vclausify_rel
% 27.37/4.02  --clausifier_options                    --mode clausify
% 27.37/4.02  --stdin                                 false
% 27.37/4.02  --stats_out                             sel
% 27.37/4.02  
% 27.37/4.02  ------ General Options
% 27.37/4.02  
% 27.37/4.02  --fof                                   false
% 27.37/4.02  --time_out_real                         604.99
% 27.37/4.02  --time_out_virtual                      -1.
% 27.37/4.02  --symbol_type_check                     false
% 27.37/4.02  --clausify_out                          false
% 27.37/4.02  --sig_cnt_out                           false
% 27.37/4.02  --trig_cnt_out                          false
% 27.37/4.02  --trig_cnt_out_tolerance                1.
% 27.37/4.02  --trig_cnt_out_sk_spl                   false
% 27.37/4.02  --abstr_cl_out                          false
% 27.37/4.02  
% 27.37/4.02  ------ Global Options
% 27.37/4.02  
% 27.37/4.02  --schedule                              none
% 27.37/4.02  --add_important_lit                     false
% 27.37/4.02  --prop_solver_per_cl                    1000
% 27.37/4.02  --min_unsat_core                        false
% 27.37/4.02  --soft_assumptions                      false
% 27.37/4.02  --soft_lemma_size                       3
% 27.37/4.02  --prop_impl_unit_size                   0
% 27.37/4.02  --prop_impl_unit                        []
% 27.37/4.02  --share_sel_clauses                     true
% 27.37/4.02  --reset_solvers                         false
% 27.37/4.02  --bc_imp_inh                            [conj_cone]
% 27.37/4.02  --conj_cone_tolerance                   3.
% 27.37/4.02  --extra_neg_conj                        none
% 27.37/4.02  --large_theory_mode                     true
% 27.37/4.02  --prolific_symb_bound                   200
% 27.37/4.02  --lt_threshold                          2000
% 27.37/4.02  --clause_weak_htbl                      true
% 27.37/4.02  --gc_record_bc_elim                     false
% 27.37/4.02  
% 27.37/4.02  ------ Preprocessing Options
% 27.37/4.02  
% 27.37/4.02  --preprocessing_flag                    true
% 27.37/4.02  --time_out_prep_mult                    0.1
% 27.37/4.02  --splitting_mode                        input
% 27.37/4.02  --splitting_grd                         true
% 27.37/4.02  --splitting_cvd                         false
% 27.37/4.02  --splitting_cvd_svl                     false
% 27.37/4.02  --splitting_nvd                         32
% 27.37/4.02  --sub_typing                            true
% 27.37/4.02  --prep_gs_sim                           false
% 27.37/4.02  --prep_unflatten                        true
% 27.37/4.02  --prep_res_sim                          true
% 27.37/4.02  --prep_upred                            true
% 27.37/4.02  --prep_sem_filter                       exhaustive
% 27.37/4.02  --prep_sem_filter_out                   false
% 27.37/4.02  --pred_elim                             false
% 27.37/4.02  --res_sim_input                         true
% 27.37/4.02  --eq_ax_congr_red                       true
% 27.37/4.02  --pure_diseq_elim                       true
% 27.37/4.02  --brand_transform                       false
% 27.37/4.02  --non_eq_to_eq                          false
% 27.37/4.02  --prep_def_merge                        true
% 27.37/4.02  --prep_def_merge_prop_impl              false
% 27.37/4.02  --prep_def_merge_mbd                    true
% 27.37/4.02  --prep_def_merge_tr_red                 false
% 27.37/4.02  --prep_def_merge_tr_cl                  false
% 27.37/4.02  --smt_preprocessing                     true
% 27.37/4.02  --smt_ac_axioms                         fast
% 27.37/4.02  --preprocessed_out                      false
% 27.37/4.02  --preprocessed_stats                    false
% 27.37/4.02  
% 27.37/4.02  ------ Abstraction refinement Options
% 27.37/4.02  
% 27.37/4.02  --abstr_ref                             []
% 27.37/4.02  --abstr_ref_prep                        false
% 27.37/4.02  --abstr_ref_until_sat                   false
% 27.37/4.02  --abstr_ref_sig_restrict                funpre
% 27.37/4.02  --abstr_ref_af_restrict_to_split_sk     false
% 27.37/4.02  --abstr_ref_under                       []
% 27.37/4.02  
% 27.37/4.02  ------ SAT Options
% 27.37/4.02  
% 27.37/4.02  --sat_mode                              false
% 27.37/4.02  --sat_fm_restart_options                ""
% 27.37/4.02  --sat_gr_def                            false
% 27.37/4.02  --sat_epr_types                         true
% 27.37/4.02  --sat_non_cyclic_types                  false
% 27.37/4.02  --sat_finite_models                     false
% 27.37/4.02  --sat_fm_lemmas                         false
% 27.37/4.02  --sat_fm_prep                           false
% 27.37/4.02  --sat_fm_uc_incr                        true
% 27.37/4.02  --sat_out_model                         small
% 27.37/4.02  --sat_out_clauses                       false
% 27.37/4.02  
% 27.37/4.02  ------ QBF Options
% 27.37/4.02  
% 27.37/4.02  --qbf_mode                              false
% 27.37/4.02  --qbf_elim_univ                         false
% 27.37/4.02  --qbf_dom_inst                          none
% 27.37/4.02  --qbf_dom_pre_inst                      false
% 27.37/4.02  --qbf_sk_in                             false
% 27.37/4.02  --qbf_pred_elim                         true
% 27.37/4.02  --qbf_split                             512
% 27.37/4.02  
% 27.37/4.02  ------ BMC1 Options
% 27.37/4.02  
% 27.37/4.02  --bmc1_incremental                      false
% 27.37/4.02  --bmc1_axioms                           reachable_all
% 27.37/4.02  --bmc1_min_bound                        0
% 27.37/4.02  --bmc1_max_bound                        -1
% 27.37/4.02  --bmc1_max_bound_default                -1
% 27.37/4.02  --bmc1_symbol_reachability              true
% 27.37/4.02  --bmc1_property_lemmas                  false
% 27.37/4.02  --bmc1_k_induction                      false
% 27.37/4.02  --bmc1_non_equiv_states                 false
% 27.37/4.02  --bmc1_deadlock                         false
% 27.37/4.02  --bmc1_ucm                              false
% 27.37/4.02  --bmc1_add_unsat_core                   none
% 27.37/4.02  --bmc1_unsat_core_children              false
% 27.37/4.02  --bmc1_unsat_core_extrapolate_axioms    false
% 27.37/4.02  --bmc1_out_stat                         full
% 27.37/4.02  --bmc1_ground_init                      false
% 27.37/4.02  --bmc1_pre_inst_next_state              false
% 27.37/4.02  --bmc1_pre_inst_state                   false
% 27.37/4.02  --bmc1_pre_inst_reach_state             false
% 27.37/4.02  --bmc1_out_unsat_core                   false
% 27.37/4.02  --bmc1_aig_witness_out                  false
% 27.37/4.02  --bmc1_verbose                          false
% 27.37/4.02  --bmc1_dump_clauses_tptp                false
% 27.37/4.02  --bmc1_dump_unsat_core_tptp             false
% 27.37/4.02  --bmc1_dump_file                        -
% 27.37/4.02  --bmc1_ucm_expand_uc_limit              128
% 27.37/4.02  --bmc1_ucm_n_expand_iterations          6
% 27.37/4.02  --bmc1_ucm_extend_mode                  1
% 27.37/4.02  --bmc1_ucm_init_mode                    2
% 27.37/4.02  --bmc1_ucm_cone_mode                    none
% 27.37/4.02  --bmc1_ucm_reduced_relation_type        0
% 27.37/4.02  --bmc1_ucm_relax_model                  4
% 27.37/4.02  --bmc1_ucm_full_tr_after_sat            true
% 27.37/4.02  --bmc1_ucm_expand_neg_assumptions       false
% 27.37/4.02  --bmc1_ucm_layered_model                none
% 27.37/4.02  --bmc1_ucm_max_lemma_size               10
% 27.37/4.02  
% 27.37/4.02  ------ AIG Options
% 27.37/4.02  
% 27.37/4.02  --aig_mode                              false
% 27.37/4.02  
% 27.37/4.02  ------ Instantiation Options
% 27.37/4.02  
% 27.37/4.02  --instantiation_flag                    true
% 27.37/4.02  --inst_sos_flag                         false
% 27.37/4.02  --inst_sos_phase                        true
% 27.37/4.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.37/4.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.37/4.02  --inst_lit_sel_side                     num_symb
% 27.37/4.02  --inst_solver_per_active                1400
% 27.37/4.02  --inst_solver_calls_frac                1.
% 27.37/4.02  --inst_passive_queue_type               priority_queues
% 27.37/4.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.37/4.02  --inst_passive_queues_freq              [25;2]
% 27.37/4.02  --inst_dismatching                      true
% 27.37/4.02  --inst_eager_unprocessed_to_passive     true
% 27.37/4.02  --inst_prop_sim_given                   true
% 27.37/4.02  --inst_prop_sim_new                     false
% 27.37/4.02  --inst_subs_new                         false
% 27.37/4.02  --inst_eq_res_simp                      false
% 27.37/4.02  --inst_subs_given                       false
% 27.37/4.02  --inst_orphan_elimination               true
% 27.37/4.02  --inst_learning_loop_flag               true
% 27.37/4.02  --inst_learning_start                   3000
% 27.37/4.02  --inst_learning_factor                  2
% 27.37/4.02  --inst_start_prop_sim_after_learn       3
% 27.37/4.02  --inst_sel_renew                        solver
% 27.37/4.02  --inst_lit_activity_flag                true
% 27.37/4.02  --inst_restr_to_given                   false
% 27.37/4.02  --inst_activity_threshold               500
% 27.37/4.02  --inst_out_proof                        true
% 27.37/4.02  
% 27.37/4.02  ------ Resolution Options
% 27.37/4.02  
% 27.37/4.02  --resolution_flag                       true
% 27.37/4.02  --res_lit_sel                           adaptive
% 27.37/4.02  --res_lit_sel_side                      none
% 27.37/4.02  --res_ordering                          kbo
% 27.37/4.02  --res_to_prop_solver                    active
% 27.37/4.02  --res_prop_simpl_new                    false
% 27.37/4.02  --res_prop_simpl_given                  true
% 27.37/4.02  --res_passive_queue_type                priority_queues
% 27.37/4.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.37/4.02  --res_passive_queues_freq               [15;5]
% 27.37/4.02  --res_forward_subs                      full
% 27.37/4.02  --res_backward_subs                     full
% 27.37/4.02  --res_forward_subs_resolution           true
% 27.37/4.02  --res_backward_subs_resolution          true
% 27.37/4.02  --res_orphan_elimination                true
% 27.37/4.02  --res_time_limit                        2.
% 27.37/4.02  --res_out_proof                         true
% 27.37/4.02  
% 27.37/4.02  ------ Superposition Options
% 27.37/4.02  
% 27.37/4.02  --superposition_flag                    true
% 27.37/4.02  --sup_passive_queue_type                priority_queues
% 27.37/4.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.37/4.02  --sup_passive_queues_freq               [1;4]
% 27.37/4.02  --demod_completeness_check              fast
% 27.37/4.02  --demod_use_ground                      true
% 27.37/4.02  --sup_to_prop_solver                    passive
% 27.37/4.02  --sup_prop_simpl_new                    true
% 27.37/4.02  --sup_prop_simpl_given                  true
% 27.37/4.02  --sup_fun_splitting                     false
% 27.37/4.02  --sup_smt_interval                      50000
% 27.37/4.02  
% 27.37/4.02  ------ Superposition Simplification Setup
% 27.37/4.02  
% 27.37/4.02  --sup_indices_passive                   []
% 27.37/4.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/4.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/4.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/4.02  --sup_full_triv                         [TrivRules;PropSubs]
% 27.37/4.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/4.02  --sup_full_bw                           [BwDemod]
% 27.37/4.02  --sup_immed_triv                        [TrivRules]
% 27.37/4.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.37/4.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/4.02  --sup_immed_bw_main                     []
% 27.37/4.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.37/4.02  --sup_input_triv                        [Unflattening;TrivRules]
% 27.37/4.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/4.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.37/4.02  
% 27.37/4.02  ------ Combination Options
% 27.37/4.02  
% 27.37/4.02  --comb_res_mult                         3
% 27.37/4.02  --comb_sup_mult                         2
% 27.37/4.02  --comb_inst_mult                        10
% 27.37/4.02  
% 27.37/4.02  ------ Debug Options
% 27.37/4.02  
% 27.37/4.02  --dbg_backtrace                         false
% 27.37/4.02  --dbg_dump_prop_clauses                 false
% 27.37/4.02  --dbg_dump_prop_clauses_file            -
% 27.37/4.02  --dbg_out_stat                          false
% 27.37/4.02  ------ Parsing...
% 27.37/4.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.37/4.02  
% 27.37/4.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 27.37/4.02  
% 27.37/4.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.37/4.02  
% 27.37/4.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.37/4.02  ------ Proving...
% 27.37/4.02  ------ Problem Properties 
% 27.37/4.02  
% 27.37/4.02  
% 27.37/4.02  clauses                                 27
% 27.37/4.02  conjectures                             3
% 27.37/4.02  EPR                                     2
% 27.37/4.02  Horn                                    20
% 27.37/4.02  unary                                   2
% 27.37/4.02  binary                                  13
% 27.37/4.02  lits                                    70
% 27.37/4.02  lits eq                                 14
% 27.37/4.02  fd_pure                                 0
% 27.37/4.02  fd_pseudo                               0
% 27.37/4.02  fd_cond                                 0
% 27.37/4.02  fd_pseudo_cond                          8
% 27.37/4.02  AC symbols                              0
% 27.37/4.02  
% 27.37/4.02  ------ Input Options Time Limit: Unbounded
% 27.37/4.02  
% 27.37/4.02  
% 27.37/4.02  ------ 
% 27.37/4.02  Current options:
% 27.37/4.02  ------ 
% 27.37/4.02  
% 27.37/4.02  ------ Input Options
% 27.37/4.02  
% 27.37/4.02  --out_options                           all
% 27.37/4.02  --tptp_safe_out                         true
% 27.37/4.02  --problem_path                          ""
% 27.37/4.02  --include_path                          ""
% 27.37/4.02  --clausifier                            res/vclausify_rel
% 27.37/4.02  --clausifier_options                    --mode clausify
% 27.37/4.02  --stdin                                 false
% 27.37/4.02  --stats_out                             sel
% 27.37/4.02  
% 27.37/4.02  ------ General Options
% 27.37/4.02  
% 27.37/4.02  --fof                                   false
% 27.37/4.02  --time_out_real                         604.99
% 27.37/4.02  --time_out_virtual                      -1.
% 27.37/4.02  --symbol_type_check                     false
% 27.37/4.02  --clausify_out                          false
% 27.37/4.02  --sig_cnt_out                           false
% 27.37/4.02  --trig_cnt_out                          false
% 27.37/4.02  --trig_cnt_out_tolerance                1.
% 27.37/4.02  --trig_cnt_out_sk_spl                   false
% 27.37/4.02  --abstr_cl_out                          false
% 27.37/4.02  
% 27.37/4.02  ------ Global Options
% 27.37/4.02  
% 27.37/4.02  --schedule                              none
% 27.37/4.02  --add_important_lit                     false
% 27.37/4.02  --prop_solver_per_cl                    1000
% 27.37/4.02  --min_unsat_core                        false
% 27.37/4.02  --soft_assumptions                      false
% 27.37/4.02  --soft_lemma_size                       3
% 27.37/4.02  --prop_impl_unit_size                   0
% 27.37/4.02  --prop_impl_unit                        []
% 27.37/4.02  --share_sel_clauses                     true
% 27.37/4.02  --reset_solvers                         false
% 27.37/4.02  --bc_imp_inh                            [conj_cone]
% 27.37/4.02  --conj_cone_tolerance                   3.
% 27.37/4.02  --extra_neg_conj                        none
% 27.37/4.02  --large_theory_mode                     true
% 27.37/4.02  --prolific_symb_bound                   200
% 27.37/4.02  --lt_threshold                          2000
% 27.37/4.02  --clause_weak_htbl                      true
% 27.37/4.02  --gc_record_bc_elim                     false
% 27.37/4.02  
% 27.37/4.02  ------ Preprocessing Options
% 27.37/4.02  
% 27.37/4.02  --preprocessing_flag                    true
% 27.37/4.02  --time_out_prep_mult                    0.1
% 27.37/4.02  --splitting_mode                        input
% 27.37/4.02  --splitting_grd                         true
% 27.37/4.02  --splitting_cvd                         false
% 27.37/4.02  --splitting_cvd_svl                     false
% 27.37/4.02  --splitting_nvd                         32
% 27.37/4.02  --sub_typing                            true
% 27.37/4.02  --prep_gs_sim                           false
% 27.37/4.02  --prep_unflatten                        true
% 27.37/4.02  --prep_res_sim                          true
% 27.37/4.02  --prep_upred                            true
% 27.37/4.02  --prep_sem_filter                       exhaustive
% 27.37/4.02  --prep_sem_filter_out                   false
% 27.37/4.02  --pred_elim                             false
% 27.37/4.02  --res_sim_input                         true
% 27.37/4.02  --eq_ax_congr_red                       true
% 27.37/4.02  --pure_diseq_elim                       true
% 27.37/4.02  --brand_transform                       false
% 27.37/4.02  --non_eq_to_eq                          false
% 27.37/4.02  --prep_def_merge                        true
% 27.37/4.02  --prep_def_merge_prop_impl              false
% 27.37/4.02  --prep_def_merge_mbd                    true
% 27.37/4.02  --prep_def_merge_tr_red                 false
% 27.37/4.02  --prep_def_merge_tr_cl                  false
% 27.37/4.02  --smt_preprocessing                     true
% 27.37/4.02  --smt_ac_axioms                         fast
% 27.37/4.02  --preprocessed_out                      false
% 27.37/4.02  --preprocessed_stats                    false
% 27.37/4.02  
% 27.37/4.02  ------ Abstraction refinement Options
% 27.37/4.02  
% 27.37/4.02  --abstr_ref                             []
% 27.37/4.02  --abstr_ref_prep                        false
% 27.37/4.02  --abstr_ref_until_sat                   false
% 27.37/4.02  --abstr_ref_sig_restrict                funpre
% 27.37/4.02  --abstr_ref_af_restrict_to_split_sk     false
% 27.37/4.02  --abstr_ref_under                       []
% 27.37/4.02  
% 27.37/4.02  ------ SAT Options
% 27.37/4.02  
% 27.37/4.02  --sat_mode                              false
% 27.37/4.02  --sat_fm_restart_options                ""
% 27.37/4.02  --sat_gr_def                            false
% 27.37/4.02  --sat_epr_types                         true
% 27.37/4.02  --sat_non_cyclic_types                  false
% 27.37/4.02  --sat_finite_models                     false
% 27.37/4.02  --sat_fm_lemmas                         false
% 27.37/4.02  --sat_fm_prep                           false
% 27.37/4.02  --sat_fm_uc_incr                        true
% 27.37/4.02  --sat_out_model                         small
% 27.37/4.02  --sat_out_clauses                       false
% 27.37/4.02  
% 27.37/4.02  ------ QBF Options
% 27.37/4.02  
% 27.37/4.02  --qbf_mode                              false
% 27.37/4.02  --qbf_elim_univ                         false
% 27.37/4.02  --qbf_dom_inst                          none
% 27.37/4.02  --qbf_dom_pre_inst                      false
% 27.37/4.02  --qbf_sk_in                             false
% 27.37/4.02  --qbf_pred_elim                         true
% 27.37/4.02  --qbf_split                             512
% 27.37/4.02  
% 27.37/4.02  ------ BMC1 Options
% 27.37/4.02  
% 27.37/4.02  --bmc1_incremental                      false
% 27.37/4.02  --bmc1_axioms                           reachable_all
% 27.37/4.02  --bmc1_min_bound                        0
% 27.37/4.02  --bmc1_max_bound                        -1
% 27.37/4.02  --bmc1_max_bound_default                -1
% 27.37/4.02  --bmc1_symbol_reachability              true
% 27.37/4.02  --bmc1_property_lemmas                  false
% 27.37/4.02  --bmc1_k_induction                      false
% 27.37/4.02  --bmc1_non_equiv_states                 false
% 27.37/4.02  --bmc1_deadlock                         false
% 27.37/4.02  --bmc1_ucm                              false
% 27.37/4.02  --bmc1_add_unsat_core                   none
% 27.37/4.02  --bmc1_unsat_core_children              false
% 27.37/4.02  --bmc1_unsat_core_extrapolate_axioms    false
% 27.37/4.02  --bmc1_out_stat                         full
% 27.37/4.02  --bmc1_ground_init                      false
% 27.37/4.02  --bmc1_pre_inst_next_state              false
% 27.37/4.02  --bmc1_pre_inst_state                   false
% 27.37/4.02  --bmc1_pre_inst_reach_state             false
% 27.37/4.02  --bmc1_out_unsat_core                   false
% 27.37/4.02  --bmc1_aig_witness_out                  false
% 27.37/4.02  --bmc1_verbose                          false
% 27.37/4.02  --bmc1_dump_clauses_tptp                false
% 27.37/4.02  --bmc1_dump_unsat_core_tptp             false
% 27.37/4.02  --bmc1_dump_file                        -
% 27.37/4.02  --bmc1_ucm_expand_uc_limit              128
% 27.37/4.02  --bmc1_ucm_n_expand_iterations          6
% 27.37/4.02  --bmc1_ucm_extend_mode                  1
% 27.37/4.02  --bmc1_ucm_init_mode                    2
% 27.37/4.02  --bmc1_ucm_cone_mode                    none
% 27.37/4.02  --bmc1_ucm_reduced_relation_type        0
% 27.37/4.02  --bmc1_ucm_relax_model                  4
% 27.37/4.02  --bmc1_ucm_full_tr_after_sat            true
% 27.37/4.02  --bmc1_ucm_expand_neg_assumptions       false
% 27.37/4.02  --bmc1_ucm_layered_model                none
% 27.37/4.02  --bmc1_ucm_max_lemma_size               10
% 27.37/4.02  
% 27.37/4.02  ------ AIG Options
% 27.37/4.02  
% 27.37/4.02  --aig_mode                              false
% 27.37/4.02  
% 27.37/4.02  ------ Instantiation Options
% 27.37/4.02  
% 27.37/4.02  --instantiation_flag                    true
% 27.37/4.02  --inst_sos_flag                         false
% 27.37/4.02  --inst_sos_phase                        true
% 27.37/4.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.37/4.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.37/4.02  --inst_lit_sel_side                     num_symb
% 27.37/4.02  --inst_solver_per_active                1400
% 27.37/4.02  --inst_solver_calls_frac                1.
% 27.37/4.02  --inst_passive_queue_type               priority_queues
% 27.37/4.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.37/4.02  --inst_passive_queues_freq              [25;2]
% 27.37/4.02  --inst_dismatching                      true
% 27.37/4.02  --inst_eager_unprocessed_to_passive     true
% 27.37/4.02  --inst_prop_sim_given                   true
% 27.37/4.02  --inst_prop_sim_new                     false
% 27.37/4.02  --inst_subs_new                         false
% 27.37/4.02  --inst_eq_res_simp                      false
% 27.37/4.02  --inst_subs_given                       false
% 27.37/4.02  --inst_orphan_elimination               true
% 27.37/4.02  --inst_learning_loop_flag               true
% 27.37/4.02  --inst_learning_start                   3000
% 27.37/4.02  --inst_learning_factor                  2
% 27.37/4.02  --inst_start_prop_sim_after_learn       3
% 27.37/4.02  --inst_sel_renew                        solver
% 27.37/4.02  --inst_lit_activity_flag                true
% 27.37/4.02  --inst_restr_to_given                   false
% 27.37/4.02  --inst_activity_threshold               500
% 27.37/4.02  --inst_out_proof                        true
% 27.37/4.02  
% 27.37/4.02  ------ Resolution Options
% 27.37/4.02  
% 27.37/4.02  --resolution_flag                       true
% 27.37/4.02  --res_lit_sel                           adaptive
% 27.37/4.02  --res_lit_sel_side                      none
% 27.37/4.02  --res_ordering                          kbo
% 27.37/4.02  --res_to_prop_solver                    active
% 27.37/4.02  --res_prop_simpl_new                    false
% 27.37/4.02  --res_prop_simpl_given                  true
% 27.37/4.02  --res_passive_queue_type                priority_queues
% 27.37/4.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.37/4.02  --res_passive_queues_freq               [15;5]
% 27.37/4.02  --res_forward_subs                      full
% 27.37/4.02  --res_backward_subs                     full
% 27.37/4.02  --res_forward_subs_resolution           true
% 27.37/4.02  --res_backward_subs_resolution          true
% 27.37/4.02  --res_orphan_elimination                true
% 27.37/4.02  --res_time_limit                        2.
% 27.37/4.02  --res_out_proof                         true
% 27.37/4.02  
% 27.37/4.02  ------ Superposition Options
% 27.37/4.02  
% 27.37/4.02  --superposition_flag                    true
% 27.37/4.02  --sup_passive_queue_type                priority_queues
% 27.37/4.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.37/4.02  --sup_passive_queues_freq               [1;4]
% 27.37/4.02  --demod_completeness_check              fast
% 27.37/4.02  --demod_use_ground                      true
% 27.37/4.02  --sup_to_prop_solver                    passive
% 27.37/4.02  --sup_prop_simpl_new                    true
% 27.37/4.02  --sup_prop_simpl_given                  true
% 27.37/4.02  --sup_fun_splitting                     false
% 27.37/4.02  --sup_smt_interval                      50000
% 27.37/4.02  
% 27.37/4.02  ------ Superposition Simplification Setup
% 27.37/4.02  
% 27.37/4.02  --sup_indices_passive                   []
% 27.37/4.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/4.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/4.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/4.02  --sup_full_triv                         [TrivRules;PropSubs]
% 27.37/4.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/4.02  --sup_full_bw                           [BwDemod]
% 27.37/4.02  --sup_immed_triv                        [TrivRules]
% 27.37/4.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.37/4.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/4.02  --sup_immed_bw_main                     []
% 27.37/4.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.37/4.02  --sup_input_triv                        [Unflattening;TrivRules]
% 27.37/4.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/4.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.37/4.02  
% 27.37/4.02  ------ Combination Options
% 27.37/4.02  
% 27.37/4.02  --comb_res_mult                         3
% 27.37/4.02  --comb_sup_mult                         2
% 27.37/4.02  --comb_inst_mult                        10
% 27.37/4.02  
% 27.37/4.02  ------ Debug Options
% 27.37/4.02  
% 27.37/4.02  --dbg_backtrace                         false
% 27.37/4.02  --dbg_dump_prop_clauses                 false
% 27.37/4.02  --dbg_dump_prop_clauses_file            -
% 27.37/4.02  --dbg_out_stat                          false
% 27.37/4.02  
% 27.37/4.02  
% 27.37/4.02  
% 27.37/4.02  
% 27.37/4.02  ------ Proving...
% 27.37/4.02  
% 27.37/4.02  
% 27.37/4.02  % SZS status Theorem for theBenchmark.p
% 27.37/4.02  
% 27.37/4.02  % SZS output start CNFRefutation for theBenchmark.p
% 27.37/4.02  
% 27.37/4.02  fof(f3,axiom,(
% 27.37/4.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.37/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.37/4.02  
% 27.37/4.02  fof(f13,plain,(
% 27.37/4.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.37/4.02    inference(rectify,[],[f3])).
% 27.37/4.02  
% 27.37/4.02  fof(f14,plain,(
% 27.37/4.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.37/4.02    inference(ennf_transformation,[],[f13])).
% 27.37/4.02  
% 27.37/4.02  fof(f26,plain,(
% 27.37/4.02    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 27.37/4.02    introduced(choice_axiom,[])).
% 27.37/4.02  
% 27.37/4.02  fof(f27,plain,(
% 27.37/4.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.37/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f26])).
% 27.37/4.02  
% 27.37/4.02  fof(f53,plain,(
% 27.37/4.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 27.37/4.02    inference(cnf_transformation,[],[f27])).
% 27.37/4.02  
% 27.37/4.02  fof(f6,axiom,(
% 27.37/4.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 27.37/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.37/4.02  
% 27.37/4.02  fof(f56,plain,(
% 27.37/4.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 27.37/4.02    inference(cnf_transformation,[],[f6])).
% 27.37/4.02  
% 27.37/4.02  fof(f80,plain,(
% 27.37/4.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 27.37/4.02    inference(definition_unfolding,[],[f53,f56])).
% 27.37/4.02  
% 27.37/4.02  fof(f1,axiom,(
% 27.37/4.02    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 27.37/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.37/4.02  
% 27.37/4.02  fof(f20,plain,(
% 27.37/4.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.37/4.02    inference(nnf_transformation,[],[f1])).
% 27.37/4.02  
% 27.37/4.02  fof(f21,plain,(
% 27.37/4.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.37/4.02    inference(flattening,[],[f20])).
% 27.37/4.02  
% 27.37/4.02  fof(f22,plain,(
% 27.37/4.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.37/4.02    inference(rectify,[],[f21])).
% 27.37/4.02  
% 27.37/4.02  fof(f23,plain,(
% 27.37/4.02    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 27.37/4.02    introduced(choice_axiom,[])).
% 27.37/4.02  
% 27.37/4.02  fof(f24,plain,(
% 27.37/4.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.37/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 27.37/4.02  
% 27.37/4.02  fof(f46,plain,(
% 27.37/4.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 27.37/4.02    inference(cnf_transformation,[],[f24])).
% 27.37/4.02  
% 27.37/4.02  fof(f75,plain,(
% 27.37/4.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 27.37/4.02    inference(definition_unfolding,[],[f46,f56])).
% 27.37/4.02  
% 27.37/4.02  fof(f83,plain,(
% 27.37/4.02    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 27.37/4.02    inference(equality_resolution,[],[f75])).
% 27.37/4.02  
% 27.37/4.02  fof(f7,axiom,(
% 27.37/4.02    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 27.37/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.37/4.02  
% 27.37/4.02  fof(f16,plain,(
% 27.37/4.02    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 27.37/4.02    inference(ennf_transformation,[],[f7])).
% 27.37/4.02  
% 27.37/4.02  fof(f28,plain,(
% 27.37/4.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 27.37/4.02    inference(nnf_transformation,[],[f16])).
% 27.37/4.02  
% 27.37/4.02  fof(f29,plain,(
% 27.37/4.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 27.37/4.02    inference(rectify,[],[f28])).
% 27.37/4.02  
% 27.37/4.02  fof(f32,plain,(
% 27.37/4.02    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)))),
% 27.37/4.02    introduced(choice_axiom,[])).
% 27.37/4.02  
% 27.37/4.02  fof(f31,plain,(
% 27.37/4.02    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0)))) )),
% 27.37/4.02    introduced(choice_axiom,[])).
% 27.37/4.02  
% 27.37/4.02  fof(f30,plain,(
% 27.37/4.02    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 27.37/4.02    introduced(choice_axiom,[])).
% 27.37/4.02  
% 27.37/4.02  fof(f33,plain,(
% 27.37/4.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 27.37/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).
% 27.37/4.02  
% 27.37/4.02  fof(f59,plain,(
% 27.37/4.02    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 27.37/4.02    inference(cnf_transformation,[],[f33])).
% 27.37/4.02  
% 27.37/4.02  fof(f86,plain,(
% 27.37/4.02    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 27.37/4.02    inference(equality_resolution,[],[f59])).
% 27.37/4.02  
% 27.37/4.02  fof(f8,axiom,(
% 27.37/4.02    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 27.37/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.37/4.02  
% 27.37/4.02  fof(f34,plain,(
% 27.37/4.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 27.37/4.02    inference(nnf_transformation,[],[f8])).
% 27.37/4.02  
% 27.37/4.02  fof(f35,plain,(
% 27.37/4.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 27.37/4.02    inference(rectify,[],[f34])).
% 27.37/4.02  
% 27.37/4.02  fof(f38,plain,(
% 27.37/4.02    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 27.37/4.02    introduced(choice_axiom,[])).
% 27.37/4.02  
% 27.37/4.02  fof(f37,plain,(
% 27.37/4.02    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0))) )),
% 27.37/4.02    introduced(choice_axiom,[])).
% 27.37/4.02  
% 27.37/4.02  fof(f36,plain,(
% 27.37/4.02    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 27.37/4.02    introduced(choice_axiom,[])).
% 27.37/4.02  
% 27.37/4.02  fof(f39,plain,(
% 27.37/4.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 27.37/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f35,f38,f37,f36])).
% 27.37/4.02  
% 27.37/4.02  fof(f63,plain,(
% 27.37/4.02    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 27.37/4.02    inference(cnf_transformation,[],[f39])).
% 27.37/4.02  
% 27.37/4.02  fof(f90,plain,(
% 27.37/4.02    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 27.37/4.02    inference(equality_resolution,[],[f63])).
% 27.37/4.02  
% 27.37/4.02  fof(f11,conjecture,(
% 27.37/4.02    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 27.37/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.37/4.02  
% 27.37/4.02  fof(f12,negated_conjecture,(
% 27.37/4.02    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 27.37/4.02    inference(negated_conjecture,[],[f11])).
% 27.37/4.02  
% 27.37/4.02  fof(f19,plain,(
% 27.37/4.02    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 27.37/4.02    inference(ennf_transformation,[],[f12])).
% 27.37/4.02  
% 27.37/4.02  fof(f40,plain,(
% 27.37/4.02    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 27.37/4.02    inference(nnf_transformation,[],[f19])).
% 27.37/4.02  
% 27.37/4.02  fof(f41,plain,(
% 27.37/4.02    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 27.37/4.02    inference(flattening,[],[f40])).
% 27.37/4.02  
% 27.37/4.02  fof(f42,plain,(
% 27.37/4.02    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)) & (r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)) & v1_relat_1(sK9))),
% 27.37/4.02    introduced(choice_axiom,[])).
% 27.37/4.02  
% 27.37/4.02  fof(f43,plain,(
% 27.37/4.02    (~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)) & (r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)) & v1_relat_1(sK9)),
% 27.37/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f41,f42])).
% 27.37/4.02  
% 27.37/4.02  fof(f70,plain,(
% 27.37/4.02    r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)),
% 27.37/4.02    inference(cnf_transformation,[],[f43])).
% 27.37/4.02  
% 27.37/4.02  fof(f71,plain,(
% 27.37/4.02    ~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)),
% 27.37/4.02    inference(cnf_transformation,[],[f43])).
% 27.37/4.02  
% 27.37/4.02  fof(f4,axiom,(
% 27.37/4.02    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 27.37/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.37/4.02  
% 27.37/4.02  fof(f54,plain,(
% 27.37/4.02    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 27.37/4.02    inference(cnf_transformation,[],[f4])).
% 27.37/4.02  
% 27.37/4.02  fof(f2,axiom,(
% 27.37/4.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 27.37/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.37/4.02  
% 27.37/4.02  fof(f25,plain,(
% 27.37/4.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 27.37/4.02    inference(nnf_transformation,[],[f2])).
% 27.37/4.02  
% 27.37/4.02  fof(f50,plain,(
% 27.37/4.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 27.37/4.02    inference(cnf_transformation,[],[f25])).
% 27.37/4.02  
% 27.37/4.02  fof(f79,plain,(
% 27.37/4.02    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 27.37/4.02    inference(definition_unfolding,[],[f50,f56])).
% 27.37/4.02  
% 27.37/4.02  fof(f69,plain,(
% 27.37/4.02    v1_relat_1(sK9)),
% 27.37/4.02    inference(cnf_transformation,[],[f43])).
% 27.37/4.02  
% 27.37/4.02  fof(f9,axiom,(
% 27.37/4.02    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 27.37/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.37/4.02  
% 27.37/4.02  fof(f17,plain,(
% 27.37/4.02    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 27.37/4.02    inference(ennf_transformation,[],[f9])).
% 27.37/4.02  
% 27.37/4.02  fof(f67,plain,(
% 27.37/4.02    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 27.37/4.02    inference(cnf_transformation,[],[f17])).
% 27.37/4.02  
% 27.37/4.02  fof(f82,plain,(
% 27.37/4.02    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 27.37/4.02    inference(definition_unfolding,[],[f67,f56])).
% 27.37/4.02  
% 27.37/4.02  fof(f10,axiom,(
% 27.37/4.02    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 27.37/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.37/4.02  
% 27.37/4.02  fof(f18,plain,(
% 27.37/4.02    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 27.37/4.02    inference(ennf_transformation,[],[f10])).
% 27.37/4.02  
% 27.37/4.02  fof(f68,plain,(
% 27.37/4.02    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 27.37/4.02    inference(cnf_transformation,[],[f18])).
% 27.37/4.02  
% 27.37/4.02  fof(f44,plain,(
% 27.37/4.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 27.37/4.02    inference(cnf_transformation,[],[f24])).
% 27.37/4.02  
% 27.37/4.02  fof(f77,plain,(
% 27.37/4.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 27.37/4.02    inference(definition_unfolding,[],[f44,f56])).
% 27.37/4.02  
% 27.37/4.02  fof(f85,plain,(
% 27.37/4.02    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 27.37/4.02    inference(equality_resolution,[],[f77])).
% 27.37/4.02  
% 27.37/4.02  fof(f52,plain,(
% 27.37/4.02    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 27.37/4.02    inference(cnf_transformation,[],[f27])).
% 27.37/4.02  
% 27.37/4.02  fof(f81,plain,(
% 27.37/4.02    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 27.37/4.02    inference(definition_unfolding,[],[f52,f56])).
% 27.37/4.02  
% 27.37/4.02  fof(f45,plain,(
% 27.37/4.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 27.37/4.02    inference(cnf_transformation,[],[f24])).
% 27.37/4.02  
% 27.37/4.02  fof(f76,plain,(
% 27.37/4.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 27.37/4.02    inference(definition_unfolding,[],[f45,f56])).
% 27.37/4.02  
% 27.37/4.02  fof(f84,plain,(
% 27.37/4.02    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 27.37/4.02    inference(equality_resolution,[],[f76])).
% 27.37/4.02  
% 27.37/4.02  cnf(c_8,plain,
% 27.37/4.02      ( ~ r1_xboole_0(X0,X1)
% 27.37/4.02      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ),
% 27.37/4.02      inference(cnf_transformation,[],[f80]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_122130,plain,
% 27.37/4.02      ( ~ r1_xboole_0(k10_relat_1(sK9,sK8),X0)
% 27.37/4.02      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k10_relat_1(sK9,sK8),X0))) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_8]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_122132,plain,
% 27.37/4.02      ( ~ r1_xboole_0(k10_relat_1(sK9,sK8),k1_xboole_0)
% 27.37/4.02      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k10_relat_1(sK9,sK8),k1_xboole_0))) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_122130]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_313,plain,( X0 = X0 ),theory(equality) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_99911,plain,
% 27.37/4.02      ( sK7(sK9,sK1(k2_relat_1(sK9),sK8)) = sK7(sK9,sK1(k2_relat_1(sK9),sK8)) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_313]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_317,plain,
% 27.37/4.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.37/4.02      theory(equality) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_27537,plain,
% 27.37/4.02      ( r2_hidden(X0,X1)
% 27.37/4.02      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 27.37/4.02      | X0 != sK7(sK9,sK1(k2_relat_1(sK9),sK8))
% 27.37/4.02      | X1 != k10_relat_1(sK9,sK8) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_317]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_99910,plain,
% 27.37/4.02      ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X0)
% 27.37/4.02      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 27.37/4.02      | X0 != k10_relat_1(sK9,sK8)
% 27.37/4.02      | sK7(sK9,sK1(k2_relat_1(sK9),sK8)) != sK7(sK9,sK1(k2_relat_1(sK9),sK8)) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_27537]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_99913,plain,
% 27.37/4.02      ( ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 27.37/4.02      | r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_xboole_0)
% 27.37/4.02      | sK7(sK9,sK1(k2_relat_1(sK9),sK8)) != sK7(sK9,sK1(k2_relat_1(sK9),sK8))
% 27.37/4.02      | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_99910]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_3,plain,
% 27.37/4.02      ( ~ r2_hidden(X0,X1)
% 27.37/4.02      | ~ r2_hidden(X0,X2)
% 27.37/4.02      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 27.37/4.02      inference(cnf_transformation,[],[f83]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_27553,plain,
% 27.37/4.02      ( ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X0)
% 27.37/4.02      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 27.37/4.02      | r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k10_relat_1(sK9,sK8),X0))) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_3]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_27555,plain,
% 27.37/4.02      ( ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 27.37/4.02      | r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k10_relat_1(sK9,sK8),k1_xboole_0)))
% 27.37/4.02      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_xboole_0) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_27553]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_15,plain,
% 27.37/4.02      ( ~ r2_hidden(X0,X1)
% 27.37/4.02      | r2_hidden(X2,k10_relat_1(X3,X1))
% 27.37/4.02      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 27.37/4.02      | ~ v1_relat_1(X3) ),
% 27.37/4.02      inference(cnf_transformation,[],[f86]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_4351,plain,
% 27.37/4.02      ( r2_hidden(X0,k10_relat_1(X1,sK8))
% 27.37/4.02      | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK9),sK8)),X1)
% 27.37/4.02      | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8)
% 27.37/4.02      | ~ v1_relat_1(X1) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_15]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_8179,plain,
% 27.37/4.02      ( r2_hidden(X0,k10_relat_1(sK9,sK8))
% 27.37/4.02      | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK9),sK8)),sK9)
% 27.37/4.02      | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8)
% 27.37/4.02      | ~ v1_relat_1(sK9) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_4351]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_12640,plain,
% 27.37/4.02      ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 27.37/4.02      | ~ r2_hidden(k4_tarski(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),sK1(k2_relat_1(sK9),sK8)),sK9)
% 27.37/4.02      | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8)
% 27.37/4.02      | ~ v1_relat_1(sK9) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_8179]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_21,plain,
% 27.37/4.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 27.37/4.02      | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
% 27.37/4.02      inference(cnf_transformation,[],[f90]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_4583,plain,
% 27.37/4.02      ( r2_hidden(k4_tarski(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),sK1(k2_relat_1(sK9),sK8)),sK9)
% 27.37/4.02      | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_21]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_25,negated_conjecture,
% 27.37/4.02      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 27.37/4.02      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 27.37/4.02      inference(cnf_transformation,[],[f70]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_3960,plain,
% 27.37/4.02      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 27.37/4.02      | ~ r2_hidden(X0,k10_relat_1(sK9,sK8))
% 27.37/4.02      | r2_hidden(X1,k1_xboole_0)
% 27.37/4.02      | X1 != X0 ),
% 27.37/4.02      inference(resolution,[status(thm)],[c_317,c_25]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_24,negated_conjecture,
% 27.37/4.02      ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
% 27.37/4.02      | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
% 27.37/4.02      inference(cnf_transformation,[],[f71]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_10,plain,
% 27.37/4.02      ( r1_xboole_0(X0,k1_xboole_0) ),
% 27.37/4.02      inference(cnf_transformation,[],[f54]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_925,plain,
% 27.37/4.02      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 27.37/4.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_7,plain,
% 27.37/4.02      ( ~ r1_xboole_0(X0,X1)
% 27.37/4.02      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 27.37/4.02      inference(cnf_transformation,[],[f79]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_928,plain,
% 27.37/4.02      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 27.37/4.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 27.37/4.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_1226,plain,
% 27.37/4.02      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.37/4.02      inference(superposition,[status(thm)],[c_925,c_928]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_927,plain,
% 27.37/4.02      ( r1_xboole_0(X0,X1) != iProver_top
% 27.37/4.02      | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
% 27.37/4.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_3102,plain,
% 27.37/4.02      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 27.37/4.02      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 27.37/4.02      inference(superposition,[status(thm)],[c_1226,c_927]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_3112,plain,
% 27.37/4.02      ( ~ r1_xboole_0(X0,k1_xboole_0) | ~ r2_hidden(X1,k1_xboole_0) ),
% 27.37/4.02      inference(predicate_to_equality_rev,[status(thm)],[c_3102]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_314,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_2618,plain,
% 27.37/4.02      ( X0 != X1 | X1 = X0 ),
% 27.37/4.02      inference(resolution,[status(thm)],[c_314,c_313]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_3383,plain,
% 27.37/4.02      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 27.37/4.02      | k10_relat_1(sK9,sK8) = k1_xboole_0 ),
% 27.37/4.02      inference(resolution,[status(thm)],[c_2618,c_25]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_3396,plain,
% 27.37/4.02      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 27.37/4.02      | X0 != k1_xboole_0
% 27.37/4.02      | k10_relat_1(sK9,sK8) = X0 ),
% 27.37/4.02      inference(resolution,[status(thm)],[c_3383,c_314]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_2616,plain,
% 27.37/4.02      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 27.37/4.02      | X0 != k10_relat_1(sK9,sK8)
% 27.37/4.02      | k1_xboole_0 = X0 ),
% 27.37/4.02      inference(resolution,[status(thm)],[c_314,c_25]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_3623,plain,
% 27.37/4.02      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 27.37/4.02      | k10_relat_1(sK9,sK8) != k1_xboole_0
% 27.37/4.02      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 27.37/4.02      inference(resolution,[status(thm)],[c_3396,c_2616]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_332,plain,
% 27.37/4.02      ( k1_xboole_0 = k1_xboole_0 ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_313]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_1299,plain,
% 27.37/4.02      ( k10_relat_1(sK9,sK8) != X0
% 27.37/4.02      | k1_xboole_0 != X0
% 27.37/4.02      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_314]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_1300,plain,
% 27.37/4.02      ( k10_relat_1(sK9,sK8) != k1_xboole_0
% 27.37/4.02      | k1_xboole_0 = k10_relat_1(sK9,sK8)
% 27.37/4.02      | k1_xboole_0 != k1_xboole_0 ),
% 27.37/4.02      inference(instantiation,[status(thm)],[c_1299]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_3626,plain,
% 27.37/4.02      ( k10_relat_1(sK9,sK8) != k1_xboole_0
% 27.37/4.02      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 27.37/4.02      inference(global_propositional_subsumption,
% 27.37/4.02                [status(thm)],
% 27.37/4.02                [c_3623,c_332,c_1300]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_910,plain,
% 27.37/4.02      ( k1_xboole_0 = k10_relat_1(sK9,sK8)
% 27.37/4.02      | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
% 27.37/4.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_1227,plain,
% 27.37/4.02      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 27.37/4.02      | k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8)) = k1_xboole_0 ),
% 27.37/4.02      inference(superposition,[status(thm)],[c_910,c_928]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_26,negated_conjecture,
% 27.37/4.02      ( v1_relat_1(sK9) ),
% 27.37/4.02      inference(cnf_transformation,[],[f69]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_909,plain,
% 27.37/4.02      ( v1_relat_1(sK9) = iProver_top ),
% 27.37/4.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_22,plain,
% 27.37/4.02      ( ~ v1_relat_1(X0)
% 27.37/4.02      | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 27.37/4.02      inference(cnf_transformation,[],[f82]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_913,plain,
% 27.37/4.02      ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 27.37/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.37/4.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_1529,plain,
% 27.37/4.02      ( k10_relat_1(sK9,k1_setfam_1(k2_tarski(k2_relat_1(sK9),X0))) = k10_relat_1(sK9,X0) ),
% 27.37/4.02      inference(superposition,[status(thm)],[c_909,c_913]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_3761,plain,
% 27.37/4.02      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 27.37/4.02      | k10_relat_1(sK9,k1_xboole_0) = k10_relat_1(sK9,sK8) ),
% 27.37/4.02      inference(superposition,[status(thm)],[c_1227,c_1529]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_23,plain,
% 27.37/4.02      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 27.37/4.02      inference(cnf_transformation,[],[f68]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_912,plain,
% 27.37/4.02      ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 27.37/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.37/4.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_1187,plain,
% 27.37/4.02      ( k10_relat_1(sK9,k1_xboole_0) = k1_xboole_0 ),
% 27.37/4.02      inference(superposition,[status(thm)],[c_909,c_912]) ).
% 27.37/4.02  
% 27.37/4.02  cnf(c_3762,plain,
% 27.37/4.02      ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
% 27.37/4.02      inference(light_normalisation,[status(thm)],[c_3761,c_1187]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_4250,plain,
% 27.37/4.03      ( ~ r2_hidden(X0,k10_relat_1(sK9,sK8)) | X1 != X0 ),
% 27.37/4.03      inference(global_propositional_subsumption,
% 27.37/4.03                [status(thm)],
% 27.37/4.03                [c_3960,c_24,c_10,c_332,c_1300,c_3112,c_3762]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_5,plain,
% 27.37/4.03      ( r2_hidden(X0,X1)
% 27.37/4.03      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 27.37/4.03      inference(cnf_transformation,[],[f85]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_9,plain,
% 27.37/4.03      ( r1_xboole_0(X0,X1)
% 27.37/4.03      | r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ),
% 27.37/4.03      inference(cnf_transformation,[],[f81]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_1392,plain,
% 27.37/4.03      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 27.37/4.03      inference(resolution,[status(thm)],[c_5,c_9]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_4284,plain,
% 27.37/4.03      ( r1_xboole_0(k10_relat_1(sK9,sK8),X0)
% 27.37/4.03      | X1 != sK1(k10_relat_1(sK9,sK8),X0) ),
% 27.37/4.03      inference(resolution,[status(thm)],[c_4250,c_1392]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_4551,plain,
% 27.37/4.03      ( r1_xboole_0(k10_relat_1(sK9,sK8),X0) ),
% 27.37/4.03      inference(resolution,[status(thm)],[c_4284,c_313]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_4553,plain,
% 27.37/4.03      ( r1_xboole_0(k10_relat_1(sK9,sK8),k1_xboole_0) ),
% 27.37/4.03      inference(instantiation,[status(thm)],[c_4551]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_1520,plain,
% 27.37/4.03      ( r2_hidden(sK1(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
% 27.37/4.03      | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8))) ),
% 27.37/4.03      inference(instantiation,[status(thm)],[c_5]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_4,plain,
% 27.37/4.03      ( r2_hidden(X0,X1)
% 27.37/4.03      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 27.37/4.03      inference(cnf_transformation,[],[f84]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_1517,plain,
% 27.37/4.03      ( ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8)))
% 27.37/4.03      | r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8) ),
% 27.37/4.03      inference(instantiation,[status(thm)],[c_4]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(c_1176,plain,
% 27.37/4.03      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 27.37/4.03      | r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8))) ),
% 27.37/4.03      inference(instantiation,[status(thm)],[c_9]) ).
% 27.37/4.03  
% 27.37/4.03  cnf(contradiction,plain,
% 27.37/4.03      ( $false ),
% 27.37/4.03      inference(minisat,
% 27.37/4.03                [status(thm)],
% 27.37/4.03                [c_122132,c_99911,c_99913,c_27555,c_12640,c_4583,c_4553,
% 27.37/4.03                 c_3762,c_3626,c_1520,c_1517,c_1176,c_24,c_26]) ).
% 27.37/4.03  
% 27.37/4.03  
% 27.37/4.03  % SZS output end CNFRefutation for theBenchmark.p
% 27.37/4.03  
% 27.37/4.03  ------                               Statistics
% 27.37/4.03  
% 27.37/4.03  ------ Selected
% 27.37/4.03  
% 27.37/4.03  total_time:                             3.055
% 27.37/4.03  
%------------------------------------------------------------------------------
