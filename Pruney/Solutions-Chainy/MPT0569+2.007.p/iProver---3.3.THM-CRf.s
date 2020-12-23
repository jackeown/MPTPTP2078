%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:28 EST 2020

% Result     : Theorem 11.98s
% Output     : CNFRefutation 11.98s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 176 expanded)
%              Number of clauses        :   46 (  49 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  427 ( 742 expanded)
%              Number of equality atoms :  101 ( 184 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f28])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

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
    inference(flattening,[],[f22])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).

fof(f62,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f37,f40,f39,f38])).

fof(f66,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f59])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

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
   => ( ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
        | k1_xboole_0 != k10_relat_1(sK9,sK8) )
      & ( r1_xboole_0(k2_relat_1(sK9),sK8)
        | k1_xboole_0 = k10_relat_1(sK9,sK8) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
      | k1_xboole_0 != k10_relat_1(sK9,sK8) )
    & ( r1_xboole_0(k2_relat_1(sK9),sK8)
      | k1_xboole_0 = k10_relat_1(sK9,sK8) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f43,f44])).

fof(f73,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f72,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f70,f59])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f74,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_30416,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_30418,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_30416])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_30381,plain,
    ( ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X1)
    | r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_30383,plain,
    ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_30381])).

cnf(c_326,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_30343,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | X0 != sK7(sK9,sK1(k2_relat_1(sK9),sK8))
    | X1 != k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_30355,plain,
    ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | X0 != k10_relat_1(sK9,sK8)
    | sK7(sK9,sK1(k2_relat_1(sK9),sK8)) != sK7(sK9,sK1(k2_relat_1(sK9),sK8)) ),
    inference(instantiation,[status(thm)],[c_30343])).

cnf(c_30356,plain,
    ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | X0 != k10_relat_1(sK9,sK8) ),
    inference(equality_resolution_simp,[status(thm)],[c_30355])).

cnf(c_30358,plain,
    ( ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_xboole_0)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_30356])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_11856,plain,
    ( r2_hidden(X0,k10_relat_1(X1,sK8))
    | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK9),sK8)),X1)
    | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_12065,plain,
    ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | ~ r2_hidden(k4_tarski(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),sK1(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_11856])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_11910,plain,
    ( r2_hidden(k4_tarski(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),sK1(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_11846,plain,
    ( r2_hidden(sK1(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
    | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_11843,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8)))
    | r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_11825,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_26,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7796,plain,
    ( k1_xboole_0 = k10_relat_1(sK9,sK8)
    | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7804,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8370,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7796,c_7804])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7795,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7799,plain,
    ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9012,plain,
    ( k10_relat_1(sK9,k1_setfam_1(k2_tarski(k2_relat_1(sK9),X0))) = k10_relat_1(sK9,X0) ),
    inference(superposition,[status(thm)],[c_7795,c_7799])).

cnf(c_9154,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | k10_relat_1(sK9,k1_xboole_0) = k10_relat_1(sK9,sK8) ),
    inference(superposition,[status(thm)],[c_8370,c_9012])).

cnf(c_24,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_7798,plain,
    ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8180,plain,
    ( k10_relat_1(sK9,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7795,c_7798])).

cnf(c_9155,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9154,c_8180])).

cnf(c_323,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2527,plain,
    ( k10_relat_1(sK9,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_2528,plain,
    ( k10_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK9,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_322,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_341,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_65,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_25,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30418,c_30383,c_30358,c_12065,c_11910,c_11846,c_11843,c_11825,c_9155,c_2528,c_341,c_65,c_25,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:18:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.98/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.98/1.98  
% 11.98/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.98/1.98  
% 11.98/1.98  ------  iProver source info
% 11.98/1.98  
% 11.98/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.98/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.98/1.98  git: non_committed_changes: false
% 11.98/1.98  git: last_make_outside_of_git: false
% 11.98/1.98  
% 11.98/1.98  ------ 
% 11.98/1.98  ------ Parsing...
% 11.98/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  ------ Proving...
% 11.98/1.98  ------ Problem Properties 
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  clauses                                 28
% 11.98/1.98  conjectures                             3
% 11.98/1.98  EPR                                     3
% 11.98/1.98  Horn                                    21
% 11.98/1.98  unary                                   2
% 11.98/1.98  binary                                  14
% 11.98/1.98  lits                                    72
% 11.98/1.98  lits eq                                 14
% 11.98/1.98  fd_pure                                 0
% 11.98/1.98  fd_pseudo                               0
% 11.98/1.98  fd_cond                                 0
% 11.98/1.98  fd_pseudo_cond                          8
% 11.98/1.98  AC symbols                              0
% 11.98/1.98  
% 11.98/1.98  ------ Input Options Time Limit: Unbounded
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.98/1.98  Current options:
% 11.98/1.98  ------ 
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.98/1.98  
% 11.98/1.98  ------ Proving...
% 11.98/1.98  
% 11.98/1.98  
% 11.98/1.98  % SZS status Theorem for theBenchmark.p
% 11.98/1.98  
% 11.98/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.98/1.98  
% 11.98/1.98  fof(f4,axiom,(
% 11.98/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.98/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/1.98  
% 11.98/1.98  fof(f14,plain,(
% 11.98/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.98/1.98    inference(rectify,[],[f4])).
% 11.98/1.98  
% 11.98/1.98  fof(f16,plain,(
% 11.98/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.98/1.98    inference(ennf_transformation,[],[f14])).
% 11.98/1.98  
% 11.98/1.98  fof(f28,plain,(
% 11.98/1.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 11.98/1.98    introduced(choice_axiom,[])).
% 11.98/1.98  
% 11.98/1.98  fof(f29,plain,(
% 11.98/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.98/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f28])).
% 11.98/1.98  
% 11.98/1.98  fof(f56,plain,(
% 11.98/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 11.98/1.98    inference(cnf_transformation,[],[f29])).
% 11.98/1.98  
% 11.98/1.98  fof(f7,axiom,(
% 11.98/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.98/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/1.98  
% 11.98/1.98  fof(f59,plain,(
% 11.98/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.98/1.98    inference(cnf_transformation,[],[f7])).
% 11.98/1.98  
% 11.98/1.98  fof(f83,plain,(
% 11.98/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 11.98/1.98    inference(definition_unfolding,[],[f56,f59])).
% 11.98/1.98  
% 11.98/1.98  fof(f1,axiom,(
% 11.98/1.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.98/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/1.98  
% 11.98/1.98  fof(f22,plain,(
% 11.98/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.98/1.98    inference(nnf_transformation,[],[f1])).
% 11.98/1.98  
% 11.98/1.98  fof(f23,plain,(
% 11.98/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.98/1.98    inference(flattening,[],[f22])).
% 11.98/1.98  
% 11.98/1.98  fof(f24,plain,(
% 11.98/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.98/1.98    inference(rectify,[],[f23])).
% 11.98/1.98  
% 11.98/1.98  fof(f25,plain,(
% 11.98/1.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.98/1.98    introduced(choice_axiom,[])).
% 11.98/1.98  
% 11.98/1.98  fof(f26,plain,(
% 11.98/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.98/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 11.98/1.98  
% 11.98/1.98  fof(f48,plain,(
% 11.98/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 11.98/1.98    inference(cnf_transformation,[],[f26])).
% 11.98/1.98  
% 11.98/1.98  fof(f78,plain,(
% 11.98/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 11.98/1.98    inference(definition_unfolding,[],[f48,f59])).
% 11.98/1.98  
% 11.98/1.98  fof(f86,plain,(
% 11.98/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 11.98/1.98    inference(equality_resolution,[],[f78])).
% 11.98/1.98  
% 11.98/1.98  fof(f8,axiom,(
% 11.98/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 11.98/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/1.98  
% 11.98/1.98  fof(f18,plain,(
% 11.98/1.98    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 11.98/1.98    inference(ennf_transformation,[],[f8])).
% 11.98/1.98  
% 11.98/1.98  fof(f30,plain,(
% 11.98/1.98    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.98/1.98    inference(nnf_transformation,[],[f18])).
% 11.98/1.98  
% 11.98/1.98  fof(f31,plain,(
% 11.98/1.98    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.98/1.98    inference(rectify,[],[f30])).
% 11.98/1.98  
% 11.98/1.98  fof(f34,plain,(
% 11.98/1.98    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)))),
% 11.98/1.98    introduced(choice_axiom,[])).
% 11.98/1.98  
% 11.98/1.98  fof(f33,plain,(
% 11.98/1.98    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0)))) )),
% 11.98/1.98    introduced(choice_axiom,[])).
% 11.98/1.98  
% 11.98/1.98  fof(f32,plain,(
% 11.98/1.98    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 11.98/1.98    introduced(choice_axiom,[])).
% 11.98/1.98  
% 11.98/1.98  fof(f35,plain,(
% 11.98/1.98    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.98/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).
% 11.98/1.98  
% 11.98/1.98  fof(f62,plain,(
% 11.98/1.98    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 11.98/1.98    inference(cnf_transformation,[],[f35])).
% 11.98/1.98  
% 11.98/1.98  fof(f89,plain,(
% 11.98/1.98    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 11.98/1.98    inference(equality_resolution,[],[f62])).
% 11.98/1.98  
% 11.98/1.98  fof(f9,axiom,(
% 11.98/1.98    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 11.98/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/1.98  
% 11.98/1.98  fof(f36,plain,(
% 11.98/1.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 11.98/1.98    inference(nnf_transformation,[],[f9])).
% 11.98/1.98  
% 11.98/1.98  fof(f37,plain,(
% 11.98/1.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 11.98/1.98    inference(rectify,[],[f36])).
% 11.98/1.98  
% 11.98/1.98  fof(f40,plain,(
% 11.98/1.98    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 11.98/1.98    introduced(choice_axiom,[])).
% 11.98/1.98  
% 11.98/1.98  fof(f39,plain,(
% 11.98/1.98    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0))) )),
% 11.98/1.98    introduced(choice_axiom,[])).
% 11.98/1.98  
% 11.98/1.98  fof(f38,plain,(
% 11.98/1.98    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 11.98/1.98    introduced(choice_axiom,[])).
% 11.98/1.98  
% 11.98/1.98  fof(f41,plain,(
% 11.98/1.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 11.98/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f37,f40,f39,f38])).
% 11.98/1.98  
% 11.98/1.98  fof(f66,plain,(
% 11.98/1.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 11.98/1.98    inference(cnf_transformation,[],[f41])).
% 11.98/1.98  
% 11.98/1.98  fof(f93,plain,(
% 11.98/1.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 11.98/1.98    inference(equality_resolution,[],[f66])).
% 11.98/1.98  
% 11.98/1.98  fof(f46,plain,(
% 11.98/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.98/1.98    inference(cnf_transformation,[],[f26])).
% 11.98/1.98  
% 11.98/1.98  fof(f80,plain,(
% 11.98/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 11.98/1.98    inference(definition_unfolding,[],[f46,f59])).
% 11.98/1.98  
% 11.98/1.98  fof(f88,plain,(
% 11.98/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 11.98/1.98    inference(equality_resolution,[],[f80])).
% 11.98/1.98  
% 11.98/1.98  fof(f47,plain,(
% 11.98/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.98/1.98    inference(cnf_transformation,[],[f26])).
% 11.98/1.98  
% 11.98/1.98  fof(f79,plain,(
% 11.98/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 11.98/1.98    inference(definition_unfolding,[],[f47,f59])).
% 11.98/1.98  
% 11.98/1.98  fof(f87,plain,(
% 11.98/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 11.98/1.98    inference(equality_resolution,[],[f79])).
% 11.98/1.98  
% 11.98/1.98  fof(f55,plain,(
% 11.98/1.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 11.98/1.98    inference(cnf_transformation,[],[f29])).
% 11.98/1.98  
% 11.98/1.98  fof(f84,plain,(
% 11.98/1.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 11.98/1.98    inference(definition_unfolding,[],[f55,f59])).
% 11.98/1.98  
% 11.98/1.98  fof(f12,conjecture,(
% 11.98/1.98    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 11.98/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/1.98  
% 11.98/1.98  fof(f13,negated_conjecture,(
% 11.98/1.98    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 11.98/1.98    inference(negated_conjecture,[],[f12])).
% 11.98/1.98  
% 11.98/1.98  fof(f21,plain,(
% 11.98/1.98    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 11.98/1.98    inference(ennf_transformation,[],[f13])).
% 11.98/1.98  
% 11.98/1.98  fof(f42,plain,(
% 11.98/1.98    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 11.98/1.98    inference(nnf_transformation,[],[f21])).
% 11.98/1.98  
% 11.98/1.98  fof(f43,plain,(
% 11.98/1.98    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 11.98/1.98    inference(flattening,[],[f42])).
% 11.98/1.98  
% 11.98/1.98  fof(f44,plain,(
% 11.98/1.98    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)) & (r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)) & v1_relat_1(sK9))),
% 11.98/1.98    introduced(choice_axiom,[])).
% 11.98/1.98  
% 11.98/1.98  fof(f45,plain,(
% 11.98/1.98    (~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)) & (r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)) & v1_relat_1(sK9)),
% 11.98/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f43,f44])).
% 11.98/1.98  
% 11.98/1.98  fof(f73,plain,(
% 11.98/1.98    r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)),
% 11.98/1.98    inference(cnf_transformation,[],[f45])).
% 11.98/1.98  
% 11.98/1.98  fof(f2,axiom,(
% 11.98/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.98/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/1.98  
% 11.98/1.98  fof(f27,plain,(
% 11.98/1.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.98/1.98    inference(nnf_transformation,[],[f2])).
% 11.98/1.98  
% 11.98/1.98  fof(f52,plain,(
% 11.98/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.98/1.98    inference(cnf_transformation,[],[f27])).
% 11.98/1.98  
% 11.98/1.98  fof(f82,plain,(
% 11.98/1.98    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.98/1.98    inference(definition_unfolding,[],[f52,f59])).
% 11.98/1.98  
% 11.98/1.98  fof(f72,plain,(
% 11.98/1.98    v1_relat_1(sK9)),
% 11.98/1.98    inference(cnf_transformation,[],[f45])).
% 11.98/1.98  
% 11.98/1.98  fof(f10,axiom,(
% 11.98/1.98    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 11.98/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/1.98  
% 11.98/1.98  fof(f19,plain,(
% 11.98/1.98    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.98/1.98    inference(ennf_transformation,[],[f10])).
% 11.98/1.98  
% 11.98/1.98  fof(f70,plain,(
% 11.98/1.98    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 11.98/1.98    inference(cnf_transformation,[],[f19])).
% 11.98/1.98  
% 11.98/1.98  fof(f85,plain,(
% 11.98/1.98    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 11.98/1.98    inference(definition_unfolding,[],[f70,f59])).
% 11.98/1.98  
% 11.98/1.98  fof(f11,axiom,(
% 11.98/1.98    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 11.98/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/1.98  
% 11.98/1.98  fof(f20,plain,(
% 11.98/1.98    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 11.98/1.98    inference(ennf_transformation,[],[f11])).
% 11.98/1.98  
% 11.98/1.98  fof(f71,plain,(
% 11.98/1.98    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 11.98/1.98    inference(cnf_transformation,[],[f20])).
% 11.98/1.98  
% 11.98/1.98  fof(f5,axiom,(
% 11.98/1.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 11.98/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/1.98  
% 11.98/1.98  fof(f57,plain,(
% 11.98/1.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 11.98/1.98    inference(cnf_transformation,[],[f5])).
% 11.98/1.98  
% 11.98/1.98  fof(f74,plain,(
% 11.98/1.98    ~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)),
% 11.98/1.98    inference(cnf_transformation,[],[f45])).
% 11.98/1.98  
% 11.98/1.98  cnf(c_9,plain,
% 11.98/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.98/1.98      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ),
% 11.98/1.98      inference(cnf_transformation,[],[f83]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_30416,plain,
% 11.98/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.98/1.98      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(X0,X1))) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_9]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_30418,plain,
% 11.98/1.98      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 11.98/1.98      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_30416]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_3,plain,
% 11.98/1.98      ( ~ r2_hidden(X0,X1)
% 11.98/1.98      | ~ r2_hidden(X0,X2)
% 11.98/1.98      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 11.98/1.98      inference(cnf_transformation,[],[f86]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_30381,plain,
% 11.98/1.98      ( ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X0)
% 11.98/1.98      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X1)
% 11.98/1.98      | r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(X1,X0))) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_3]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_30383,plain,
% 11.98/1.98      ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)))
% 11.98/1.98      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_xboole_0) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_30381]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_326,plain,
% 11.98/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.98/1.98      theory(equality) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_30343,plain,
% 11.98/1.98      ( r2_hidden(X0,X1)
% 11.98/1.98      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 11.98/1.98      | X0 != sK7(sK9,sK1(k2_relat_1(sK9),sK8))
% 11.98/1.98      | X1 != k10_relat_1(sK9,sK8) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_326]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_30355,plain,
% 11.98/1.98      ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X0)
% 11.98/1.98      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 11.98/1.98      | X0 != k10_relat_1(sK9,sK8)
% 11.98/1.98      | sK7(sK9,sK1(k2_relat_1(sK9),sK8)) != sK7(sK9,sK1(k2_relat_1(sK9),sK8)) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_30343]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_30356,plain,
% 11.98/1.98      ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),X0)
% 11.98/1.98      | ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 11.98/1.98      | X0 != k10_relat_1(sK9,sK8) ),
% 11.98/1.98      inference(equality_resolution_simp,[status(thm)],[c_30355]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_30358,plain,
% 11.98/1.98      ( ~ r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 11.98/1.98      | r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k1_xboole_0)
% 11.98/1.98      | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_30356]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_16,plain,
% 11.98/1.98      ( ~ r2_hidden(X0,X1)
% 11.98/1.98      | r2_hidden(X2,k10_relat_1(X3,X1))
% 11.98/1.98      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 11.98/1.98      | ~ v1_relat_1(X3) ),
% 11.98/1.98      inference(cnf_transformation,[],[f89]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_11856,plain,
% 11.98/1.98      ( r2_hidden(X0,k10_relat_1(X1,sK8))
% 11.98/1.98      | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK9),sK8)),X1)
% 11.98/1.98      | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8)
% 11.98/1.98      | ~ v1_relat_1(X1) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_16]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_12065,plain,
% 11.98/1.98      ( r2_hidden(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 11.98/1.98      | ~ r2_hidden(k4_tarski(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),sK1(k2_relat_1(sK9),sK8)),sK9)
% 11.98/1.98      | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8)
% 11.98/1.98      | ~ v1_relat_1(sK9) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_11856]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_22,plain,
% 11.98/1.98      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.98/1.98      | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
% 11.98/1.98      inference(cnf_transformation,[],[f93]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_11910,plain,
% 11.98/1.98      ( r2_hidden(k4_tarski(sK7(sK9,sK1(k2_relat_1(sK9),sK8)),sK1(k2_relat_1(sK9),sK8)),sK9)
% 11.98/1.98      | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_22]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_5,plain,
% 11.98/1.98      ( r2_hidden(X0,X1)
% 11.98/1.98      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 11.98/1.98      inference(cnf_transformation,[],[f88]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_11846,plain,
% 11.98/1.98      ( r2_hidden(sK1(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
% 11.98/1.98      | ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8))) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_5]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_4,plain,
% 11.98/1.98      ( r2_hidden(X0,X1)
% 11.98/1.98      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 11.98/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_11843,plain,
% 11.98/1.98      ( ~ r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8)))
% 11.98/1.98      | r2_hidden(sK1(k2_relat_1(sK9),sK8),sK8) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_4]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_10,plain,
% 11.98/1.98      ( r1_xboole_0(X0,X1)
% 11.98/1.98      | r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ),
% 11.98/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_11825,plain,
% 11.98/1.98      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 11.98/1.98      | r2_hidden(sK1(k2_relat_1(sK9),sK8),k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8))) ),
% 11.98/1.98      inference(instantiation,[status(thm)],[c_10]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_26,negated_conjecture,
% 11.98/1.98      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 11.98/1.98      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 11.98/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_7796,plain,
% 11.98/1.98      ( k1_xboole_0 = k10_relat_1(sK9,sK8)
% 11.98/1.98      | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
% 11.98/1.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.98/1.98  
% 11.98/1.98  cnf(c_7,plain,
% 11.98/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.98/1.98      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 11.98/1.98      inference(cnf_transformation,[],[f82]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_7804,plain,
% 11.98/1.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 11.98/1.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 11.98/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_8370,plain,
% 11.98/1.99      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 11.98/1.99      | k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8)) = k1_xboole_0 ),
% 11.98/1.99      inference(superposition,[status(thm)],[c_7796,c_7804]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_27,negated_conjecture,
% 11.98/1.99      ( v1_relat_1(sK9) ),
% 11.98/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_7795,plain,
% 11.98/1.99      ( v1_relat_1(sK9) = iProver_top ),
% 11.98/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_23,plain,
% 11.98/1.99      ( ~ v1_relat_1(X0)
% 11.98/1.99      | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 11.98/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_7799,plain,
% 11.98/1.99      ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 11.98/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.98/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_9012,plain,
% 11.98/1.99      ( k10_relat_1(sK9,k1_setfam_1(k2_tarski(k2_relat_1(sK9),X0))) = k10_relat_1(sK9,X0) ),
% 11.98/1.99      inference(superposition,[status(thm)],[c_7795,c_7799]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_9154,plain,
% 11.98/1.99      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 11.98/1.99      | k10_relat_1(sK9,k1_xboole_0) = k10_relat_1(sK9,sK8) ),
% 11.98/1.99      inference(superposition,[status(thm)],[c_8370,c_9012]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_24,plain,
% 11.98/1.99      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.98/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_7798,plain,
% 11.98/1.99      ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 11.98/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.98/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_8180,plain,
% 11.98/1.99      ( k10_relat_1(sK9,k1_xboole_0) = k1_xboole_0 ),
% 11.98/1.99      inference(superposition,[status(thm)],[c_7795,c_7798]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_9155,plain,
% 11.98/1.99      ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
% 11.98/1.99      inference(light_normalisation,[status(thm)],[c_9154,c_8180]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_323,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_2527,plain,
% 11.98/1.99      ( k10_relat_1(sK9,sK8) != X0
% 11.98/1.99      | k1_xboole_0 != X0
% 11.98/1.99      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 11.98/1.99      inference(instantiation,[status(thm)],[c_323]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_2528,plain,
% 11.98/1.99      ( k10_relat_1(sK9,sK8) != k1_xboole_0
% 11.98/1.99      | k1_xboole_0 = k10_relat_1(sK9,sK8)
% 11.98/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.98/1.99      inference(instantiation,[status(thm)],[c_2527]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_322,plain,( X0 = X0 ),theory(equality) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_341,plain,
% 11.98/1.99      ( k1_xboole_0 = k1_xboole_0 ),
% 11.98/1.99      inference(instantiation,[status(thm)],[c_322]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_11,plain,
% 11.98/1.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.98/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_65,plain,
% 11.98/1.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.98/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(c_25,negated_conjecture,
% 11.98/1.99      ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
% 11.98/1.99      | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
% 11.98/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.98/1.99  
% 11.98/1.99  cnf(contradiction,plain,
% 11.98/1.99      ( $false ),
% 11.98/1.99      inference(minisat,
% 11.98/1.99                [status(thm)],
% 11.98/1.99                [c_30418,c_30383,c_30358,c_12065,c_11910,c_11846,c_11843,
% 11.98/1.99                 c_11825,c_9155,c_2528,c_341,c_65,c_25,c_27]) ).
% 11.98/1.99  
% 11.98/1.99  
% 11.98/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.98/1.99  
% 11.98/1.99  ------                               Statistics
% 11.98/1.99  
% 11.98/1.99  ------ Selected
% 11.98/1.99  
% 11.98/1.99  total_time:                             1.37
% 11.98/1.99  
%------------------------------------------------------------------------------
