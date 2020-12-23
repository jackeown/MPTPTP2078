%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0685+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:54 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 171 expanded)
%              Number of clauses        :   50 (  50 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  509 (1128 expanded)
%              Number of equality atoms :  100 ( 174 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
            & r2_hidden(sK0(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK0(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                    & r2_hidden(sK0(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f36,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f2,axiom,(
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

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f42,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f4])).

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
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f49,plain,(
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
    inference(equality_resolution,[],[f49])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(k7_relat_1(sK8,sK6),sK7) != k3_xboole_0(sK6,k10_relat_1(sK8,sK7))
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k10_relat_1(k7_relat_1(sK8,sK6),sK7) != k3_xboole_0(sK6,k10_relat_1(sK8,sK7))
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f15,f32])).

fof(f56,plain,(
    k10_relat_1(k7_relat_1(sK8,sK6),sK7) != k3_xboole_0(sK6,k10_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1163,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK6)
    | ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),X0),X1)
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),X0),k7_relat_1(X1,sK6))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k7_relat_1(X1,sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_20417,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK6)
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))))),k7_relat_1(sK8,sK6))
    | ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))))),sK8)
    | ~ v1_relat_1(k7_relat_1(sK8,sK6))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_20419,plain,
    ( r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))))),k7_relat_1(sK8,sK6)) = iProver_top
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))))),sK8) != iProver_top
    | v1_relat_1(k7_relat_1(sK8,sK6)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20417])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_969,plain,
    ( r2_hidden(X0,k10_relat_1(X1,sK7))
    | ~ r2_hidden(sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK7)
    | ~ r2_hidden(k4_tarski(X0,sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),X1)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3927,plain,
    ( ~ r2_hidden(sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK7)
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_3928,plain,
    ( r2_hidden(sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK7) != iProver_top
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7)) = iProver_top
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3927])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1338,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),X0)
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(X0,k10_relat_1(sK8,sK7)))
    | ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3053,plain,
    ( r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))
    | ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK6) ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_3054,plain,
    ( r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7))) = iProver_top
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7)) != iProver_top
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3053])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(sK2(X2,X1,X3),X0),X2)
    | ~ v1_relat_1(X2)
    | k10_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_953,plain,
    ( ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))
    | ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),X0),k7_relat_1(sK8,sK6))
    | ~ v1_relat_1(k7_relat_1(sK8,sK6))
    | k10_relat_1(k7_relat_1(sK8,sK6),sK7) = k3_xboole_0(sK6,k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2425,plain,
    ( ~ r2_hidden(sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),sK7)
    | ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))
    | ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))))),k7_relat_1(sK8,sK6))
    | ~ v1_relat_1(k7_relat_1(sK8,sK6))
    | k10_relat_1(k7_relat_1(sK8,sK6),sK7) = k3_xboole_0(sK6,k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_2426,plain,
    ( k10_relat_1(k7_relat_1(sK8,sK6),sK7) = k3_xboole_0(sK6,k10_relat_1(sK8,sK7))
    | r2_hidden(sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),sK7) != iProver_top
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7))) != iProver_top
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))))),k7_relat_1(sK8,sK6)) != iProver_top
    | v1_relat_1(k7_relat_1(sK8,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2425])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK4(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1355,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7))
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))))),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1359,plain,
    ( r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7)) != iProver_top
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))))),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1355])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1356,plain,
    ( r2_hidden(sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),sK7)
    | ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1357,plain,
    ( r2_hidden(sK4(sK8,sK7,sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),sK7) = iProver_top
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1356])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_249,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ v1_relat_1(X3)
    | X3 != X2
    | k7_relat_1(X3,X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_250,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_1066,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),k7_relat_1(sK8,sK6))
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_1067,plain,
    ( r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),k7_relat_1(sK8,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1066])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1063,plain,
    ( r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK6)
    | ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),k7_relat_1(sK8,sK6))
    | ~ v1_relat_1(k7_relat_1(sK8,sK6))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1064,plain,
    ( r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK6) = iProver_top
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),k7_relat_1(sK8,sK6)) != iProver_top
    | v1_relat_1(k7_relat_1(sK8,sK6)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1035,plain,
    ( v1_relat_1(k7_relat_1(sK8,sK6))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1036,plain,
    ( v1_relat_1(k7_relat_1(sK8,sK6)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1011,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1012,plain,
    ( r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7))) != iProver_top
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1008,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1009,plain,
    ( r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7))) != iProver_top
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k10_relat_1(sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_958,plain,
    ( r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),k7_relat_1(sK8,sK6))
    | ~ v1_relat_1(k7_relat_1(sK8,sK6))
    | k10_relat_1(k7_relat_1(sK8,sK6),sK7) = k3_xboole_0(sK6,k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_959,plain,
    ( k10_relat_1(k7_relat_1(sK8,sK6),sK7) = k3_xboole_0(sK6,k10_relat_1(sK8,sK7))
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7))) = iProver_top
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))),k7_relat_1(sK8,sK6)) = iProver_top
    | v1_relat_1(k7_relat_1(sK8,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_7,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_950,plain,
    ( r2_hidden(sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK7)
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))
    | ~ v1_relat_1(k7_relat_1(sK8,sK6))
    | k10_relat_1(k7_relat_1(sK8,sK6),sK7) = k3_xboole_0(sK6,k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_951,plain,
    ( k10_relat_1(k7_relat_1(sK8,sK6),sK7) = k3_xboole_0(sK6,k10_relat_1(sK8,sK7))
    | r2_hidden(sK3(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),sK7) = iProver_top
    | r2_hidden(sK2(k7_relat_1(sK8,sK6),sK7,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7))) = iProver_top
    | v1_relat_1(k7_relat_1(sK8,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_21,negated_conjecture,
    ( k10_relat_1(k7_relat_1(sK8,sK6),sK7) != k3_xboole_0(sK6,k10_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20419,c_3928,c_3054,c_2426,c_1359,c_1357,c_1067,c_1064,c_1036,c_1012,c_1009,c_959,c_951,c_21,c_23])).


%------------------------------------------------------------------------------
