%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0577+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:39 EST 2020

% Result     : Theorem 11.85s
% Output     : CNFRefutation 11.85s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 198 expanded)
%              Number of clauses        :   45 (  49 expanded)
%              Number of leaves         :   12 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  432 (1303 expanded)
%              Number of equality atoms :   93 ( 202 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    8 (   2 average)

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

fof(f6,plain,(
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

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f15,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15,f14,f13])).

fof(f28,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f18,f21,f20,f19])).

fof(f34,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f26,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f27,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) != k10_relat_1(k5_relat_1(X1,X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) != k10_relat_1(k5_relat_1(X1,X2),X0)
          & v1_relat_1(X2) )
     => ( k10_relat_1(X1,k10_relat_1(sK9,X0)) != k10_relat_1(k5_relat_1(X1,sK9),X0)
        & v1_relat_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k10_relat_1(X1,k10_relat_1(X2,X0)) != k10_relat_1(k5_relat_1(X1,X2),X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k10_relat_1(k5_relat_1(sK8,X2),sK7) != k10_relat_1(sK8,k10_relat_1(X2,sK7))
          & v1_relat_1(X2) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k10_relat_1(k5_relat_1(sK8,sK9),sK7) != k10_relat_1(sK8,k10_relat_1(sK9,sK7))
    & v1_relat_1(sK9)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f10,f24,f23])).

fof(f41,plain,(
    k10_relat_1(k5_relat_1(sK8,sK9),sK7) != k10_relat_1(sK8,k10_relat_1(sK9,sK7)) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f33,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1074,plain,
    ( ~ r2_hidden(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),X0)
    | r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,X0))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_21859,plain,
    ( ~ r2_hidden(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,sK7))
    | r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7)))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_21860,plain,
    ( r2_hidden(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,sK7)) != iProver_top
    | r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7))) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21859])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(sK0(X2,X1,X3),X0),X2)
    | ~ v1_relat_1(X2)
    | k10_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_15686,plain,
    ( ~ r2_hidden(sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK7)
    | ~ r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7)))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))))),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | k10_relat_1(k5_relat_1(sK8,sK9),sK7) = k10_relat_1(sK8,k10_relat_1(sK9,sK7)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_15687,plain,
    ( k10_relat_1(k5_relat_1(sK8,sK9),sK7) = k10_relat_1(sK8,k10_relat_1(sK9,sK7))
    | r2_hidden(sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK7) != iProver_top
    | r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7))) != iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))))),k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15686])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1300,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),X0),X1)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),X0),k5_relat_1(sK8,X1))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK8)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(sK8,X1))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2916,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))))),sK9)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))))),k5_relat_1(sK8,sK9))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK8)
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_2917,plain,
    ( r2_hidden(k4_tarski(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))))),sK9) != iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))))),k5_relat_1(sK8,sK9)) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK8) != iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2916])).

cnf(c_1089,plain,
    ( r2_hidden(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,X0))
    | ~ r2_hidden(sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),X0)
    | ~ r2_hidden(k4_tarski(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK9)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1702,plain,
    ( r2_hidden(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,sK7))
    | ~ r2_hidden(sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK7)
    | ~ r2_hidden(k4_tarski(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK9)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_1703,plain,
    ( r2_hidden(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,sK7)) = iProver_top
    | r2_hidden(sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1702])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1310,plain,
    ( ~ r2_hidden(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,sK7))
    | r2_hidden(k4_tarski(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))))),sK9)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1314,plain,
    ( r2_hidden(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,sK7)) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))))),sK9) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1311,plain,
    ( r2_hidden(sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK7)
    | ~ r2_hidden(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,sK7))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1312,plain,
    ( r2_hidden(sK2(sK9,sK7,sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK7) = iProver_top
    | r2_hidden(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,sK7)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,negated_conjecture,
    ( k10_relat_1(k5_relat_1(sK8,sK9),sK7) != k10_relat_1(sK8,k10_relat_1(sK9,sK7)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_941,plain,
    ( r2_hidden(sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK7)
    | r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7)))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_1,c_13])).

cnf(c_942,plain,
    ( r2_hidden(sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK7) = iProver_top
    | r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7))) = iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_809,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK8)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_813,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK6(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_810,plain,
    ( r2_hidden(k4_tarski(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK9)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_811,plain,
    ( r2_hidden(k4_tarski(sK6(sK8,sK9,sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_689,plain,
    ( ~ r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7)))
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_693,plain,
    ( r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7))) != iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))))),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_690,plain,
    ( r2_hidden(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,sK7))
    | ~ r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7)))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_691,plain,
    ( r2_hidden(sK2(sK8,k10_relat_1(sK9,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k10_relat_1(sK9,sK7)) = iProver_top
    | r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7))) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_629,plain,
    ( v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_630,plain,
    ( v1_relat_1(k5_relat_1(sK8,sK9)) = iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_592,plain,
    ( r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7)))
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | k10_relat_1(k5_relat_1(sK8,sK9),sK7) = k10_relat_1(sK8,k10_relat_1(sK9,sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_593,plain,
    ( k10_relat_1(k5_relat_1(sK8,sK9),sK7) = k10_relat_1(sK8,k10_relat_1(sK9,sK7))
    | r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),k10_relat_1(sK8,k10_relat_1(sK9,sK7))) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7))),sK1(k5_relat_1(sK8,sK9),sK7,k10_relat_1(sK8,k10_relat_1(sK9,sK7)))),k5_relat_1(sK8,sK9)) = iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21860,c_15687,c_2917,c_1703,c_1314,c_1312,c_942,c_813,c_811,c_693,c_691,c_630,c_593,c_13,c_17,c_16])).


%------------------------------------------------------------------------------
