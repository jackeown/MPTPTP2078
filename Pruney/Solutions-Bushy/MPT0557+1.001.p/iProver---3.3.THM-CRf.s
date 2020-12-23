%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0557+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:35 EST 2020

% Result     : Theorem 7.28s
% Output     : CNFRefutation 7.28s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 176 expanded)
%              Number of clauses        :   31 (  34 expanded)
%              Number of leaves         :   12 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  385 (1232 expanded)
%              Number of equality atoms :   42 ( 141 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f15,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15,f14,f13])).

fof(f28,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f26,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f27,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k9_relat_1(X2,k9_relat_1(X1,X0)) != k9_relat_1(k5_relat_1(X1,X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k9_relat_1(X2,k9_relat_1(X1,X0)) != k9_relat_1(k5_relat_1(X1,X2),X0)
          & v1_relat_1(X2) )
     => ( k9_relat_1(k5_relat_1(X1,sK9),X0) != k9_relat_1(sK9,k9_relat_1(X1,X0))
        & v1_relat_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k9_relat_1(X2,k9_relat_1(X1,X0)) != k9_relat_1(k5_relat_1(X1,X2),X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k9_relat_1(X2,k9_relat_1(sK8,sK7)) != k9_relat_1(k5_relat_1(sK8,X2),sK7)
          & v1_relat_1(X2) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k9_relat_1(k5_relat_1(sK8,sK9),sK7) != k9_relat_1(sK9,k9_relat_1(sK8,sK7))
    & v1_relat_1(sK9)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f10,f24,f23])).

fof(f41,plain,(
    k9_relat_1(k5_relat_1(sK8,sK9),sK7) != k9_relat_1(sK9,k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2839,plain,
    ( r2_hidden(X0,k9_relat_1(X1,k9_relat_1(sK8,sK7)))
    | ~ r2_hidden(sK6(sK8,sK9,sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k9_relat_1(sK8,sK7))
    | ~ r2_hidden(k4_tarski(sK6(sK8,sK9,sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_20333,plain,
    ( ~ r2_hidden(sK6(sK8,sK9,sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k9_relat_1(sK8,sK7))
    | r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),k9_relat_1(sK9,k9_relat_1(sK8,sK7)))
    | ~ r2_hidden(k4_tarski(sK6(sK8,sK9,sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),sK9)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_2839])).

cnf(c_928,plain,
    ( r2_hidden(X0,k9_relat_1(X1,sK7))
    | ~ r2_hidden(sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK7)
    | ~ r2_hidden(k4_tarski(sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2071,plain,
    ( r2_hidden(sK6(sK8,sK9,sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k9_relat_1(sK8,sK7))
    | ~ r2_hidden(sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK7)
    | ~ r2_hidden(k4_tarski(sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK6(sK8,sK9,sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_874,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),X1)
    | r2_hidden(k4_tarski(X0,sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k5_relat_1(X1,sK9))
    | ~ r2_hidden(k4_tarski(sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),sK9)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1979,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),sK9)
    | ~ r2_hidden(k4_tarski(sK2(sK8,sK7,sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),sK8)
    | r2_hidden(k4_tarski(sK2(sK8,sK7,sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(X0,sK0(X2,X1,X3)),X2)
    | ~ v1_relat_1(X2)
    | k9_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_611,plain,
    ( ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),k9_relat_1(sK9,k9_relat_1(sK8,sK7)))
    | ~ r2_hidden(k4_tarski(X0,sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | k9_relat_1(k5_relat_1(sK8,sK9),sK7) = k9_relat_1(sK9,k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1453,plain,
    ( ~ r2_hidden(sK2(sK8,sK7,sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),sK7)
    | ~ r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),k9_relat_1(sK9,k9_relat_1(sK8,sK7)))
    | ~ r2_hidden(k4_tarski(sK2(sK8,sK7,sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | k9_relat_1(k5_relat_1(sK8,sK9),sK7) = k9_relat_1(sK9,k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_956,plain,
    ( r2_hidden(k4_tarski(sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK6(sK8,sK9,sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),sK8)
    | ~ r2_hidden(k4_tarski(sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK6(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_957,plain,
    ( r2_hidden(k4_tarski(sK6(sK8,sK9,sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),sK9)
    | ~ r2_hidden(k4_tarski(sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_889,plain,
    ( ~ r2_hidden(sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k9_relat_1(sK8,sK7))
    | r2_hidden(k4_tarski(sK2(sK8,sK7,sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_890,plain,
    ( ~ r2_hidden(sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k9_relat_1(sK8,sK7))
    | r2_hidden(sK2(sK8,sK7,sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))))),sK7)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_726,plain,
    ( ~ r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),k9_relat_1(sK9,k9_relat_1(sK8,sK7)))
    | r2_hidden(k4_tarski(sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),sK9)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_727,plain,
    ( r2_hidden(sK2(sK9,k9_relat_1(sK8,sK7),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k9_relat_1(sK8,sK7))
    | ~ r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),k9_relat_1(sK9,k9_relat_1(sK8,sK7)))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_643,plain,
    ( v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_616,plain,
    ( r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),k9_relat_1(sK9,k9_relat_1(sK8,sK7)))
    | r2_hidden(k4_tarski(sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7)))),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | k9_relat_1(k5_relat_1(sK8,sK9),sK7) = k9_relat_1(sK9,k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_608,plain,
    ( r2_hidden(sK1(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),sK7)
    | r2_hidden(sK0(k5_relat_1(sK8,sK9),sK7,k9_relat_1(sK9,k9_relat_1(sK8,sK7))),k9_relat_1(sK9,k9_relat_1(sK8,sK7)))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | k9_relat_1(k5_relat_1(sK8,sK9),sK7) = k9_relat_1(sK9,k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_13,negated_conjecture,
    ( k9_relat_1(k5_relat_1(sK8,sK9),sK7) != k9_relat_1(sK9,k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20333,c_2071,c_1979,c_1453,c_956,c_957,c_889,c_890,c_726,c_727,c_643,c_616,c_608,c_13,c_14,c_15])).


%------------------------------------------------------------------------------
