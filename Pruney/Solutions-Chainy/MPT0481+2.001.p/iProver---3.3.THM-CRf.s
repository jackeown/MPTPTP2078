%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:34 EST 2020

% Result     : Theorem 11.92s
% Output     : CNFRefutation 11.92s
% Verified   : 
% Statistics : Number of formulae       :  111 (1789 expanded)
%              Number of clauses        :   67 ( 649 expanded)
%              Number of leaves         :   12 ( 374 expanded)
%              Depth                    :   32
%              Number of atoms          :  471 (7977 expanded)
%              Number of equality atoms :  193 (1845 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f24,f27,f26,f25])).

fof(f41,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK0(X0,X1) != sK1(X0,X1)
          | ~ r2_hidden(sK0(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( ( sK0(X0,X1) = sK1(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK0(X0,X1) != sK1(X0,X1)
              | ~ r2_hidden(sK0(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( ( sK0(X0,X1) = sK1(X0,X1)
                & r2_hidden(sK0(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f32,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
        | ~ r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
      | ~ r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f13,f29])).

fof(f49,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
    | ~ r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_548,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_542,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_540,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_649,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_542,c_540])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | ~ v1_relat_1(k6_relat_1(X2))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_551,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) != iProver_top
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_539,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_573,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X0),k6_relat_1(X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_551,c_539])).

cnf(c_1584,plain,
    ( sK7(X0,k6_relat_1(X1),X2,X3) = X3
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_573])).

cnf(c_1651,plain,
    ( sK7(X0,k6_relat_1(X1),X2,X3) = X3
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1584,c_539])).

cnf(c_1657,plain,
    ( sK7(X0,k6_relat_1(X1),sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)) = sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)
    | r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_548,c_1651])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK7(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_541,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_639,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_541,c_540])).

cnf(c_1279,plain,
    ( sK7(k6_relat_1(X0),X1,X2,X3) = X2
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_573])).

cnf(c_21,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1464,plain,
    ( v1_relat_1(X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | sK7(k6_relat_1(X0),X1,X2,X3) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1279,c_21])).

cnf(c_1465,plain,
    ( sK7(k6_relat_1(X0),X1,X2,X3) = X2
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1464])).

cnf(c_1475,plain,
    ( sK7(k6_relat_1(X0),X1,sK2(k5_relat_1(k6_relat_1(X0),X1),X2),sK3(k5_relat_1(k6_relat_1(X0),X1),X2)) = sK2(k5_relat_1(k6_relat_1(X0),X1),X2)
    | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_548,c_1465])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
    | ~ r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_538,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) != iProver_top
    | r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_28480,plain,
    ( sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
    | r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_538])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_781,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9))
    | ~ v1_relat_1(k6_relat_1(sK8))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_782,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) = iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_831,plain,
    ( v1_relat_1(k6_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_832,plain,
    ( v1_relat_1(k6_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_29423,plain,
    ( sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
    | r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28480,c_19,c_782,c_832])).

cnf(c_29431,plain,
    ( sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
    | sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_29423])).

cnf(c_1188,plain,
    ( v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)))
    | ~ v1_relat_1(k6_relat_1(sK8))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_29454,plain,
    ( ~ v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)))
    | ~ v1_relat_1(sK9)
    | sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
    | sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_29431])).

cnf(c_29456,plain,
    ( sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
    | sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29431,c_19,c_832,c_1189])).

cnf(c_29460,plain,
    ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
    | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9) = iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_29456,c_649])).

cnf(c_29979,plain,
    ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
    | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29460,c_19,c_832])).

cnf(c_29986,plain,
    ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
    | r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9) = iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_548,c_29979])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_755,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_756,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_42100,plain,
    ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
    | r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29986,c_19,c_756,c_782,c_832])).

cnf(c_42107,plain,
    ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
    | r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_42100,c_538])).

cnf(c_42164,plain,
    ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_42107])).

cnf(c_1189,plain,
    ( v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) = iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1188])).

cnf(c_44653,plain,
    ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42164,c_19,c_832,c_1189])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_550,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_579,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_550,c_539])).

cnf(c_1582,plain,
    ( r2_hidden(sK7(X0,k6_relat_1(X1),X2,X3),X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_579])).

cnf(c_1847,plain,
    ( r2_hidden(sK7(X0,k6_relat_1(X1),X2,X3),X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1582,c_539])).

cnf(c_1853,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2) = iProver_top
    | r2_hidden(sK7(X0,k6_relat_1(X1),sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_548,c_1847])).

cnf(c_44660,plain,
    ( r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) = iProver_top
    | r2_hidden(sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK8) = iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_44653,c_1853])).

cnf(c_909,plain,
    ( r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),sK9)
    | ~ v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_910,plain,
    ( r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),sK9) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_909])).

cnf(c_44657,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),sK9) = iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_44653,c_639])).

cnf(c_44843,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44657,c_19,c_832])).

cnf(c_44849,plain,
    ( r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),sK9) = iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_548,c_44843])).

cnf(c_45258,plain,
    ( r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44660,c_19,c_832,c_910,c_1189,c_44849])).

cnf(c_45264,plain,
    ( sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9) ),
    inference(superposition,[status(thm)],[c_45258,c_29423])).

cnf(c_46139,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9) = iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_45264,c_649])).

cnf(c_763,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
    | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),k5_relat_1(k6_relat_1(sK8),sK9))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_764,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),k5_relat_1(k6_relat_1(sK8),sK9)) = iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_20,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) != iProver_top
    | r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46139,c_45258,c_832,c_782,c_764,c_756,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:36:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.92/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.92/1.99  
% 11.92/1.99  ------  iProver source info
% 11.92/1.99  
% 11.92/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.92/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.92/1.99  git: non_committed_changes: false
% 11.92/1.99  git: last_make_outside_of_git: false
% 11.92/1.99  
% 11.92/1.99  ------ 
% 11.92/1.99  
% 11.92/1.99  ------ Input Options
% 11.92/1.99  
% 11.92/1.99  --out_options                           all
% 11.92/1.99  --tptp_safe_out                         true
% 11.92/1.99  --problem_path                          ""
% 11.92/1.99  --include_path                          ""
% 11.92/1.99  --clausifier                            res/vclausify_rel
% 11.92/1.99  --clausifier_options                    --mode clausify
% 11.92/1.99  --stdin                                 false
% 11.92/1.99  --stats_out                             all
% 11.92/1.99  
% 11.92/1.99  ------ General Options
% 11.92/1.99  
% 11.92/1.99  --fof                                   false
% 11.92/1.99  --time_out_real                         305.
% 11.92/1.99  --time_out_virtual                      -1.
% 11.92/1.99  --symbol_type_check                     false
% 11.92/1.99  --clausify_out                          false
% 11.92/1.99  --sig_cnt_out                           false
% 11.92/1.99  --trig_cnt_out                          false
% 11.92/1.99  --trig_cnt_out_tolerance                1.
% 11.92/1.99  --trig_cnt_out_sk_spl                   false
% 11.92/1.99  --abstr_cl_out                          false
% 11.92/1.99  
% 11.92/1.99  ------ Global Options
% 11.92/1.99  
% 11.92/1.99  --schedule                              default
% 11.92/1.99  --add_important_lit                     false
% 11.92/1.99  --prop_solver_per_cl                    1000
% 11.92/1.99  --min_unsat_core                        false
% 11.92/1.99  --soft_assumptions                      false
% 11.92/1.99  --soft_lemma_size                       3
% 11.92/1.99  --prop_impl_unit_size                   0
% 11.92/1.99  --prop_impl_unit                        []
% 11.92/1.99  --share_sel_clauses                     true
% 11.92/1.99  --reset_solvers                         false
% 11.92/1.99  --bc_imp_inh                            [conj_cone]
% 11.92/1.99  --conj_cone_tolerance                   3.
% 11.92/1.99  --extra_neg_conj                        none
% 11.92/1.99  --large_theory_mode                     true
% 11.92/1.99  --prolific_symb_bound                   200
% 11.92/1.99  --lt_threshold                          2000
% 11.92/1.99  --clause_weak_htbl                      true
% 11.92/1.99  --gc_record_bc_elim                     false
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing Options
% 11.92/1.99  
% 11.92/1.99  --preprocessing_flag                    true
% 11.92/1.99  --time_out_prep_mult                    0.1
% 11.92/1.99  --splitting_mode                        input
% 11.92/1.99  --splitting_grd                         true
% 11.92/1.99  --splitting_cvd                         false
% 11.92/1.99  --splitting_cvd_svl                     false
% 11.92/1.99  --splitting_nvd                         32
% 11.92/1.99  --sub_typing                            true
% 11.92/1.99  --prep_gs_sim                           true
% 11.92/1.99  --prep_unflatten                        true
% 11.92/1.99  --prep_res_sim                          true
% 11.92/1.99  --prep_upred                            true
% 11.92/1.99  --prep_sem_filter                       exhaustive
% 11.92/1.99  --prep_sem_filter_out                   false
% 11.92/1.99  --pred_elim                             true
% 11.92/1.99  --res_sim_input                         true
% 11.92/1.99  --eq_ax_congr_red                       true
% 11.92/1.99  --pure_diseq_elim                       true
% 11.92/1.99  --brand_transform                       false
% 11.92/1.99  --non_eq_to_eq                          false
% 11.92/1.99  --prep_def_merge                        true
% 11.92/1.99  --prep_def_merge_prop_impl              false
% 11.92/1.99  --prep_def_merge_mbd                    true
% 11.92/1.99  --prep_def_merge_tr_red                 false
% 11.92/1.99  --prep_def_merge_tr_cl                  false
% 11.92/1.99  --smt_preprocessing                     true
% 11.92/1.99  --smt_ac_axioms                         fast
% 11.92/1.99  --preprocessed_out                      false
% 11.92/1.99  --preprocessed_stats                    false
% 11.92/1.99  
% 11.92/1.99  ------ Abstraction refinement Options
% 11.92/1.99  
% 11.92/1.99  --abstr_ref                             []
% 11.92/1.99  --abstr_ref_prep                        false
% 11.92/1.99  --abstr_ref_until_sat                   false
% 11.92/1.99  --abstr_ref_sig_restrict                funpre
% 11.92/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.92/1.99  --abstr_ref_under                       []
% 11.92/1.99  
% 11.92/1.99  ------ SAT Options
% 11.92/1.99  
% 11.92/1.99  --sat_mode                              false
% 11.92/1.99  --sat_fm_restart_options                ""
% 11.92/1.99  --sat_gr_def                            false
% 11.92/1.99  --sat_epr_types                         true
% 11.92/1.99  --sat_non_cyclic_types                  false
% 11.92/1.99  --sat_finite_models                     false
% 11.92/1.99  --sat_fm_lemmas                         false
% 11.92/1.99  --sat_fm_prep                           false
% 11.92/1.99  --sat_fm_uc_incr                        true
% 11.92/1.99  --sat_out_model                         small
% 11.92/1.99  --sat_out_clauses                       false
% 11.92/1.99  
% 11.92/1.99  ------ QBF Options
% 11.92/1.99  
% 11.92/1.99  --qbf_mode                              false
% 11.92/1.99  --qbf_elim_univ                         false
% 11.92/1.99  --qbf_dom_inst                          none
% 11.92/1.99  --qbf_dom_pre_inst                      false
% 11.92/1.99  --qbf_sk_in                             false
% 11.92/1.99  --qbf_pred_elim                         true
% 11.92/1.99  --qbf_split                             512
% 11.92/1.99  
% 11.92/1.99  ------ BMC1 Options
% 11.92/1.99  
% 11.92/1.99  --bmc1_incremental                      false
% 11.92/1.99  --bmc1_axioms                           reachable_all
% 11.92/1.99  --bmc1_min_bound                        0
% 11.92/1.99  --bmc1_max_bound                        -1
% 11.92/1.99  --bmc1_max_bound_default                -1
% 11.92/1.99  --bmc1_symbol_reachability              true
% 11.92/1.99  --bmc1_property_lemmas                  false
% 11.92/1.99  --bmc1_k_induction                      false
% 11.92/1.99  --bmc1_non_equiv_states                 false
% 11.92/1.99  --bmc1_deadlock                         false
% 11.92/1.99  --bmc1_ucm                              false
% 11.92/1.99  --bmc1_add_unsat_core                   none
% 11.92/1.99  --bmc1_unsat_core_children              false
% 11.92/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.92/1.99  --bmc1_out_stat                         full
% 11.92/1.99  --bmc1_ground_init                      false
% 11.92/1.99  --bmc1_pre_inst_next_state              false
% 11.92/1.99  --bmc1_pre_inst_state                   false
% 11.92/1.99  --bmc1_pre_inst_reach_state             false
% 11.92/1.99  --bmc1_out_unsat_core                   false
% 11.92/1.99  --bmc1_aig_witness_out                  false
% 11.92/1.99  --bmc1_verbose                          false
% 11.92/1.99  --bmc1_dump_clauses_tptp                false
% 11.92/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.92/1.99  --bmc1_dump_file                        -
% 11.92/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.92/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.92/1.99  --bmc1_ucm_extend_mode                  1
% 11.92/1.99  --bmc1_ucm_init_mode                    2
% 11.92/1.99  --bmc1_ucm_cone_mode                    none
% 11.92/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.92/1.99  --bmc1_ucm_relax_model                  4
% 11.92/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.92/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.92/1.99  --bmc1_ucm_layered_model                none
% 11.92/1.99  --bmc1_ucm_max_lemma_size               10
% 11.92/1.99  
% 11.92/1.99  ------ AIG Options
% 11.92/1.99  
% 11.92/1.99  --aig_mode                              false
% 11.92/1.99  
% 11.92/1.99  ------ Instantiation Options
% 11.92/1.99  
% 11.92/1.99  --instantiation_flag                    true
% 11.92/1.99  --inst_sos_flag                         false
% 11.92/1.99  --inst_sos_phase                        true
% 11.92/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.92/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.92/1.99  --inst_lit_sel_side                     num_symb
% 11.92/1.99  --inst_solver_per_active                1400
% 11.92/1.99  --inst_solver_calls_frac                1.
% 11.92/1.99  --inst_passive_queue_type               priority_queues
% 11.92/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.92/1.99  --inst_passive_queues_freq              [25;2]
% 11.92/1.99  --inst_dismatching                      true
% 11.92/1.99  --inst_eager_unprocessed_to_passive     true
% 11.92/1.99  --inst_prop_sim_given                   true
% 11.92/1.99  --inst_prop_sim_new                     false
% 11.92/1.99  --inst_subs_new                         false
% 11.92/1.99  --inst_eq_res_simp                      false
% 11.92/1.99  --inst_subs_given                       false
% 11.92/1.99  --inst_orphan_elimination               true
% 11.92/1.99  --inst_learning_loop_flag               true
% 11.92/1.99  --inst_learning_start                   3000
% 11.92/1.99  --inst_learning_factor                  2
% 11.92/1.99  --inst_start_prop_sim_after_learn       3
% 11.92/1.99  --inst_sel_renew                        solver
% 11.92/1.99  --inst_lit_activity_flag                true
% 11.92/1.99  --inst_restr_to_given                   false
% 11.92/1.99  --inst_activity_threshold               500
% 11.92/1.99  --inst_out_proof                        true
% 11.92/1.99  
% 11.92/1.99  ------ Resolution Options
% 11.92/1.99  
% 11.92/1.99  --resolution_flag                       true
% 11.92/1.99  --res_lit_sel                           adaptive
% 11.92/1.99  --res_lit_sel_side                      none
% 11.92/1.99  --res_ordering                          kbo
% 11.92/1.99  --res_to_prop_solver                    active
% 11.92/1.99  --res_prop_simpl_new                    false
% 11.92/1.99  --res_prop_simpl_given                  true
% 11.92/1.99  --res_passive_queue_type                priority_queues
% 11.92/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.92/1.99  --res_passive_queues_freq               [15;5]
% 11.92/1.99  --res_forward_subs                      full
% 11.92/1.99  --res_backward_subs                     full
% 11.92/1.99  --res_forward_subs_resolution           true
% 11.92/1.99  --res_backward_subs_resolution          true
% 11.92/1.99  --res_orphan_elimination                true
% 11.92/1.99  --res_time_limit                        2.
% 11.92/1.99  --res_out_proof                         true
% 11.92/1.99  
% 11.92/1.99  ------ Superposition Options
% 11.92/1.99  
% 11.92/1.99  --superposition_flag                    true
% 11.92/1.99  --sup_passive_queue_type                priority_queues
% 11.92/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.92/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.92/1.99  --demod_completeness_check              fast
% 11.92/1.99  --demod_use_ground                      true
% 11.92/1.99  --sup_to_prop_solver                    passive
% 11.92/1.99  --sup_prop_simpl_new                    true
% 11.92/1.99  --sup_prop_simpl_given                  true
% 11.92/1.99  --sup_fun_splitting                     false
% 11.92/1.99  --sup_smt_interval                      50000
% 11.92/1.99  
% 11.92/1.99  ------ Superposition Simplification Setup
% 11.92/1.99  
% 11.92/1.99  --sup_indices_passive                   []
% 11.92/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.92/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_full_bw                           [BwDemod]
% 11.92/1.99  --sup_immed_triv                        [TrivRules]
% 11.92/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.92/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_immed_bw_main                     []
% 11.92/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.92/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.92/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.92/1.99  
% 11.92/1.99  ------ Combination Options
% 11.92/1.99  
% 11.92/1.99  --comb_res_mult                         3
% 11.92/1.99  --comb_sup_mult                         2
% 11.92/1.99  --comb_inst_mult                        10
% 11.92/1.99  
% 11.92/1.99  ------ Debug Options
% 11.92/1.99  
% 11.92/1.99  --dbg_backtrace                         false
% 11.92/1.99  --dbg_dump_prop_clauses                 false
% 11.92/1.99  --dbg_dump_prop_clauses_file            -
% 11.92/1.99  --dbg_out_stat                          false
% 11.92/1.99  ------ Parsing...
% 11.92/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.92/1.99  ------ Proving...
% 11.92/1.99  ------ Problem Properties 
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  clauses                                 19
% 11.92/1.99  conjectures                             2
% 11.92/1.99  EPR                                     1
% 11.92/1.99  Horn                                    14
% 11.92/1.99  unary                                   2
% 11.92/1.99  binary                                  1
% 11.92/1.99  lits                                    74
% 11.92/1.99  lits eq                                 9
% 11.92/1.99  fd_pure                                 0
% 11.92/1.99  fd_pseudo                               0
% 11.92/1.99  fd_cond                                 0
% 11.92/1.99  fd_pseudo_cond                          7
% 11.92/1.99  AC symbols                              0
% 11.92/1.99  
% 11.92/1.99  ------ Schedule dynamic 5 is on 
% 11.92/1.99  
% 11.92/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  ------ 
% 11.92/1.99  Current options:
% 11.92/1.99  ------ 
% 11.92/1.99  
% 11.92/1.99  ------ Input Options
% 11.92/1.99  
% 11.92/1.99  --out_options                           all
% 11.92/1.99  --tptp_safe_out                         true
% 11.92/1.99  --problem_path                          ""
% 11.92/1.99  --include_path                          ""
% 11.92/1.99  --clausifier                            res/vclausify_rel
% 11.92/1.99  --clausifier_options                    --mode clausify
% 11.92/1.99  --stdin                                 false
% 11.92/1.99  --stats_out                             all
% 11.92/1.99  
% 11.92/1.99  ------ General Options
% 11.92/1.99  
% 11.92/1.99  --fof                                   false
% 11.92/1.99  --time_out_real                         305.
% 11.92/1.99  --time_out_virtual                      -1.
% 11.92/1.99  --symbol_type_check                     false
% 11.92/1.99  --clausify_out                          false
% 11.92/1.99  --sig_cnt_out                           false
% 11.92/1.99  --trig_cnt_out                          false
% 11.92/1.99  --trig_cnt_out_tolerance                1.
% 11.92/1.99  --trig_cnt_out_sk_spl                   false
% 11.92/1.99  --abstr_cl_out                          false
% 11.92/1.99  
% 11.92/1.99  ------ Global Options
% 11.92/1.99  
% 11.92/1.99  --schedule                              default
% 11.92/1.99  --add_important_lit                     false
% 11.92/1.99  --prop_solver_per_cl                    1000
% 11.92/1.99  --min_unsat_core                        false
% 11.92/1.99  --soft_assumptions                      false
% 11.92/1.99  --soft_lemma_size                       3
% 11.92/1.99  --prop_impl_unit_size                   0
% 11.92/1.99  --prop_impl_unit                        []
% 11.92/1.99  --share_sel_clauses                     true
% 11.92/1.99  --reset_solvers                         false
% 11.92/1.99  --bc_imp_inh                            [conj_cone]
% 11.92/1.99  --conj_cone_tolerance                   3.
% 11.92/1.99  --extra_neg_conj                        none
% 11.92/1.99  --large_theory_mode                     true
% 11.92/1.99  --prolific_symb_bound                   200
% 11.92/1.99  --lt_threshold                          2000
% 11.92/1.99  --clause_weak_htbl                      true
% 11.92/1.99  --gc_record_bc_elim                     false
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing Options
% 11.92/1.99  
% 11.92/1.99  --preprocessing_flag                    true
% 11.92/1.99  --time_out_prep_mult                    0.1
% 11.92/1.99  --splitting_mode                        input
% 11.92/1.99  --splitting_grd                         true
% 11.92/1.99  --splitting_cvd                         false
% 11.92/1.99  --splitting_cvd_svl                     false
% 11.92/1.99  --splitting_nvd                         32
% 11.92/1.99  --sub_typing                            true
% 11.92/1.99  --prep_gs_sim                           true
% 11.92/1.99  --prep_unflatten                        true
% 11.92/1.99  --prep_res_sim                          true
% 11.92/1.99  --prep_upred                            true
% 11.92/1.99  --prep_sem_filter                       exhaustive
% 11.92/1.99  --prep_sem_filter_out                   false
% 11.92/1.99  --pred_elim                             true
% 11.92/1.99  --res_sim_input                         true
% 11.92/1.99  --eq_ax_congr_red                       true
% 11.92/1.99  --pure_diseq_elim                       true
% 11.92/1.99  --brand_transform                       false
% 11.92/1.99  --non_eq_to_eq                          false
% 11.92/1.99  --prep_def_merge                        true
% 11.92/1.99  --prep_def_merge_prop_impl              false
% 11.92/1.99  --prep_def_merge_mbd                    true
% 11.92/1.99  --prep_def_merge_tr_red                 false
% 11.92/1.99  --prep_def_merge_tr_cl                  false
% 11.92/1.99  --smt_preprocessing                     true
% 11.92/1.99  --smt_ac_axioms                         fast
% 11.92/1.99  --preprocessed_out                      false
% 11.92/1.99  --preprocessed_stats                    false
% 11.92/1.99  
% 11.92/1.99  ------ Abstraction refinement Options
% 11.92/1.99  
% 11.92/1.99  --abstr_ref                             []
% 11.92/1.99  --abstr_ref_prep                        false
% 11.92/1.99  --abstr_ref_until_sat                   false
% 11.92/1.99  --abstr_ref_sig_restrict                funpre
% 11.92/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.92/1.99  --abstr_ref_under                       []
% 11.92/1.99  
% 11.92/1.99  ------ SAT Options
% 11.92/1.99  
% 11.92/1.99  --sat_mode                              false
% 11.92/1.99  --sat_fm_restart_options                ""
% 11.92/1.99  --sat_gr_def                            false
% 11.92/1.99  --sat_epr_types                         true
% 11.92/1.99  --sat_non_cyclic_types                  false
% 11.92/1.99  --sat_finite_models                     false
% 11.92/1.99  --sat_fm_lemmas                         false
% 11.92/1.99  --sat_fm_prep                           false
% 11.92/1.99  --sat_fm_uc_incr                        true
% 11.92/1.99  --sat_out_model                         small
% 11.92/1.99  --sat_out_clauses                       false
% 11.92/1.99  
% 11.92/1.99  ------ QBF Options
% 11.92/1.99  
% 11.92/1.99  --qbf_mode                              false
% 11.92/1.99  --qbf_elim_univ                         false
% 11.92/1.99  --qbf_dom_inst                          none
% 11.92/1.99  --qbf_dom_pre_inst                      false
% 11.92/1.99  --qbf_sk_in                             false
% 11.92/1.99  --qbf_pred_elim                         true
% 11.92/1.99  --qbf_split                             512
% 11.92/1.99  
% 11.92/1.99  ------ BMC1 Options
% 11.92/1.99  
% 11.92/1.99  --bmc1_incremental                      false
% 11.92/1.99  --bmc1_axioms                           reachable_all
% 11.92/1.99  --bmc1_min_bound                        0
% 11.92/1.99  --bmc1_max_bound                        -1
% 11.92/1.99  --bmc1_max_bound_default                -1
% 11.92/1.99  --bmc1_symbol_reachability              true
% 11.92/1.99  --bmc1_property_lemmas                  false
% 11.92/1.99  --bmc1_k_induction                      false
% 11.92/1.99  --bmc1_non_equiv_states                 false
% 11.92/1.99  --bmc1_deadlock                         false
% 11.92/1.99  --bmc1_ucm                              false
% 11.92/1.99  --bmc1_add_unsat_core                   none
% 11.92/1.99  --bmc1_unsat_core_children              false
% 11.92/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.92/1.99  --bmc1_out_stat                         full
% 11.92/1.99  --bmc1_ground_init                      false
% 11.92/1.99  --bmc1_pre_inst_next_state              false
% 11.92/1.99  --bmc1_pre_inst_state                   false
% 11.92/1.99  --bmc1_pre_inst_reach_state             false
% 11.92/1.99  --bmc1_out_unsat_core                   false
% 11.92/1.99  --bmc1_aig_witness_out                  false
% 11.92/1.99  --bmc1_verbose                          false
% 11.92/1.99  --bmc1_dump_clauses_tptp                false
% 11.92/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.92/1.99  --bmc1_dump_file                        -
% 11.92/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.92/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.92/1.99  --bmc1_ucm_extend_mode                  1
% 11.92/1.99  --bmc1_ucm_init_mode                    2
% 11.92/1.99  --bmc1_ucm_cone_mode                    none
% 11.92/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.92/1.99  --bmc1_ucm_relax_model                  4
% 11.92/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.92/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.92/1.99  --bmc1_ucm_layered_model                none
% 11.92/1.99  --bmc1_ucm_max_lemma_size               10
% 11.92/1.99  
% 11.92/1.99  ------ AIG Options
% 11.92/1.99  
% 11.92/1.99  --aig_mode                              false
% 11.92/1.99  
% 11.92/1.99  ------ Instantiation Options
% 11.92/1.99  
% 11.92/1.99  --instantiation_flag                    true
% 11.92/1.99  --inst_sos_flag                         false
% 11.92/1.99  --inst_sos_phase                        true
% 11.92/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.92/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.92/1.99  --inst_lit_sel_side                     none
% 11.92/1.99  --inst_solver_per_active                1400
% 11.92/1.99  --inst_solver_calls_frac                1.
% 11.92/1.99  --inst_passive_queue_type               priority_queues
% 11.92/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.92/1.99  --inst_passive_queues_freq              [25;2]
% 11.92/1.99  --inst_dismatching                      true
% 11.92/1.99  --inst_eager_unprocessed_to_passive     true
% 11.92/1.99  --inst_prop_sim_given                   true
% 11.92/1.99  --inst_prop_sim_new                     false
% 11.92/1.99  --inst_subs_new                         false
% 11.92/1.99  --inst_eq_res_simp                      false
% 11.92/1.99  --inst_subs_given                       false
% 11.92/1.99  --inst_orphan_elimination               true
% 11.92/1.99  --inst_learning_loop_flag               true
% 11.92/1.99  --inst_learning_start                   3000
% 11.92/1.99  --inst_learning_factor                  2
% 11.92/1.99  --inst_start_prop_sim_after_learn       3
% 11.92/1.99  --inst_sel_renew                        solver
% 11.92/1.99  --inst_lit_activity_flag                true
% 11.92/1.99  --inst_restr_to_given                   false
% 11.92/1.99  --inst_activity_threshold               500
% 11.92/1.99  --inst_out_proof                        true
% 11.92/1.99  
% 11.92/1.99  ------ Resolution Options
% 11.92/1.99  
% 11.92/1.99  --resolution_flag                       false
% 11.92/1.99  --res_lit_sel                           adaptive
% 11.92/1.99  --res_lit_sel_side                      none
% 11.92/1.99  --res_ordering                          kbo
% 11.92/1.99  --res_to_prop_solver                    active
% 11.92/1.99  --res_prop_simpl_new                    false
% 11.92/1.99  --res_prop_simpl_given                  true
% 11.92/1.99  --res_passive_queue_type                priority_queues
% 11.92/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.92/1.99  --res_passive_queues_freq               [15;5]
% 11.92/1.99  --res_forward_subs                      full
% 11.92/1.99  --res_backward_subs                     full
% 11.92/1.99  --res_forward_subs_resolution           true
% 11.92/1.99  --res_backward_subs_resolution          true
% 11.92/1.99  --res_orphan_elimination                true
% 11.92/1.99  --res_time_limit                        2.
% 11.92/1.99  --res_out_proof                         true
% 11.92/1.99  
% 11.92/1.99  ------ Superposition Options
% 11.92/1.99  
% 11.92/1.99  --superposition_flag                    true
% 11.92/1.99  --sup_passive_queue_type                priority_queues
% 11.92/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.92/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.92/1.99  --demod_completeness_check              fast
% 11.92/1.99  --demod_use_ground                      true
% 11.92/1.99  --sup_to_prop_solver                    passive
% 11.92/1.99  --sup_prop_simpl_new                    true
% 11.92/1.99  --sup_prop_simpl_given                  true
% 11.92/1.99  --sup_fun_splitting                     false
% 11.92/1.99  --sup_smt_interval                      50000
% 11.92/1.99  
% 11.92/1.99  ------ Superposition Simplification Setup
% 11.92/1.99  
% 11.92/1.99  --sup_indices_passive                   []
% 11.92/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.92/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_full_bw                           [BwDemod]
% 11.92/1.99  --sup_immed_triv                        [TrivRules]
% 11.92/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.92/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_immed_bw_main                     []
% 11.92/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.92/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.92/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.92/1.99  
% 11.92/1.99  ------ Combination Options
% 11.92/1.99  
% 11.92/1.99  --comb_res_mult                         3
% 11.92/1.99  --comb_sup_mult                         2
% 11.92/1.99  --comb_inst_mult                        10
% 11.92/1.99  
% 11.92/1.99  ------ Debug Options
% 11.92/1.99  
% 11.92/1.99  --dbg_backtrace                         false
% 11.92/1.99  --dbg_dump_prop_clauses                 false
% 11.92/1.99  --dbg_dump_prop_clauses_file            -
% 11.92/1.99  --dbg_out_stat                          false
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  ------ Proving...
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  % SZS status Theorem for theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  fof(f2,axiom,(
% 11.92/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f9,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 11.92/1.99    inference(ennf_transformation,[],[f2])).
% 11.92/1.99  
% 11.92/1.99  fof(f19,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 11.92/1.99    inference(nnf_transformation,[],[f9])).
% 11.92/1.99  
% 11.92/1.99  fof(f20,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 11.92/1.99    inference(rectify,[],[f19])).
% 11.92/1.99  
% 11.92/1.99  fof(f21,plain,(
% 11.92/1.99    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)))),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f22,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 11.92/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f21])).
% 11.92/1.99  
% 11.92/1.99  fof(f38,plain,(
% 11.92/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f22])).
% 11.92/1.99  
% 11.92/1.99  fof(f3,axiom,(
% 11.92/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f10,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.92/1.99    inference(ennf_transformation,[],[f3])).
% 11.92/1.99  
% 11.92/1.99  fof(f23,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.92/1.99    inference(nnf_transformation,[],[f10])).
% 11.92/1.99  
% 11.92/1.99  fof(f24,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.92/1.99    inference(rectify,[],[f23])).
% 11.92/1.99  
% 11.92/1.99  fof(f27,plain,(
% 11.92/1.99    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)))),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f26,plain,(
% 11.92/1.99    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2)),X0)))) )),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f25,plain,(
% 11.92/1.99    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2))))),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f28,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.92/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f24,f27,f26,f25])).
% 11.92/1.99  
% 11.92/1.99  fof(f41,plain,(
% 11.92/1.99    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f28])).
% 11.92/1.99  
% 11.92/1.99  fof(f55,plain,(
% 11.92/1.99    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.92/1.99    inference(equality_resolution,[],[f41])).
% 11.92/1.99  
% 11.92/1.99  fof(f4,axiom,(
% 11.92/1.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f11,plain,(
% 11.92/1.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 11.92/1.99    inference(ennf_transformation,[],[f4])).
% 11.92/1.99  
% 11.92/1.99  fof(f12,plain,(
% 11.92/1.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 11.92/1.99    inference(flattening,[],[f11])).
% 11.92/1.99  
% 11.92/1.99  fof(f46,plain,(
% 11.92/1.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f12])).
% 11.92/1.99  
% 11.92/1.99  fof(f1,axiom,(
% 11.92/1.99    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f8,plain,(
% 11.92/1.99    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 11.92/1.99    inference(ennf_transformation,[],[f1])).
% 11.92/1.99  
% 11.92/1.99  fof(f14,plain,(
% 11.92/1.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 11.92/1.99    inference(nnf_transformation,[],[f8])).
% 11.92/1.99  
% 11.92/1.99  fof(f15,plain,(
% 11.92/1.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 11.92/1.99    inference(flattening,[],[f14])).
% 11.92/1.99  
% 11.92/1.99  fof(f16,plain,(
% 11.92/1.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 11.92/1.99    inference(rectify,[],[f15])).
% 11.92/1.99  
% 11.92/1.99  fof(f17,plain,(
% 11.92/1.99    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1))))),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f18,plain,(
% 11.92/1.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 11.92/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 11.92/1.99  
% 11.92/1.99  fof(f32,plain,(
% 11.92/1.99    ( ! [X4,X0,X5,X1] : (X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),X1) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f18])).
% 11.92/1.99  
% 11.92/1.99  fof(f52,plain,(
% 11.92/1.99    ( ! [X4,X0,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 11.92/1.99    inference(equality_resolution,[],[f32])).
% 11.92/1.99  
% 11.92/1.99  fof(f5,axiom,(
% 11.92/1.99    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f47,plain,(
% 11.92/1.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.92/1.99    inference(cnf_transformation,[],[f5])).
% 11.92/1.99  
% 11.92/1.99  fof(f40,plain,(
% 11.92/1.99    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f28])).
% 11.92/1.99  
% 11.92/1.99  fof(f56,plain,(
% 11.92/1.99    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.92/1.99    inference(equality_resolution,[],[f40])).
% 11.92/1.99  
% 11.92/1.99  fof(f6,conjecture,(
% 11.92/1.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f7,negated_conjecture,(
% 11.92/1.99    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 11.92/1.99    inference(negated_conjecture,[],[f6])).
% 11.92/1.99  
% 11.92/1.99  fof(f13,plain,(
% 11.92/1.99    ? [X0,X1] : ((~r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) & v1_relat_1(X1))),
% 11.92/1.99    inference(ennf_transformation,[],[f7])).
% 11.92/1.99  
% 11.92/1.99  fof(f29,plain,(
% 11.92/1.99    ? [X0,X1] : ((~r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) & v1_relat_1(X1)) => ((~r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) | ~r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) & v1_relat_1(sK9))),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f30,plain,(
% 11.92/1.99    (~r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) | ~r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) & v1_relat_1(sK9)),
% 11.92/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f13,f29])).
% 11.92/1.99  
% 11.92/1.99  fof(f49,plain,(
% 11.92/1.99    ~r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) | ~r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),
% 11.92/1.99    inference(cnf_transformation,[],[f30])).
% 11.92/1.99  
% 11.92/1.99  fof(f48,plain,(
% 11.92/1.99    v1_relat_1(sK9)),
% 11.92/1.99    inference(cnf_transformation,[],[f30])).
% 11.92/1.99  
% 11.92/1.99  fof(f39,plain,(
% 11.92/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f22])).
% 11.92/1.99  
% 11.92/1.99  fof(f31,plain,(
% 11.92/1.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f18])).
% 11.92/1.99  
% 11.92/1.99  fof(f53,plain,(
% 11.92/1.99    ( ! [X4,X0,X5] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 11.92/1.99    inference(equality_resolution,[],[f31])).
% 11.92/1.99  
% 11.92/1.99  cnf(c_7,plain,
% 11.92/1.99      ( r1_tarski(X0,X1)
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 11.92/1.99      | ~ v1_relat_1(X0) ),
% 11.92/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_548,plain,
% 11.92/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) = iProver_top
% 11.92/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_13,plain,
% 11.92/1.99      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 11.92/1.99      | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X3)
% 11.92/1.99      | ~ v1_relat_1(X3)
% 11.92/1.99      | ~ v1_relat_1(X2)
% 11.92/1.99      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 11.92/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_542,plain,
% 11.92/1.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X3) = iProver_top
% 11.92/1.99      | v1_relat_1(X3) != iProver_top
% 11.92/1.99      | v1_relat_1(X2) != iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_15,plain,
% 11.92/1.99      ( ~ v1_relat_1(X0)
% 11.92/1.99      | ~ v1_relat_1(X1)
% 11.92/1.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 11.92/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_540,plain,
% 11.92/1.99      ( v1_relat_1(X0) != iProver_top
% 11.92/1.99      | v1_relat_1(X1) != iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_649,plain,
% 11.92/1.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X3) = iProver_top
% 11.92/1.99      | v1_relat_1(X3) != iProver_top
% 11.92/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.92/1.99      inference(forward_subsumption_resolution,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_542,c_540]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_4,plain,
% 11.92/1.99      ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
% 11.92/1.99      | ~ v1_relat_1(k6_relat_1(X2))
% 11.92/1.99      | X0 = X1 ),
% 11.92/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_551,plain,
% 11.92/1.99      ( X0 = X1
% 11.92/1.99      | r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) != iProver_top
% 11.92/1.99      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_16,plain,
% 11.92/1.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 11.92/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_539,plain,
% 11.92/1.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_573,plain,
% 11.92/1.99      ( X0 = X1
% 11.92/1.99      | r2_hidden(k4_tarski(X1,X0),k6_relat_1(X2)) != iProver_top ),
% 11.92/1.99      inference(forward_subsumption_resolution,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_551,c_539]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1584,plain,
% 11.92/1.99      ( sK7(X0,k6_relat_1(X1),X2,X3) = X3
% 11.92/1.99      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
% 11.92/1.99      | v1_relat_1(X0) != iProver_top
% 11.92/1.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_649,c_573]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1651,plain,
% 11.92/1.99      ( sK7(X0,k6_relat_1(X1),X2,X3) = X3
% 11.92/1.99      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
% 11.92/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.92/1.99      inference(forward_subsumption_resolution,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_1584,c_539]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1657,plain,
% 11.92/1.99      ( sK7(X0,k6_relat_1(X1),sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)) = sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)
% 11.92/1.99      | r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2) = iProver_top
% 11.92/1.99      | v1_relat_1(X0) != iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_548,c_1651]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_14,plain,
% 11.92/1.99      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 11.92/1.99      | r2_hidden(k4_tarski(X0,sK7(X2,X3,X0,X1)),X2)
% 11.92/1.99      | ~ v1_relat_1(X3)
% 11.92/1.99      | ~ v1_relat_1(X2)
% 11.92/1.99      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 11.92/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_541,plain,
% 11.92/1.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(X0,sK7(X2,X3,X0,X1)),X2) = iProver_top
% 11.92/1.99      | v1_relat_1(X3) != iProver_top
% 11.92/1.99      | v1_relat_1(X2) != iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_639,plain,
% 11.92/1.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(X0,sK7(X2,X3,X0,X1)),X2) = iProver_top
% 11.92/1.99      | v1_relat_1(X3) != iProver_top
% 11.92/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.92/1.99      inference(forward_subsumption_resolution,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_541,c_540]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1279,plain,
% 11.92/1.99      ( sK7(k6_relat_1(X0),X1,X2,X3) = X2
% 11.92/1.99      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 11.92/1.99      | v1_relat_1(X1) != iProver_top
% 11.92/1.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_639,c_573]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_21,plain,
% 11.92/1.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1464,plain,
% 11.92/1.99      ( v1_relat_1(X1) != iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 11.92/1.99      | sK7(k6_relat_1(X0),X1,X2,X3) = X2 ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_1279,c_21]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1465,plain,
% 11.92/1.99      ( sK7(k6_relat_1(X0),X1,X2,X3) = X2
% 11.92/1.99      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 11.92/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.92/1.99      inference(renaming,[status(thm)],[c_1464]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1475,plain,
% 11.92/1.99      ( sK7(k6_relat_1(X0),X1,sK2(k5_relat_1(k6_relat_1(X0),X1),X2),sK3(k5_relat_1(k6_relat_1(X0),X1),X2)) = sK2(k5_relat_1(k6_relat_1(X0),X1),X2)
% 11.92/1.99      | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X2) = iProver_top
% 11.92/1.99      | v1_relat_1(X1) != iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_548,c_1465]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_17,negated_conjecture,
% 11.92/1.99      ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
% 11.92/1.99      | ~ r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) ),
% 11.92/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_538,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) != iProver_top
% 11.92/1.99      | r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_28480,plain,
% 11.92/1.99      ( sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
% 11.92/1.99      | r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) != iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
% 11.92/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_1475,c_538]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_18,negated_conjecture,
% 11.92/1.99      ( v1_relat_1(sK9) ),
% 11.92/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_19,plain,
% 11.92/1.99      ( v1_relat_1(sK9) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_781,plain,
% 11.92/1.99      ( v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9))
% 11.92/1.99      | ~ v1_relat_1(k6_relat_1(sK8))
% 11.92/1.99      | ~ v1_relat_1(sK9) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_782,plain,
% 11.92/1.99      ( v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) = iProver_top
% 11.92/1.99      | v1_relat_1(k6_relat_1(sK8)) != iProver_top
% 11.92/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_831,plain,
% 11.92/1.99      ( v1_relat_1(k6_relat_1(sK8)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_16]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_832,plain,
% 11.92/1.99      ( v1_relat_1(k6_relat_1(sK8)) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_29423,plain,
% 11.92/1.99      ( sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
% 11.92/1.99      | r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) != iProver_top ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_28480,c_19,c_782,c_832]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_29431,plain,
% 11.92/1.99      ( sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
% 11.92/1.99      | sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
% 11.92/1.99      | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
% 11.92/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_1657,c_29423]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1188,plain,
% 11.92/1.99      ( v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)))
% 11.92/1.99      | ~ v1_relat_1(k6_relat_1(sK8))
% 11.92/1.99      | ~ v1_relat_1(sK9) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_29454,plain,
% 11.92/1.99      ( ~ v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)))
% 11.92/1.99      | ~ v1_relat_1(sK9)
% 11.92/1.99      | sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
% 11.92/1.99      | sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) ),
% 11.92/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_29431]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_29456,plain,
% 11.92/1.99      ( sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
% 11.92/1.99      | sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_29431,c_19,c_832,c_1189]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_29460,plain,
% 11.92/1.99      ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9) = iProver_top
% 11.92/1.99      | v1_relat_1(k6_relat_1(sK8)) != iProver_top
% 11.92/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_29456,c_649]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_29979,plain,
% 11.92/1.99      ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9) = iProver_top ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_29460,c_19,c_832]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_29986,plain,
% 11.92/1.99      ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
% 11.92/1.99      | r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) = iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9) = iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_548,c_29979]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_6,plain,
% 11.92/1.99      ( r1_tarski(X0,X1)
% 11.92/1.99      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
% 11.92/1.99      | ~ v1_relat_1(X0) ),
% 11.92/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_755,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
% 11.92/1.99      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9)
% 11.92/1.99      | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_756,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) = iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9) != iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_42100,plain,
% 11.92/1.99      ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
% 11.92/1.99      | r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) = iProver_top ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_29986,c_19,c_756,c_782,c_832]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_42107,plain,
% 11.92/1.99      ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
% 11.92/1.99      | r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_42100,c_538]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_42164,plain,
% 11.92/1.99      ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
% 11.92/1.99      | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
% 11.92/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_1657,c_42107]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1189,plain,
% 11.92/1.99      ( v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) = iProver_top
% 11.92/1.99      | v1_relat_1(k6_relat_1(sK8)) != iProver_top
% 11.92/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_1188]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_44653,plain,
% 11.92/1.99      ( sK7(sK9,k6_relat_1(sK8),sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)) = sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_42164,c_19,c_832,c_1189]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_5,plain,
% 11.92/1.99      ( r2_hidden(X0,X1)
% 11.92/1.99      | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
% 11.92/1.99      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 11.92/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_550,plain,
% 11.92/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top
% 11.92/1.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_579,plain,
% 11.92/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
% 11.92/1.99      inference(forward_subsumption_resolution,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_550,c_539]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1582,plain,
% 11.92/1.99      ( r2_hidden(sK7(X0,k6_relat_1(X1),X2,X3),X1) = iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
% 11.92/1.99      | v1_relat_1(X0) != iProver_top
% 11.92/1.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_649,c_579]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1847,plain,
% 11.92/1.99      ( r2_hidden(sK7(X0,k6_relat_1(X1),X2,X3),X1) = iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
% 11.92/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.92/1.99      inference(forward_subsumption_resolution,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_1582,c_539]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1853,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2) = iProver_top
% 11.92/1.99      | r2_hidden(sK7(X0,k6_relat_1(X1),sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)),X1) = iProver_top
% 11.92/1.99      | v1_relat_1(X0) != iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_548,c_1847]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_44660,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) = iProver_top
% 11.92/1.99      | r2_hidden(sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK8) = iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
% 11.92/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_44653,c_1853]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_909,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)
% 11.92/1.99      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),sK9)
% 11.92/1.99      | ~ v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_910,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) = iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),sK9) != iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_909]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_44657,plain,
% 11.92/1.99      ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),sK9) = iProver_top
% 11.92/1.99      | v1_relat_1(k6_relat_1(sK8)) != iProver_top
% 11.92/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_44653,c_639]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_44843,plain,
% 11.92/1.99      ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),sK9) = iProver_top ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_44657,c_19,c_832]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_44849,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) = iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(sK9,k6_relat_1(sK8)),sK9),sK3(k5_relat_1(sK9,k6_relat_1(sK8)),sK9)),sK9) = iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_548,c_44843]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_45258,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) = iProver_top ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_44660,c_19,c_832,c_910,c_1189,c_44849]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_45264,plain,
% 11.92/1.99      ( sK7(k6_relat_1(sK8),sK9,sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)) = sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9) ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_45258,c_29423]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_46139,plain,
% 11.92/1.99      ( r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),sK9) = iProver_top
% 11.92/1.99      | v1_relat_1(k6_relat_1(sK8)) != iProver_top
% 11.92/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_45264,c_649]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_763,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9)
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),k5_relat_1(k6_relat_1(sK8),sK9))
% 11.92/1.99      | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_764,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) = iProver_top
% 11.92/1.99      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK8),sK9),sK9),sK3(k5_relat_1(k6_relat_1(sK8),sK9),sK9)),k5_relat_1(k6_relat_1(sK8),sK9)) = iProver_top
% 11.92/1.99      | v1_relat_1(k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_20,plain,
% 11.92/1.99      ( r1_tarski(k5_relat_1(k6_relat_1(sK8),sK9),sK9) != iProver_top
% 11.92/1.99      | r1_tarski(k5_relat_1(sK9,k6_relat_1(sK8)),sK9) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(contradiction,plain,
% 11.92/1.99      ( $false ),
% 11.92/1.99      inference(minisat,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_46139,c_45258,c_832,c_782,c_764,c_756,c_20,c_19]) ).
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  ------                               Statistics
% 11.92/1.99  
% 11.92/1.99  ------ General
% 11.92/1.99  
% 11.92/1.99  abstr_ref_over_cycles:                  0
% 11.92/1.99  abstr_ref_under_cycles:                 0
% 11.92/1.99  gc_basic_clause_elim:                   0
% 11.92/1.99  forced_gc_time:                         0
% 11.92/1.99  parsing_time:                           0.008
% 11.92/1.99  unif_index_cands_time:                  0.
% 11.92/1.99  unif_index_add_time:                    0.
% 11.92/1.99  orderings_time:                         0.
% 11.92/1.99  out_proof_time:                         0.015
% 11.92/1.99  total_time:                             1.318
% 11.92/1.99  num_of_symbols:                         47
% 11.92/1.99  num_of_terms:                           37717
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing
% 11.92/1.99  
% 11.92/1.99  num_of_splits:                          0
% 11.92/1.99  num_of_split_atoms:                     0
% 11.92/1.99  num_of_reused_defs:                     0
% 11.92/1.99  num_eq_ax_congr_red:                    42
% 11.92/1.99  num_of_sem_filtered_clauses:            1
% 11.92/1.99  num_of_subtypes:                        0
% 11.92/1.99  monotx_restored_types:                  0
% 11.92/1.99  sat_num_of_epr_types:                   0
% 11.92/1.99  sat_num_of_non_cyclic_types:            0
% 11.92/1.99  sat_guarded_non_collapsed_types:        0
% 11.92/1.99  num_pure_diseq_elim:                    0
% 11.92/1.99  simp_replaced_by:                       0
% 11.92/1.99  res_preprocessed:                       74
% 11.92/1.99  prep_upred:                             0
% 11.92/1.99  prep_unflattend:                        0
% 11.92/1.99  smt_new_axioms:                         0
% 11.92/1.99  pred_elim_cands:                        3
% 11.92/1.99  pred_elim:                              0
% 11.92/1.99  pred_elim_cl:                           0
% 11.92/1.99  pred_elim_cycles:                       1
% 11.92/1.99  merged_defs:                            0
% 11.92/1.99  merged_defs_ncl:                        0
% 11.92/1.99  bin_hyper_res:                          0
% 11.92/1.99  prep_cycles:                            3
% 11.92/1.99  pred_elim_time:                         0.
% 11.92/1.99  splitting_time:                         0.
% 11.92/1.99  sem_filter_time:                        0.
% 11.92/1.99  monotx_time:                            0.001
% 11.92/1.99  subtype_inf_time:                       0.
% 11.92/1.99  
% 11.92/1.99  ------ Problem properties
% 11.92/1.99  
% 11.92/1.99  clauses:                                19
% 11.92/1.99  conjectures:                            2
% 11.92/1.99  epr:                                    1
% 11.92/1.99  horn:                                   14
% 11.92/1.99  ground:                                 2
% 11.92/1.99  unary:                                  2
% 11.92/1.99  binary:                                 1
% 11.92/1.99  lits:                                   74
% 11.92/1.99  lits_eq:                                9
% 11.92/1.99  fd_pure:                                0
% 11.92/1.99  fd_pseudo:                              0
% 11.92/1.99  fd_cond:                                0
% 11.92/1.99  fd_pseudo_cond:                         7
% 11.92/1.99  ac_symbols:                             0
% 11.92/1.99  
% 11.92/1.99  ------ Propositional Solver
% 11.92/1.99  
% 11.92/1.99  prop_solver_calls:                      28
% 11.92/1.99  prop_fast_solver_calls:                 1748
% 11.92/1.99  smt_solver_calls:                       0
% 11.92/1.99  smt_fast_solver_calls:                  0
% 11.92/1.99  prop_num_of_clauses:                    13622
% 11.92/1.99  prop_preprocess_simplified:             13345
% 11.92/1.99  prop_fo_subsumed:                       120
% 11.92/1.99  prop_solver_time:                       0.
% 11.92/1.99  smt_solver_time:                        0.
% 11.92/1.99  smt_fast_solver_time:                   0.
% 11.92/1.99  prop_fast_solver_time:                  0.
% 11.92/1.99  prop_unsat_core_time:                   0.001
% 11.92/1.99  
% 11.92/1.99  ------ QBF
% 11.92/1.99  
% 11.92/1.99  qbf_q_res:                              0
% 11.92/1.99  qbf_num_tautologies:                    0
% 11.92/1.99  qbf_prep_cycles:                        0
% 11.92/1.99  
% 11.92/1.99  ------ BMC1
% 11.92/1.99  
% 11.92/1.99  bmc1_current_bound:                     -1
% 11.92/1.99  bmc1_last_solved_bound:                 -1
% 11.92/1.99  bmc1_unsat_core_size:                   -1
% 11.92/1.99  bmc1_unsat_core_parents_size:           -1
% 11.92/1.99  bmc1_merge_next_fun:                    0
% 11.92/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.92/1.99  
% 11.92/1.99  ------ Instantiation
% 11.92/1.99  
% 11.92/1.99  inst_num_of_clauses:                    1758
% 11.92/1.99  inst_num_in_passive:                    259
% 11.92/1.99  inst_num_in_active:                     720
% 11.92/1.99  inst_num_in_unprocessed:                779
% 11.92/1.99  inst_num_of_loops:                      990
% 11.92/1.99  inst_num_of_learning_restarts:          0
% 11.92/1.99  inst_num_moves_active_passive:          265
% 11.92/1.99  inst_lit_activity:                      0
% 11.92/1.99  inst_lit_activity_moves:                0
% 11.92/1.99  inst_num_tautologies:                   0
% 11.92/1.99  inst_num_prop_implied:                  0
% 11.92/1.99  inst_num_existing_simplified:           0
% 11.92/1.99  inst_num_eq_res_simplified:             0
% 11.92/1.99  inst_num_child_elim:                    0
% 11.92/1.99  inst_num_of_dismatching_blockings:      873
% 11.92/1.99  inst_num_of_non_proper_insts:           2096
% 11.92/1.99  inst_num_of_duplicates:                 0
% 11.92/1.99  inst_inst_num_from_inst_to_res:         0
% 11.92/1.99  inst_dismatching_checking_time:         0.
% 11.92/1.99  
% 11.92/1.99  ------ Resolution
% 11.92/1.99  
% 11.92/1.99  res_num_of_clauses:                     0
% 11.92/1.99  res_num_in_passive:                     0
% 11.92/1.99  res_num_in_active:                      0
% 11.92/1.99  res_num_of_loops:                       77
% 11.92/1.99  res_forward_subset_subsumed:            156
% 11.92/1.99  res_backward_subset_subsumed:           0
% 11.92/1.99  res_forward_subsumed:                   0
% 11.92/1.99  res_backward_subsumed:                  0
% 11.92/1.99  res_forward_subsumption_resolution:     0
% 11.92/1.99  res_backward_subsumption_resolution:    0
% 11.92/1.99  res_clause_to_clause_subsumption:       10647
% 11.92/1.99  res_orphan_elimination:                 0
% 11.92/1.99  res_tautology_del:                      171
% 11.92/1.99  res_num_eq_res_simplified:              0
% 11.92/1.99  res_num_sel_changes:                    0
% 11.92/1.99  res_moves_from_active_to_pass:          0
% 11.92/1.99  
% 11.92/1.99  ------ Superposition
% 11.92/1.99  
% 11.92/1.99  sup_time_total:                         0.
% 11.92/1.99  sup_time_generating:                    0.
% 11.92/1.99  sup_time_sim_full:                      0.
% 11.92/1.99  sup_time_sim_immed:                     0.
% 11.92/1.99  
% 11.92/1.99  sup_num_of_clauses:                     2058
% 11.92/1.99  sup_num_in_active:                      165
% 11.92/1.99  sup_num_in_passive:                     1893
% 11.92/1.99  sup_num_of_loops:                       196
% 11.92/1.99  sup_fw_superposition:                   934
% 11.92/1.99  sup_bw_superposition:                   1467
% 11.92/1.99  sup_immediate_simplified:               120
% 11.92/1.99  sup_given_eliminated:                   0
% 11.92/1.99  comparisons_done:                       0
% 11.92/1.99  comparisons_avoided:                    87
% 11.92/1.99  
% 11.92/1.99  ------ Simplifications
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  sim_fw_subset_subsumed:                 37
% 11.92/1.99  sim_bw_subset_subsumed:                 163
% 11.92/1.99  sim_fw_subsumed:                        68
% 11.92/1.99  sim_bw_subsumed:                        17
% 11.92/1.99  sim_fw_subsumption_res:                 23
% 11.92/1.99  sim_bw_subsumption_res:                 0
% 11.92/1.99  sim_tautology_del:                      27
% 11.92/1.99  sim_eq_tautology_del:                   12
% 11.92/1.99  sim_eq_res_simp:                        1
% 11.92/1.99  sim_fw_demodulated:                     0
% 11.92/1.99  sim_bw_demodulated:                     0
% 11.92/1.99  sim_light_normalised:                   0
% 11.92/1.99  sim_joinable_taut:                      0
% 11.92/1.99  sim_joinable_simp:                      0
% 11.92/1.99  sim_ac_normalised:                      0
% 11.92/1.99  sim_smt_subsumption:                    0
% 11.92/1.99  
%------------------------------------------------------------------------------
