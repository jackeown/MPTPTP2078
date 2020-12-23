%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0481+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:24 EST 2020

% Result     : Theorem 11.66s
% Output     : CNFRefutation 11.66s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
