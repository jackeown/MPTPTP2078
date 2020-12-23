%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0578+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:39 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 176 expanded)
%              Number of clauses        :   40 (  44 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  429 ( 990 expanded)
%              Number of equality atoms :   86 ( 175 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f22,f21,f20])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f40])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK8(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK7(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK6(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),sK7(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f25,f28,f27,f26])).

fof(f45,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1))
          & v1_relat_1(X1) )
     => ( k10_relat_1(X0,k1_relat_1(sK11)) != k1_relat_1(k5_relat_1(X0,sK11))
        & v1_relat_1(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k10_relat_1(sK10,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(sK10,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k10_relat_1(sK10,k1_relat_1(sK11)) != k1_relat_1(k5_relat_1(sK10,sK11))
    & v1_relat_1(sK11)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f11,f31,f30])).

fof(f52,plain,(
    k10_relat_1(sK10,k1_relat_1(sK11)) != k1_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f44,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15242,plain,
    ( r2_hidden(sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k1_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK11) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_15243,plain,
    ( r2_hidden(sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k1_relat_1(sK11)) = iProver_top
    | r2_hidden(k4_tarski(sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15242])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(sK0(X2,X1,X3),X0),X2)
    | ~ v1_relat_1(X2)
    | k10_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15216,plain,
    ( ~ r2_hidden(sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k1_relat_1(sK11))
    | ~ r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
    | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11)))))),sK10)
    | ~ v1_relat_1(sK10)
    | k10_relat_1(sK10,k1_relat_1(sK11)) = k1_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_15217,plain,
    ( k10_relat_1(sK10,k1_relat_1(sK11)) = k1_relat_1(k5_relat_1(sK10,sK11))
    | r2_hidden(sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k1_relat_1(sK11)) != iProver_top
    | r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11)))))),sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15216])).

cnf(c_13440,plain,
    ( r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
    | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(sK11,sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_13441,plain,
    ( r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11))) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(sK11,sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13440])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_842,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),X0),X1)
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),X0),k5_relat_1(sK10,X1))
    | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11)))),sK10)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(sK10,X1))
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5728,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(sK11,sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK11)
    | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11)))),sK10)
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(sK11,sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_5729,plain,
    ( r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(sK11,sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK11) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11)))),sK10) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(sK11,sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11)) = iProver_top
    | v1_relat_1(k5_relat_1(sK10,sK11)) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5728])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,negated_conjecture,
    ( k10_relat_1(sK10,k1_relat_1(sK11)) != k1_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4629,plain,
    ( r2_hidden(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK11))
    | r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
    | ~ v1_relat_1(sK10) ),
    inference(resolution,[status(thm)],[c_1,c_17])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5151,plain,
    ( r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
    | r2_hidden(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4629,c_19])).

cnf(c_5152,plain,
    ( r2_hidden(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK11))
    | r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11))) ),
    inference(renaming,[status(thm)],[c_5151])).

cnf(c_5153,plain,
    ( r2_hidden(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK11)) = iProver_top
    | r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5152])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1954,plain,
    ( v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1955,plain,
    ( v1_relat_1(k5_relat_1(sK10,sK11)) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1954])).

cnf(c_15,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK9(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1021,plain,
    ( r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11)))))),sK10)
    | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1025,plain,
    ( r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11)))))),sK10) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11)) != iProver_top
    | v1_relat_1(k5_relat_1(sK10,sK11)) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK9(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1022,plain,
    ( r2_hidden(k4_tarski(sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK11)
    | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1023,plain,
    ( r2_hidden(k4_tarski(sK9(sK10,sK11,sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK11) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11)) != iProver_top
    | v1_relat_1(k5_relat_1(sK10,sK11)) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_794,plain,
    ( ~ r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_795,plain,
    ( r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_754,plain,
    ( ~ r2_hidden(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK11))
    | r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(sK11,sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK11) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_755,plain,
    ( r2_hidden(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK5(sK11,sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))))),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_746,plain,
    ( r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11)))),sK10)
    | ~ v1_relat_1(sK10)
    | k10_relat_1(sK10,k1_relat_1(sK11)) = k1_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_747,plain,
    ( k10_relat_1(sK10,k1_relat_1(sK11)) = k1_relat_1(k5_relat_1(sK10,sK11))
    | r2_hidden(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11))) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(sK11),k1_relat_1(k5_relat_1(sK10,sK11)))),sK10) = iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,plain,
    ( v1_relat_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15243,c_15217,c_13441,c_5729,c_5153,c_1955,c_1025,c_1023,c_795,c_755,c_747,c_17,c_21,c_20])).


%------------------------------------------------------------------------------
