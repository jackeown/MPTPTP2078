%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0462+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:21 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 203 expanded)
%              Number of clauses        :   40 (  49 expanded)
%              Number of leaves         :   12 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  400 (1290 expanded)
%              Number of equality atoms :   15 (  31 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f27,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f16,plain,(
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
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f20,f19,f18])).

fof(f32,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f31,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ! [X3] :
                    ( v1_relat_1(X3)
                   => ( ( r1_tarski(X2,X3)
                        & r1_tarski(X0,X1) )
                     => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,sK9))
        & r1_tarski(X2,sK9)
        & r1_tarski(X0,X1)
        & v1_relat_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
              & r1_tarski(X2,X3)
              & r1_tarski(X0,X1)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k5_relat_1(X0,sK8),k5_relat_1(X1,X3))
            & r1_tarski(sK8,X3)
            & r1_tarski(X0,X1)
            & v1_relat_1(X3) )
        & v1_relat_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(sK7,X3))
                & r1_tarski(X2,X3)
                & r1_tarski(X0,sK7)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                    & r1_tarski(X2,X3)
                    & r1_tarski(X0,X1)
                    & v1_relat_1(X3) )
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(sK6,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(sK6,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))
    & r1_tarski(sK8,sK9)
    & r1_tarski(sK6,sK7)
    & v1_relat_1(sK9)
    & v1_relat_1(sK8)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f11,f25,f24,f23,f22])).

fof(f43,plain,(
    ~ r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f26])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    r1_tarski(sK8,sK9) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_2,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X0,X1),X3)
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_315,plain,
    ( ~ r2_hidden(k4_tarski(X0_45,X1_45),X0_43)
    | r2_hidden(k4_tarski(X0_45,X1_45),X1_43)
    | ~ r1_tarski(X0_43,X1_43)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1113,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)))),X0_43)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)))),sK6)
    | ~ r1_tarski(sK6,X0_43)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_16768,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)))),sK7)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)))),sK6)
    | ~ r1_tarski(sK6,sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_311,plain,
    ( ~ r2_hidden(k4_tarski(X0_45,X1_45),X0_43)
    | ~ r2_hidden(k4_tarski(X2_45,X0_45),X1_43)
    | r2_hidden(k4_tarski(X2_45,X1_45),k5_relat_1(X1_43,X0_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | ~ v1_relat_1(k5_relat_1(X1_43,X0_43)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2296,plain,
    ( ~ r2_hidden(k4_tarski(X0_45,sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)))),X0_43)
    | r2_hidden(k4_tarski(X0_45,sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),k5_relat_1(X0_43,sK9))
    | ~ r2_hidden(k4_tarski(sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK9)
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(k5_relat_1(X0_43,sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_4734,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK9)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)))),X0_43)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),k5_relat_1(X0_43,sK9))
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(k5_relat_1(X0_43,sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_2296])).

cnf(c_5983,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK9)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)))),sK7)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),k5_relat_1(sK7,sK9))
    | ~ v1_relat_1(k5_relat_1(sK7,sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4734])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_308,plain,
    ( ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | v1_relat_1(k5_relat_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2679,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(k5_relat_1(X0_43,sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_4728,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2679])).

cnf(c_1174,plain,
    ( r2_hidden(k4_tarski(sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),X0_43)
    | ~ r2_hidden(k4_tarski(sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK8)
    | ~ r1_tarski(sK8,X0_43)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_1428,plain,
    ( r2_hidden(k4_tarski(sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK9)
    | ~ r2_hidden(k4_tarski(sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK8)
    | ~ r1_tarski(sK8,sK9)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_8,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_309,plain,
    ( ~ r2_hidden(k4_tarski(X0_45,X1_45),k5_relat_1(X0_43,X1_43))
    | r2_hidden(k4_tarski(X0_45,sK5(X0_43,X1_43,X0_45,X1_45)),X0_43)
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | ~ v1_relat_1(k5_relat_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_404,plain,
    ( ~ v1_relat_1(X1_43)
    | ~ v1_relat_1(X0_43)
    | r2_hidden(k4_tarski(X0_45,sK5(X0_43,X1_43,X0_45,X1_45)),X0_43)
    | ~ r2_hidden(k4_tarski(X0_45,X1_45),k5_relat_1(X0_43,X1_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_308])).

cnf(c_405,plain,
    ( ~ r2_hidden(k4_tarski(X0_45,X1_45),k5_relat_1(X0_43,X1_43))
    | r2_hidden(k4_tarski(X0_45,sK5(X0_43,X1_43,X0_45,X1_45)),X0_43)
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43) ),
    inference(renaming,[status(thm)],[c_404])).

cnf(c_955,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)))),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),k5_relat_1(sK6,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_7,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_310,plain,
    ( ~ r2_hidden(k4_tarski(X0_45,X1_45),k5_relat_1(X0_43,X1_43))
    | r2_hidden(k4_tarski(sK5(X0_43,X1_43,X0_45,X1_45),X1_45),X1_43)
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | ~ v1_relat_1(k5_relat_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_397,plain,
    ( ~ v1_relat_1(X1_43)
    | ~ v1_relat_1(X0_43)
    | r2_hidden(k4_tarski(sK5(X0_43,X1_43,X0_45,X1_45),X1_45),X1_43)
    | ~ r2_hidden(k4_tarski(X0_45,X1_45),k5_relat_1(X0_43,X1_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_310,c_308])).

cnf(c_398,plain,
    ( ~ r2_hidden(k4_tarski(X0_45,X1_45),k5_relat_1(X0_43,X1_43))
    | r2_hidden(k4_tarski(sK5(X0_43,X1_43,X0_45,X1_45),X1_45),X1_43)
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43) ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_956,plain,
    ( r2_hidden(k4_tarski(sK5(sK6,sK8,sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),sK8)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),k5_relat_1(sK6,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_880,plain,
    ( v1_relat_1(k5_relat_1(sK6,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_221,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(sK7,sK9) != X1
    | k5_relat_1(sK6,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_222,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),k5_relat_1(sK7,sK9))
    | ~ v1_relat_1(k5_relat_1(sK6,sK8)) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_211,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(sK7,sK9) != X1
    | k5_relat_1(sK6,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_212,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9)),sK1(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK9))),k5_relat_1(sK6,sK8))
    | ~ v1_relat_1(k5_relat_1(sK6,sK8)) ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK8,sK9) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16768,c_5983,c_4728,c_1428,c_955,c_956,c_880,c_222,c_212,c_11,c_12,c_13,c_14,c_15,c_16])).


%------------------------------------------------------------------------------
