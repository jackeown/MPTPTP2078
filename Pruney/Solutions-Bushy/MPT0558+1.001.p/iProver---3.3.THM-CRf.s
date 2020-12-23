%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0558+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:35 EST 2020

% Result     : Theorem 15.82s
% Output     : CNFRefutation 15.90s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 163 expanded)
%              Number of clauses        :   27 (  31 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  389 ( 950 expanded)
%              Number of equality atoms :   46 ( 135 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f22,f21,f20])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(X1,k2_relat_1(X0)) != k2_relat_1(k5_relat_1(X0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k9_relat_1(X1,k2_relat_1(X0)) != k2_relat_1(k5_relat_1(X0,X1))
          & v1_relat_1(X1) )
     => ( k9_relat_1(sK11,k2_relat_1(X0)) != k2_relat_1(k5_relat_1(X0,sK11))
        & v1_relat_1(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k9_relat_1(X1,k2_relat_1(X0)) != k2_relat_1(k5_relat_1(X0,X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k9_relat_1(X1,k2_relat_1(sK10)) != k2_relat_1(k5_relat_1(sK10,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k9_relat_1(sK11,k2_relat_1(sK10)) != k2_relat_1(k5_relat_1(sK10,sK11))
    & v1_relat_1(sK11)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f11,f31,f30])).

fof(f52,plain,(
    k9_relat_1(sK11,k2_relat_1(sK10)) != k2_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21456,plain,
    ( r2_hidden(sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(k5_relat_1(sK10,sK11)))
    | ~ r2_hidden(k4_tarski(sK5(sK10,sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(X0,sK0(X2,X1,X3)),X2)
    | ~ v1_relat_1(X2)
    | k9_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5782,plain,
    ( ~ r2_hidden(sK9(sK10,sK11,sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),k2_relat_1(sK10))
    | ~ r2_hidden(sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(k5_relat_1(sK10,sK11)))
    | ~ r2_hidden(k4_tarski(sK9(sK10,sK11,sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK11)
    | ~ v1_relat_1(sK11)
    | k9_relat_1(sK11,k2_relat_1(sK10)) = k2_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5769,plain,
    ( r2_hidden(sK9(sK10,sK11,sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),k2_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK9(sK10,sK11,sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))))),sK10) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,negated_conjecture,
    ( k9_relat_1(sK11,k2_relat_1(sK10)) != k2_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4640,plain,
    ( r2_hidden(sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(sK10))
    | r2_hidden(sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(k5_relat_1(sK10,sK11)))
    | ~ v1_relat_1(sK11) ),
    inference(resolution,[status(thm)],[c_1,c_17])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5113,plain,
    ( r2_hidden(sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(k5_relat_1(sK10,sK11)))
    | r2_hidden(sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4640,c_18])).

cnf(c_5114,plain,
    ( r2_hidden(sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(sK10))
    | r2_hidden(sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(k5_relat_1(sK10,sK11))) ),
    inference(renaming,[status(thm)],[c_5113])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_821,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),X0),X1)
    | r2_hidden(k4_tarski(sK5(sK10,sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),X0),k5_relat_1(sK10,X1))
    | ~ r2_hidden(k4_tarski(sK5(sK10,sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK10)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(sK10,X1))
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4696,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK11)
    | ~ r2_hidden(k4_tarski(sK5(sK10,sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK10)
    | r2_hidden(k4_tarski(sK5(sK10,sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK10)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1979,plain,
    ( v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK10)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK9(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1021,plain,
    ( r2_hidden(k4_tarski(sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK9(sK10,sK11,sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))))),sK10)
    | ~ r2_hidden(k4_tarski(sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK10)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK9(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1022,plain,
    ( r2_hidden(k4_tarski(sK9(sK10,sK11,sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK11)
    | ~ r2_hidden(k4_tarski(sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK10)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_794,plain,
    ( ~ r2_hidden(sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(k5_relat_1(sK10,sK11)))
    | r2_hidden(k4_tarski(sK5(k5_relat_1(sK10,sK11),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_754,plain,
    ( ~ r2_hidden(sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(sK10))
    | r2_hidden(k4_tarski(sK5(sK10,sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK10) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_746,plain,
    ( r2_hidden(sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(k5_relat_1(sK10,sK11)))
    | r2_hidden(k4_tarski(sK1(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11))),sK0(sK11,k2_relat_1(sK10),k2_relat_1(k5_relat_1(sK10,sK11)))),sK11)
    | ~ v1_relat_1(sK11)
    | k9_relat_1(sK11,k2_relat_1(sK10)) = k2_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21456,c_5782,c_5769,c_5114,c_4696,c_1979,c_1021,c_1022,c_794,c_754,c_746,c_17,c_18,c_19])).


%------------------------------------------------------------------------------
