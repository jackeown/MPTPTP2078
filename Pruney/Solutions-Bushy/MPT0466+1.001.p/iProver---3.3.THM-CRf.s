%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0466+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 35.21s
% Output     : CNFRefutation 35.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 253 expanded)
%              Number of clauses        :   59 (  92 expanded)
%              Number of leaves         :   13 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  478 (1405 expanded)
%              Number of equality atoms :   57 ( 157 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(nnf_transformation,[],[f8])).

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
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
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
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f21,f20,f19])).

fof(f32,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X5,X1] :
      ( k5_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f27,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f30,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f26,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) != k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) != k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          & v1_relat_1(X1) )
     => ( k4_relat_1(k5_relat_1(X0,sK7)) != k5_relat_1(k4_relat_1(sK7),k4_relat_1(X0))
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_relat_1(k5_relat_1(X0,X1)) != k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k4_relat_1(k5_relat_1(sK6,X1)) != k5_relat_1(k4_relat_1(X1),k4_relat_1(sK6))
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k4_relat_1(k5_relat_1(sK6,sK7)) != k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6))
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f12,f24,f23])).

fof(f40,plain,(
    k4_relat_1(k5_relat_1(sK6,sK7)) != k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_7,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_167,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),X0_41)
    | ~ r2_hidden(k4_tarski(X2_43,X0_43),X1_41)
    | r2_hidden(k4_tarski(X2_43,X1_43),k5_relat_1(X1_41,X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(k5_relat_1(X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_163,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | v1_relat_1(k5_relat_1(X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_266,plain,
    ( ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(X0_41)
    | r2_hidden(k4_tarski(X2_43,X1_43),k5_relat_1(X1_41,X0_41))
    | ~ r2_hidden(k4_tarski(X2_43,X0_43),X1_41)
    | ~ r2_hidden(k4_tarski(X0_43,X1_43),X0_41) ),
    inference(global_propositional_subsumption,[status(thm)],[c_167,c_163])).

cnf(c_267,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),X0_41)
    | ~ r2_hidden(k4_tarski(X2_43,X0_43),X1_41)
    | r2_hidden(k4_tarski(X2_43,X1_43),k5_relat_1(X1_41,X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41) ),
    inference(renaming,[status(thm)],[c_266])).

cnf(c_7815,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),X0_43),X0_41)
    | r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),X0_43),k5_relat_1(sK6,X0_41))
    | ~ r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK6)
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_79805,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK7)
    | ~ r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK6)
    | r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_7815])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK3(X1,X2,X3)),X2)
    | ~ r2_hidden(k4_tarski(sK2(X1,X2,X3),X0),X1)
    | ~ r2_hidden(k4_tarski(sK2(X1,X2,X3),sK3(X1,X2,X3)),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | k5_relat_1(X1,X2) = X3 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_170,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,sK3(X0_41,X1_41,X2_41)),X1_41)
    | ~ r2_hidden(k4_tarski(sK2(X0_41,X1_41,X2_41),X0_43),X0_41)
    | ~ r2_hidden(k4_tarski(sK2(X0_41,X1_41,X2_41),sK3(X0_41,X1_41,X2_41)),X2_41)
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(X2_41)
    | k5_relat_1(X0_41,X1_41) = X2_41 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_73444,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK6,sK7,sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK5(sK6,sK7,sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))))),k4_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(k5_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k4_relat_1(sK7))
    | ~ v1_relat_1(k4_relat_1(sK6))
    | k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6)) = k4_relat_1(k5_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_2,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_172,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),X0_41)
    | r2_hidden(k4_tarski(X1_43,X0_43),k4_relat_1(X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(k4_relat_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_164,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k4_relat_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_249,plain,
    ( ~ v1_relat_1(X0_41)
    | r2_hidden(k4_tarski(X1_43,X0_43),k4_relat_1(X0_41))
    | ~ r2_hidden(k4_tarski(X0_43,X1_43),X0_41) ),
    inference(global_propositional_subsumption,[status(thm)],[c_172,c_164])).

cnf(c_250,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),X0_41)
    | r2_hidden(k4_tarski(X1_43,X0_43),k4_relat_1(X0_41))
    | ~ v1_relat_1(X0_41) ),
    inference(renaming,[status(thm)],[c_249])).

cnf(c_19190,plain,
    ( r2_hidden(k4_tarski(sK5(sK6,sK7,sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK5(sK6,sK7,sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))))),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_19177,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK6,sK7,sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK7)
    | r2_hidden(k4_tarski(sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK5(sK6,sK7,sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))))),k4_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_6493,plain,
    ( r2_hidden(k4_tarski(sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(k5_relat_1(sK6,sK7)))
    | ~ r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(k5_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_8,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_166,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_41,X1_41))
    | r2_hidden(k4_tarski(sK5(X0_41,X1_41,X0_43,X1_43),X1_43),X1_41)
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(k5_relat_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_6487,plain,
    ( r2_hidden(k4_tarski(sK5(sK6,sK7,sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK7)
    | ~ r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_165,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_41,X1_41))
    | r2_hidden(k4_tarski(X0_43,sK5(X0_41,X1_41,X0_43,X1_43)),X0_41)
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(k5_relat_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_6488,plain,
    ( r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK5(sK6,sK7,sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))))),sK6)
    | ~ r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_3,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_171,plain,
    ( r2_hidden(k4_tarski(X0_43,X1_43),X0_41)
    | ~ r2_hidden(k4_tarski(X1_43,X0_43),k4_relat_1(X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(k4_relat_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_256,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ r2_hidden(k4_tarski(X1_43,X0_43),k4_relat_1(X0_41))
    | r2_hidden(k4_tarski(X0_43,X1_43),X0_41) ),
    inference(global_propositional_subsumption,[status(thm)],[c_171,c_164])).

cnf(c_257,plain,
    ( r2_hidden(k4_tarski(X0_43,X1_43),X0_41)
    | ~ r2_hidden(k4_tarski(X1_43,X0_43),k4_relat_1(X0_41))
    | ~ v1_relat_1(X0_41) ),
    inference(renaming,[status(thm)],[c_256])).

cnf(c_859,plain,
    ( r2_hidden(k4_tarski(sK4(k4_relat_1(X0_41),X1_41,X2_41),sK2(k4_relat_1(X0_41),X1_41,X2_41)),X0_41)
    | ~ r2_hidden(k4_tarski(sK2(k4_relat_1(X0_41),X1_41,X2_41),sK4(k4_relat_1(X0_41),X1_41,X2_41)),k4_relat_1(X0_41))
    | ~ v1_relat_1(X0_41) ),
    inference(instantiation,[status(thm)],[c_257])).

cnf(c_2093,plain,
    ( r2_hidden(k4_tarski(sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(X0_41)),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(X0_41))),sK7)
    | ~ r2_hidden(k4_tarski(sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(X0_41)),sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(X0_41))),k4_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_3339,plain,
    ( r2_hidden(k4_tarski(sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK7)
    | ~ r2_hidden(k4_tarski(sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_899,plain,
    ( ~ r2_hidden(k4_tarski(sK4(X0_41,k4_relat_1(X1_41),X2_41),sK3(X0_41,k4_relat_1(X1_41),X2_41)),k4_relat_1(X1_41))
    | r2_hidden(k4_tarski(sK3(X0_41,k4_relat_1(X1_41),X2_41),sK4(X0_41,k4_relat_1(X1_41),X2_41)),X1_41)
    | ~ v1_relat_1(X1_41) ),
    inference(instantiation,[status(thm)],[c_257])).

cnf(c_2979,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(sK6))
    | r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_627,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0_41,X1_41,k4_relat_1(X2_41)),sK3(X0_41,X1_41,k4_relat_1(X2_41))),k4_relat_1(X2_41))
    | r2_hidden(k4_tarski(sK3(X0_41,X1_41,k4_relat_1(X2_41)),sK2(X0_41,X1_41,k4_relat_1(X2_41))),X2_41)
    | ~ v1_relat_1(X2_41) ),
    inference(instantiation,[status(thm)],[c_257])).

cnf(c_1865,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(k5_relat_1(sK6,sK7)))
    | r2_hidden(k4_tarski(sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(k5_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_5,plain,
    ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_169,plain,
    ( r2_hidden(k4_tarski(sK4(X0_41,X1_41,X2_41),sK3(X0_41,X1_41,X2_41)),X1_41)
    | r2_hidden(k4_tarski(sK2(X0_41,X1_41,X2_41),sK3(X0_41,X1_41,X2_41)),X2_41)
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(X2_41)
    | k5_relat_1(X0_41,X1_41) = X2_41 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_898,plain,
    ( r2_hidden(k4_tarski(sK4(X0_41,k4_relat_1(X1_41),X2_41),sK3(X0_41,k4_relat_1(X1_41),X2_41)),k4_relat_1(X1_41))
    | r2_hidden(k4_tarski(sK2(X0_41,k4_relat_1(X1_41),X2_41),sK3(X0_41,k4_relat_1(X1_41),X2_41)),X2_41)
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X2_41)
    | ~ v1_relat_1(k4_relat_1(X1_41))
    | k5_relat_1(X0_41,k4_relat_1(X1_41)) = X2_41 ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_1706,plain,
    ( r2_hidden(k4_tarski(sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(sK6))
    | r2_hidden(k4_tarski(sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(k5_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k4_relat_1(sK7))
    | ~ v1_relat_1(k4_relat_1(sK6))
    | k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6)) = k4_relat_1(k5_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1284,plain,
    ( ~ v1_relat_1(k5_relat_1(sK6,sK7))
    | v1_relat_1(k4_relat_1(k5_relat_1(sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_1063,plain,
    ( v1_relat_1(k4_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_1001,plain,
    ( v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_6,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_168,plain,
    ( r2_hidden(k4_tarski(sK2(X0_41,X1_41,X2_41),sK4(X0_41,X1_41,X2_41)),X0_41)
    | r2_hidden(k4_tarski(sK2(X0_41,X1_41,X2_41),sK3(X0_41,X1_41,X2_41)),X2_41)
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(X2_41)
    | k5_relat_1(X0_41,X1_41) = X2_41 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_626,plain,
    ( r2_hidden(k4_tarski(sK2(X0_41,X1_41,k4_relat_1(X2_41)),sK4(X0_41,X1_41,k4_relat_1(X2_41))),X0_41)
    | r2_hidden(k4_tarski(sK2(X0_41,X1_41,k4_relat_1(X2_41)),sK3(X0_41,X1_41,k4_relat_1(X2_41))),k4_relat_1(X2_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(k4_relat_1(X2_41))
    | k5_relat_1(X0_41,X1_41) = k4_relat_1(X2_41) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_913,plain,
    ( r2_hidden(k4_tarski(sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK4(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(sK7))
    | r2_hidden(k4_tarski(sK2(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7))),sK3(k4_relat_1(sK7),k4_relat_1(sK6),k4_relat_1(k5_relat_1(sK6,sK7)))),k4_relat_1(k5_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k4_relat_1(sK7))
    | ~ v1_relat_1(k4_relat_1(sK6))
    | k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6)) = k4_relat_1(k5_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_176,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_655,plain,
    ( k4_relat_1(k5_relat_1(sK6,sK7)) = k4_relat_1(k5_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_179,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_533,plain,
    ( k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6)) != X0_41
    | k4_relat_1(k5_relat_1(sK6,sK7)) != X0_41
    | k4_relat_1(k5_relat_1(sK6,sK7)) = k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_654,plain,
    ( k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6)) != k4_relat_1(k5_relat_1(sK6,sK7))
    | k4_relat_1(k5_relat_1(sK6,sK7)) = k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6))
    | k4_relat_1(k5_relat_1(sK6,sK7)) != k4_relat_1(k5_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_12,negated_conjecture,
    ( k4_relat_1(k5_relat_1(sK6,sK7)) != k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_162,negated_conjecture,
    ( k4_relat_1(k5_relat_1(sK6,sK7)) != k5_relat_1(k4_relat_1(sK7),k4_relat_1(sK6)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_21,plain,
    ( v1_relat_1(k4_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79805,c_73444,c_19190,c_19177,c_6493,c_6487,c_6488,c_3339,c_2979,c_1865,c_1706,c_1284,c_1063,c_1001,c_913,c_655,c_654,c_162,c_21,c_13,c_14])).


%------------------------------------------------------------------------------
