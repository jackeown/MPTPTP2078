%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0480+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:24 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  122 (2030 expanded)
%              Number of clauses        :   77 ( 644 expanded)
%              Number of leaves         :   10 ( 421 expanded)
%              Depth                    :   28
%              Number of atoms          :  572 (11917 expanded)
%              Number of equality atoms :  260 (2322 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
        <=> ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <~> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      & v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & v1_relat_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
        & v1_relat_1(X3) )
   => ( ( ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
        | ~ r2_hidden(sK7,sK8)
        | ~ r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) )
      & ( ( r2_hidden(k4_tarski(sK6,sK7),sK9)
          & r2_hidden(sK7,sK8) )
        | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
      | ~ r2_hidden(sK7,sK8)
      | ~ r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) )
    & ( ( r2_hidden(k4_tarski(sK6,sK7),sK9)
        & r2_hidden(sK7,sK8) )
      | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f24,f25])).

fof(f43,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),sK9)
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,
    ( r2_hidden(sK7,sK8)
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f35,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f41,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
    | ~ r2_hidden(sK7,sK8)
    | ~ r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f29,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f46,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f28,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f33,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f27,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_502,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8)))
    | r2_hidden(k4_tarski(sK6,sK7),sK9) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_499,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8)))
    | r2_hidden(sK7,sK8) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_498,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) = iProver_top
    | r2_hidden(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_505,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X4) != iProver_top
    | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_609,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_505,c_502])).

cnf(c_5837,plain,
    ( r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,k5_relat_1(sK9,k6_relat_1(sK8)))) = iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | r2_hidden(sK7,sK8) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_609])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8)))
    | ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
    | ~ r2_hidden(sK7,sK8) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) != iProver_top
    | r2_hidden(sK7,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1713,plain,
    ( r2_hidden(k4_tarski(sK7,sK7),k6_relat_1(sK8))
    | ~ r2_hidden(sK7,sK8)
    | ~ v1_relat_1(k6_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1714,plain,
    ( r2_hidden(k4_tarski(sK7,sK7),k6_relat_1(sK8)) = iProver_top
    | r2_hidden(sK7,sK8) != iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1713])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2797,plain,
    ( v1_relat_1(k6_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2798,plain,
    ( v1_relat_1(k6_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2797])).

cnf(c_755,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X0,X3),k5_relat_1(X2,k6_relat_1(X4)))
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X4))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,k6_relat_1(X4)))
    | ~ v1_relat_1(k6_relat_1(X4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1134,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK9,k6_relat_1(X2)))
    | ~ r2_hidden(k4_tarski(X3,X1),k6_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X0,X3),sK9)
    | ~ v1_relat_1(k5_relat_1(sK9,k6_relat_1(X2)))
    | ~ v1_relat_1(k6_relat_1(X2))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_1730,plain,
    ( ~ r2_hidden(k4_tarski(sK7,X0),k6_relat_1(X1))
    | r2_hidden(k4_tarski(sK6,X0),k5_relat_1(sK9,k6_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
    | ~ v1_relat_1(k5_relat_1(sK9,k6_relat_1(X1)))
    | ~ v1_relat_1(k6_relat_1(X1))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_5092,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK7),k6_relat_1(sK8))
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8)))
    | ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
    | ~ v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)))
    | ~ v1_relat_1(k6_relat_1(sK8))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_5093,plain,
    ( r2_hidden(k4_tarski(sK7,sK7),k6_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5092])).

cnf(c_5836,plain,
    ( r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,k5_relat_1(sK9,k6_relat_1(sK8)))) = iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_609])).

cnf(c_6025,plain,
    ( r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,k5_relat_1(sK9,k6_relat_1(sK8)))) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5837,c_18,c_21,c_1714,c_2798,c_5093,c_5836])).

cnf(c_6026,plain,
    ( r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,k5_relat_1(sK9,k6_relat_1(sK8)))) = iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6025])).

cnf(c_6035,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X2,k5_relat_1(X3,k5_relat_1(sK9,k6_relat_1(sK8))))) = iProver_top
    | r2_hidden(k4_tarski(X1,sK6),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X3,k5_relat_1(sK9,k6_relat_1(sK8)))) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6026,c_609])).

cnf(c_6206,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X2,k5_relat_1(X3,k5_relat_1(sK9,k6_relat_1(sK8))))) = iProver_top
    | r2_hidden(k4_tarski(X1,sK6),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6035,c_502])).

cnf(c_6221,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),X0) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X0,k5_relat_1(sK9,k6_relat_1(sK8))))) = iProver_top
    | r2_hidden(sK7,sK8) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_6206])).

cnf(c_6220,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),X0) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X0,k5_relat_1(sK9,k6_relat_1(sK8))))) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_6206])).

cnf(c_6532,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X0,k5_relat_1(sK9,k6_relat_1(sK8))))) = iProver_top
    | r2_hidden(k4_tarski(sK7,sK6),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6221,c_18,c_21,c_1714,c_2798,c_5093,c_6220])).

cnf(c_6533,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),X0) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X0,k5_relat_1(sK9,k6_relat_1(sK8))))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6532])).

cnf(c_6543,plain,
    ( r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X2,k5_relat_1(sK9,k6_relat_1(sK8)))))) = iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK6),X2) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X2,k5_relat_1(sK9,k6_relat_1(sK8))))) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6533,c_609])).

cnf(c_6663,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X2,k5_relat_1(X3,k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X4,k5_relat_1(sK9,k6_relat_1(sK8))))))) = iProver_top
    | r2_hidden(k4_tarski(X1,sK6),X3) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK6),X4) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X4) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X3,k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X4,k5_relat_1(sK9,k6_relat_1(sK8)))))) != iProver_top
    | v1_relat_1(k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X4,k5_relat_1(sK9,k6_relat_1(sK8))))) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6543,c_609])).

cnf(c_8317,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X2,k5_relat_1(X3,k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X4,k5_relat_1(sK9,k6_relat_1(sK8))))))) = iProver_top
    | r2_hidden(k4_tarski(X1,sK6),X3) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK6),X4) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X4) != iProver_top
    | v1_relat_1(k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X4,k5_relat_1(sK9,k6_relat_1(sK8))))) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6663,c_502])).

cnf(c_8330,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),X0) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK6),X1) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X0,k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X1,k5_relat_1(sK9,k6_relat_1(sK8))))))) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(k5_relat_1(sK9,k6_relat_1(sK8)),k5_relat_1(X1,k5_relat_1(sK9,k6_relat_1(sK8))))) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_8317])).

cnf(c_20,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_504,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_598,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_504,c_502])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | ~ v1_relat_1(k6_relat_1(X2))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_510,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) != iProver_top
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_501,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_536,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X0),k6_relat_1(X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_510,c_501])).

cnf(c_2076,plain,
    ( sK5(X0,k6_relat_1(X1),X2,X3) = X3
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_536])).

cnf(c_2132,plain,
    ( sK5(X0,k6_relat_1(X1),X2,X3) = X3
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2076,c_501])).

cnf(c_2142,plain,
    ( sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_2132])).

cnf(c_4209,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
    | sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2142,c_18])).

cnf(c_4210,plain,
    ( sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_4209])).

cnf(c_6219,plain,
    ( sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7
    | r2_hidden(k4_tarski(sK7,sK6),X0) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k5_relat_1(X0,k5_relat_1(sK9,k6_relat_1(sK8))))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4210,c_6206])).

cnf(c_2143,plain,
    ( sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7
    | r2_hidden(sK7,sK8) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_2132])).

cnf(c_2820,plain,
    ( r2_hidden(sK7,sK8) = iProver_top
    | sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2143,c_18])).

cnf(c_2821,plain,
    ( sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7
    | r2_hidden(sK7,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_2820])).

cnf(c_7783,plain,
    ( v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6219,c_18,c_21,c_1714,c_2798,c_2821,c_4210,c_5093])).

cnf(c_7784,plain,
    ( sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7783])).

cnf(c_7789,plain,
    ( sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_502,c_7784])).

cnf(c_7792,plain,
    ( sK5(sK9,k6_relat_1(sK8),sK6,sK7) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7789,c_18,c_2798])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_503,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_588,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_503,c_502])).

cnf(c_7801,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_7792,c_588])).

cnf(c_8843,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8330,c_18,c_20,c_2798,c_7801])).

cnf(c_8849,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),X0) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(sK9,k5_relat_1(X0,k5_relat_1(sK9,k6_relat_1(sK8))))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_8843,c_6206])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_509,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_542,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_509,c_501])).

cnf(c_2075,plain,
    ( r2_hidden(sK5(X0,k6_relat_1(X1),X2,X3),X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_542])).

cnf(c_5104,plain,
    ( r2_hidden(sK5(X0,k6_relat_1(X1),X2,X3),X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2075,c_501])).

cnf(c_5117,plain,
    ( r2_hidden(sK5(sK9,k6_relat_1(sK8),sK6,sK7),sK8) = iProver_top
    | r2_hidden(sK7,sK8) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_5104])).

cnf(c_5253,plain,
    ( r2_hidden(sK7,sK8) = iProver_top
    | r2_hidden(sK5(sK9,k6_relat_1(sK8),sK6,sK7),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5117,c_18])).

cnf(c_5254,plain,
    ( r2_hidden(sK5(sK9,k6_relat_1(sK8),sK6,sK7),sK8) = iProver_top
    | r2_hidden(sK7,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_5253])).

cnf(c_7796,plain,
    ( r2_hidden(sK7,sK8) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7792,c_5254])).

cnf(c_10096,plain,
    ( v1_relat_1(k5_relat_1(sK9,k6_relat_1(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8849,c_18,c_20,c_21,c_1714,c_2798,c_5093,c_7796,c_7801])).

cnf(c_10101,plain,
    ( v1_relat_1(k6_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_502,c_10096])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10101,c_2798,c_18])).


%------------------------------------------------------------------------------
