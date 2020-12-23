%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:34 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 940 expanded)
%              Number of clauses        :   58 ( 303 expanded)
%              Number of leaves         :   10 ( 191 expanded)
%              Depth                    :   29
%              Number of atoms          :  470 (5251 expanded)
%              Number of equality atoms :  175 (1117 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
        <=> ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <~> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      & v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
      & v1_relat_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) )
        & v1_relat_1(X3) )
   => ( ( ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
        | ~ r2_hidden(sK6,sK8)
        | ~ r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) )
      & ( ( r2_hidden(k4_tarski(sK6,sK7),sK9)
          & r2_hidden(sK6,sK8) )
        | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
      | ~ r2_hidden(sK6,sK8)
      | ~ r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) )
    & ( ( r2_hidden(k4_tarski(sK6,sK7),sK9)
        & r2_hidden(sK6,sK8) )
      | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f24,f25])).

fof(f43,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),sK9)
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) ),
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

fof(f3,axiom,(
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

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f44,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
    | ~ r2_hidden(sK6,sK8)
    | ~ r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,
    ( r2_hidden(sK6,sK8)
    | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) ),
    inference(cnf_transformation,[],[f26])).

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

cnf(c_15,negated_conjecture,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))
    | r2_hidden(k4_tarski(sK6,sK7),sK9) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_499,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

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

cnf(c_588,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_503,c_502])).

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

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_501,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_536,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X0),k6_relat_1(X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_510,c_501])).

cnf(c_1635,plain,
    ( sK5(k6_relat_1(X0),X1,X2,X3) = X2
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_536])).

cnf(c_22,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1998,plain,
    ( v1_relat_1(X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | sK5(k6_relat_1(X0),X1,X2,X3) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1635,c_22])).

cnf(c_1999,plain,
    ( sK5(k6_relat_1(X0),X1,X2,X3) = X2
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1998])).

cnf(c_2012,plain,
    ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_1999])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2093,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
    | sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2012,c_18])).

cnf(c_2094,plain,
    ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_2093])).

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

cnf(c_5584,plain,
    ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6
    | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2094,c_609])).

cnf(c_6024,plain,
    ( v1_relat_1(X1) != iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top
    | sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5584,c_18])).

cnf(c_6025,plain,
    ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6
    | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6024])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))
    | ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
    | ~ r2_hidden(sK6,sK8) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_500,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6035,plain,
    ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6
    | r2_hidden(k4_tarski(sK6,sK7),sK9) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK6),k6_relat_1(sK8)) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6025,c_500])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))
    | r2_hidden(sK6,sK8) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_498,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) = iProver_top
    | r2_hidden(sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

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

cnf(c_1634,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3)) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_542])).

cnf(c_1754,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3)) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1634,c_501])).

cnf(c_1764,plain,
    ( r2_hidden(sK6,sK8) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_1754])).

cnf(c_1842,plain,
    ( r2_hidden(sK6,sK8)
    | ~ v1_relat_1(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1764])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1926,plain,
    ( r2_hidden(k4_tarski(sK6,sK6),k6_relat_1(sK8))
    | ~ r2_hidden(sK6,sK8)
    | ~ v1_relat_1(k6_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2095,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),sK9)
    | sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2094])).

cnf(c_2652,plain,
    ( v1_relat_1(k6_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6080,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
    | ~ r2_hidden(k4_tarski(sK6,sK6),k6_relat_1(sK8))
    | ~ r2_hidden(sK6,sK8)
    | ~ v1_relat_1(k6_relat_1(sK8))
    | sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6035])).

cnf(c_6259,plain,
    ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6035,c_17,c_1842,c_1926,c_2095,c_2652,c_6080])).

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

cnf(c_6262,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6259,c_598])).

cnf(c_20,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2653,plain,
    ( v1_relat_1(k6_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2652])).

cnf(c_6319,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6262,c_18,c_20,c_2653])).

cnf(c_6324,plain,
    ( r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6319,c_609])).

cnf(c_6426,plain,
    ( v1_relat_1(X1) != iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6324,c_18])).

cnf(c_6427,plain,
    ( r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top
    | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6426])).

cnf(c_6436,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),sK9) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK6),k6_relat_1(sK8)) != iProver_top
    | r2_hidden(sK6,sK8) != iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6427,c_500])).

cnf(c_1927,plain,
    ( r2_hidden(k4_tarski(sK6,sK6),k6_relat_1(sK8)) = iProver_top
    | r2_hidden(sK6,sK8) != iProver_top
    | v1_relat_1(k6_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1926])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6436,c_6319,c_2653,c_1927,c_1764,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.26/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/0.99  
% 3.26/0.99  ------  iProver source info
% 3.26/0.99  
% 3.26/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.26/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/0.99  git: non_committed_changes: false
% 3.26/0.99  git: last_make_outside_of_git: false
% 3.26/0.99  
% 3.26/0.99  ------ 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options
% 3.26/0.99  
% 3.26/0.99  --out_options                           all
% 3.26/0.99  --tptp_safe_out                         true
% 3.26/0.99  --problem_path                          ""
% 3.26/0.99  --include_path                          ""
% 3.26/0.99  --clausifier                            res/vclausify_rel
% 3.26/0.99  --clausifier_options                    --mode clausify
% 3.26/0.99  --stdin                                 false
% 3.26/0.99  --stats_out                             all
% 3.26/0.99  
% 3.26/0.99  ------ General Options
% 3.26/0.99  
% 3.26/0.99  --fof                                   false
% 3.26/0.99  --time_out_real                         305.
% 3.26/0.99  --time_out_virtual                      -1.
% 3.26/0.99  --symbol_type_check                     false
% 3.26/0.99  --clausify_out                          false
% 3.26/0.99  --sig_cnt_out                           false
% 3.26/0.99  --trig_cnt_out                          false
% 3.26/0.99  --trig_cnt_out_tolerance                1.
% 3.26/0.99  --trig_cnt_out_sk_spl                   false
% 3.26/0.99  --abstr_cl_out                          false
% 3.26/0.99  
% 3.26/0.99  ------ Global Options
% 3.26/0.99  
% 3.26/0.99  --schedule                              default
% 3.26/0.99  --add_important_lit                     false
% 3.26/0.99  --prop_solver_per_cl                    1000
% 3.26/0.99  --min_unsat_core                        false
% 3.26/0.99  --soft_assumptions                      false
% 3.26/0.99  --soft_lemma_size                       3
% 3.26/0.99  --prop_impl_unit_size                   0
% 3.26/0.99  --prop_impl_unit                        []
% 3.26/0.99  --share_sel_clauses                     true
% 3.26/0.99  --reset_solvers                         false
% 3.26/0.99  --bc_imp_inh                            [conj_cone]
% 3.26/0.99  --conj_cone_tolerance                   3.
% 3.26/0.99  --extra_neg_conj                        none
% 3.26/0.99  --large_theory_mode                     true
% 3.26/0.99  --prolific_symb_bound                   200
% 3.26/0.99  --lt_threshold                          2000
% 3.26/0.99  --clause_weak_htbl                      true
% 3.26/0.99  --gc_record_bc_elim                     false
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing Options
% 3.26/0.99  
% 3.26/0.99  --preprocessing_flag                    true
% 3.26/0.99  --time_out_prep_mult                    0.1
% 3.26/0.99  --splitting_mode                        input
% 3.26/0.99  --splitting_grd                         true
% 3.26/0.99  --splitting_cvd                         false
% 3.26/0.99  --splitting_cvd_svl                     false
% 3.26/0.99  --splitting_nvd                         32
% 3.26/0.99  --sub_typing                            true
% 3.26/0.99  --prep_gs_sim                           true
% 3.26/0.99  --prep_unflatten                        true
% 3.26/0.99  --prep_res_sim                          true
% 3.26/0.99  --prep_upred                            true
% 3.26/0.99  --prep_sem_filter                       exhaustive
% 3.26/0.99  --prep_sem_filter_out                   false
% 3.26/0.99  --pred_elim                             true
% 3.26/0.99  --res_sim_input                         true
% 3.26/0.99  --eq_ax_congr_red                       true
% 3.26/0.99  --pure_diseq_elim                       true
% 3.26/0.99  --brand_transform                       false
% 3.26/0.99  --non_eq_to_eq                          false
% 3.26/0.99  --prep_def_merge                        true
% 3.26/0.99  --prep_def_merge_prop_impl              false
% 3.26/0.99  --prep_def_merge_mbd                    true
% 3.26/0.99  --prep_def_merge_tr_red                 false
% 3.26/0.99  --prep_def_merge_tr_cl                  false
% 3.26/0.99  --smt_preprocessing                     true
% 3.26/0.99  --smt_ac_axioms                         fast
% 3.26/0.99  --preprocessed_out                      false
% 3.26/0.99  --preprocessed_stats                    false
% 3.26/0.99  
% 3.26/0.99  ------ Abstraction refinement Options
% 3.26/0.99  
% 3.26/0.99  --abstr_ref                             []
% 3.26/0.99  --abstr_ref_prep                        false
% 3.26/0.99  --abstr_ref_until_sat                   false
% 3.26/0.99  --abstr_ref_sig_restrict                funpre
% 3.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.99  --abstr_ref_under                       []
% 3.26/0.99  
% 3.26/0.99  ------ SAT Options
% 3.26/0.99  
% 3.26/0.99  --sat_mode                              false
% 3.26/0.99  --sat_fm_restart_options                ""
% 3.26/0.99  --sat_gr_def                            false
% 3.26/0.99  --sat_epr_types                         true
% 3.26/0.99  --sat_non_cyclic_types                  false
% 3.26/0.99  --sat_finite_models                     false
% 3.26/0.99  --sat_fm_lemmas                         false
% 3.26/0.99  --sat_fm_prep                           false
% 3.26/0.99  --sat_fm_uc_incr                        true
% 3.26/0.99  --sat_out_model                         small
% 3.26/0.99  --sat_out_clauses                       false
% 3.26/0.99  
% 3.26/0.99  ------ QBF Options
% 3.26/0.99  
% 3.26/0.99  --qbf_mode                              false
% 3.26/0.99  --qbf_elim_univ                         false
% 3.26/0.99  --qbf_dom_inst                          none
% 3.26/0.99  --qbf_dom_pre_inst                      false
% 3.26/0.99  --qbf_sk_in                             false
% 3.26/0.99  --qbf_pred_elim                         true
% 3.26/0.99  --qbf_split                             512
% 3.26/0.99  
% 3.26/0.99  ------ BMC1 Options
% 3.26/0.99  
% 3.26/0.99  --bmc1_incremental                      false
% 3.26/0.99  --bmc1_axioms                           reachable_all
% 3.26/0.99  --bmc1_min_bound                        0
% 3.26/0.99  --bmc1_max_bound                        -1
% 3.26/0.99  --bmc1_max_bound_default                -1
% 3.26/0.99  --bmc1_symbol_reachability              true
% 3.26/0.99  --bmc1_property_lemmas                  false
% 3.26/0.99  --bmc1_k_induction                      false
% 3.26/0.99  --bmc1_non_equiv_states                 false
% 3.26/0.99  --bmc1_deadlock                         false
% 3.26/0.99  --bmc1_ucm                              false
% 3.26/0.99  --bmc1_add_unsat_core                   none
% 3.26/0.99  --bmc1_unsat_core_children              false
% 3.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.99  --bmc1_out_stat                         full
% 3.26/0.99  --bmc1_ground_init                      false
% 3.26/0.99  --bmc1_pre_inst_next_state              false
% 3.26/0.99  --bmc1_pre_inst_state                   false
% 3.26/0.99  --bmc1_pre_inst_reach_state             false
% 3.26/0.99  --bmc1_out_unsat_core                   false
% 3.26/0.99  --bmc1_aig_witness_out                  false
% 3.26/0.99  --bmc1_verbose                          false
% 3.26/0.99  --bmc1_dump_clauses_tptp                false
% 3.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.99  --bmc1_dump_file                        -
% 3.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.99  --bmc1_ucm_extend_mode                  1
% 3.26/0.99  --bmc1_ucm_init_mode                    2
% 3.26/0.99  --bmc1_ucm_cone_mode                    none
% 3.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.99  --bmc1_ucm_relax_model                  4
% 3.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.99  --bmc1_ucm_layered_model                none
% 3.26/0.99  --bmc1_ucm_max_lemma_size               10
% 3.26/0.99  
% 3.26/0.99  ------ AIG Options
% 3.26/0.99  
% 3.26/0.99  --aig_mode                              false
% 3.26/0.99  
% 3.26/0.99  ------ Instantiation Options
% 3.26/0.99  
% 3.26/0.99  --instantiation_flag                    true
% 3.26/0.99  --inst_sos_flag                         false
% 3.26/0.99  --inst_sos_phase                        true
% 3.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel_side                     num_symb
% 3.26/0.99  --inst_solver_per_active                1400
% 3.26/0.99  --inst_solver_calls_frac                1.
% 3.26/0.99  --inst_passive_queue_type               priority_queues
% 3.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.99  --inst_passive_queues_freq              [25;2]
% 3.26/0.99  --inst_dismatching                      true
% 3.26/0.99  --inst_eager_unprocessed_to_passive     true
% 3.26/0.99  --inst_prop_sim_given                   true
% 3.26/0.99  --inst_prop_sim_new                     false
% 3.26/0.99  --inst_subs_new                         false
% 3.26/0.99  --inst_eq_res_simp                      false
% 3.26/0.99  --inst_subs_given                       false
% 3.26/0.99  --inst_orphan_elimination               true
% 3.26/0.99  --inst_learning_loop_flag               true
% 3.26/0.99  --inst_learning_start                   3000
% 3.26/0.99  --inst_learning_factor                  2
% 3.26/0.99  --inst_start_prop_sim_after_learn       3
% 3.26/0.99  --inst_sel_renew                        solver
% 3.26/0.99  --inst_lit_activity_flag                true
% 3.26/0.99  --inst_restr_to_given                   false
% 3.26/0.99  --inst_activity_threshold               500
% 3.26/0.99  --inst_out_proof                        true
% 3.26/0.99  
% 3.26/0.99  ------ Resolution Options
% 3.26/0.99  
% 3.26/0.99  --resolution_flag                       true
% 3.26/0.99  --res_lit_sel                           adaptive
% 3.26/0.99  --res_lit_sel_side                      none
% 3.26/0.99  --res_ordering                          kbo
% 3.26/0.99  --res_to_prop_solver                    active
% 3.26/0.99  --res_prop_simpl_new                    false
% 3.26/0.99  --res_prop_simpl_given                  true
% 3.26/0.99  --res_passive_queue_type                priority_queues
% 3.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.99  --res_passive_queues_freq               [15;5]
% 3.26/0.99  --res_forward_subs                      full
% 3.26/0.99  --res_backward_subs                     full
% 3.26/0.99  --res_forward_subs_resolution           true
% 3.26/0.99  --res_backward_subs_resolution          true
% 3.26/0.99  --res_orphan_elimination                true
% 3.26/0.99  --res_time_limit                        2.
% 3.26/0.99  --res_out_proof                         true
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Options
% 3.26/0.99  
% 3.26/0.99  --superposition_flag                    true
% 3.26/0.99  --sup_passive_queue_type                priority_queues
% 3.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.99  --demod_completeness_check              fast
% 3.26/0.99  --demod_use_ground                      true
% 3.26/0.99  --sup_to_prop_solver                    passive
% 3.26/0.99  --sup_prop_simpl_new                    true
% 3.26/0.99  --sup_prop_simpl_given                  true
% 3.26/0.99  --sup_fun_splitting                     false
% 3.26/0.99  --sup_smt_interval                      50000
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Simplification Setup
% 3.26/0.99  
% 3.26/0.99  --sup_indices_passive                   []
% 3.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_full_bw                           [BwDemod]
% 3.26/0.99  --sup_immed_triv                        [TrivRules]
% 3.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_immed_bw_main                     []
% 3.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  
% 3.26/0.99  ------ Combination Options
% 3.26/0.99  
% 3.26/0.99  --comb_res_mult                         3
% 3.26/0.99  --comb_sup_mult                         2
% 3.26/0.99  --comb_inst_mult                        10
% 3.26/0.99  
% 3.26/0.99  ------ Debug Options
% 3.26/0.99  
% 3.26/0.99  --dbg_backtrace                         false
% 3.26/0.99  --dbg_dump_prop_clauses                 false
% 3.26/0.99  --dbg_dump_prop_clauses_file            -
% 3.26/0.99  --dbg_out_stat                          false
% 3.26/0.99  ------ Parsing...
% 3.26/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/0.99  ------ Proving...
% 3.26/0.99  ------ Problem Properties 
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  clauses                                 18
% 3.26/0.99  conjectures                             4
% 3.26/0.99  EPR                                     1
% 3.26/0.99  Horn                                    12
% 3.26/0.99  unary                                   2
% 3.26/0.99  binary                                  2
% 3.26/0.99  lits                                    69
% 3.26/0.99  lits eq                                 9
% 3.26/0.99  fd_pure                                 0
% 3.26/0.99  fd_pseudo                               0
% 3.26/0.99  fd_cond                                 0
% 3.26/0.99  fd_pseudo_cond                          7
% 3.26/0.99  AC symbols                              0
% 3.26/0.99  
% 3.26/0.99  ------ Schedule dynamic 5 is on 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  ------ 
% 3.26/0.99  Current options:
% 3.26/0.99  ------ 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options
% 3.26/0.99  
% 3.26/0.99  --out_options                           all
% 3.26/0.99  --tptp_safe_out                         true
% 3.26/0.99  --problem_path                          ""
% 3.26/0.99  --include_path                          ""
% 3.26/0.99  --clausifier                            res/vclausify_rel
% 3.26/0.99  --clausifier_options                    --mode clausify
% 3.26/0.99  --stdin                                 false
% 3.26/0.99  --stats_out                             all
% 3.26/0.99  
% 3.26/0.99  ------ General Options
% 3.26/0.99  
% 3.26/0.99  --fof                                   false
% 3.26/0.99  --time_out_real                         305.
% 3.26/0.99  --time_out_virtual                      -1.
% 3.26/0.99  --symbol_type_check                     false
% 3.26/0.99  --clausify_out                          false
% 3.26/0.99  --sig_cnt_out                           false
% 3.26/0.99  --trig_cnt_out                          false
% 3.26/0.99  --trig_cnt_out_tolerance                1.
% 3.26/0.99  --trig_cnt_out_sk_spl                   false
% 3.26/0.99  --abstr_cl_out                          false
% 3.26/0.99  
% 3.26/0.99  ------ Global Options
% 3.26/0.99  
% 3.26/0.99  --schedule                              default
% 3.26/0.99  --add_important_lit                     false
% 3.26/0.99  --prop_solver_per_cl                    1000
% 3.26/0.99  --min_unsat_core                        false
% 3.26/0.99  --soft_assumptions                      false
% 3.26/0.99  --soft_lemma_size                       3
% 3.26/0.99  --prop_impl_unit_size                   0
% 3.26/0.99  --prop_impl_unit                        []
% 3.26/0.99  --share_sel_clauses                     true
% 3.26/0.99  --reset_solvers                         false
% 3.26/0.99  --bc_imp_inh                            [conj_cone]
% 3.26/0.99  --conj_cone_tolerance                   3.
% 3.26/0.99  --extra_neg_conj                        none
% 3.26/0.99  --large_theory_mode                     true
% 3.26/0.99  --prolific_symb_bound                   200
% 3.26/0.99  --lt_threshold                          2000
% 3.26/0.99  --clause_weak_htbl                      true
% 3.26/0.99  --gc_record_bc_elim                     false
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing Options
% 3.26/0.99  
% 3.26/0.99  --preprocessing_flag                    true
% 3.26/0.99  --time_out_prep_mult                    0.1
% 3.26/0.99  --splitting_mode                        input
% 3.26/0.99  --splitting_grd                         true
% 3.26/0.99  --splitting_cvd                         false
% 3.26/0.99  --splitting_cvd_svl                     false
% 3.26/0.99  --splitting_nvd                         32
% 3.26/0.99  --sub_typing                            true
% 3.26/0.99  --prep_gs_sim                           true
% 3.26/0.99  --prep_unflatten                        true
% 3.26/0.99  --prep_res_sim                          true
% 3.26/0.99  --prep_upred                            true
% 3.26/0.99  --prep_sem_filter                       exhaustive
% 3.26/0.99  --prep_sem_filter_out                   false
% 3.26/0.99  --pred_elim                             true
% 3.26/0.99  --res_sim_input                         true
% 3.26/0.99  --eq_ax_congr_red                       true
% 3.26/0.99  --pure_diseq_elim                       true
% 3.26/0.99  --brand_transform                       false
% 3.26/0.99  --non_eq_to_eq                          false
% 3.26/0.99  --prep_def_merge                        true
% 3.26/0.99  --prep_def_merge_prop_impl              false
% 3.26/0.99  --prep_def_merge_mbd                    true
% 3.26/0.99  --prep_def_merge_tr_red                 false
% 3.26/0.99  --prep_def_merge_tr_cl                  false
% 3.26/0.99  --smt_preprocessing                     true
% 3.26/0.99  --smt_ac_axioms                         fast
% 3.26/0.99  --preprocessed_out                      false
% 3.26/0.99  --preprocessed_stats                    false
% 3.26/0.99  
% 3.26/0.99  ------ Abstraction refinement Options
% 3.26/0.99  
% 3.26/0.99  --abstr_ref                             []
% 3.26/0.99  --abstr_ref_prep                        false
% 3.26/0.99  --abstr_ref_until_sat                   false
% 3.26/0.99  --abstr_ref_sig_restrict                funpre
% 3.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.99  --abstr_ref_under                       []
% 3.26/0.99  
% 3.26/0.99  ------ SAT Options
% 3.26/0.99  
% 3.26/0.99  --sat_mode                              false
% 3.26/0.99  --sat_fm_restart_options                ""
% 3.26/0.99  --sat_gr_def                            false
% 3.26/0.99  --sat_epr_types                         true
% 3.26/0.99  --sat_non_cyclic_types                  false
% 3.26/0.99  --sat_finite_models                     false
% 3.26/0.99  --sat_fm_lemmas                         false
% 3.26/0.99  --sat_fm_prep                           false
% 3.26/0.99  --sat_fm_uc_incr                        true
% 3.26/0.99  --sat_out_model                         small
% 3.26/0.99  --sat_out_clauses                       false
% 3.26/0.99  
% 3.26/0.99  ------ QBF Options
% 3.26/0.99  
% 3.26/0.99  --qbf_mode                              false
% 3.26/0.99  --qbf_elim_univ                         false
% 3.26/0.99  --qbf_dom_inst                          none
% 3.26/0.99  --qbf_dom_pre_inst                      false
% 3.26/0.99  --qbf_sk_in                             false
% 3.26/0.99  --qbf_pred_elim                         true
% 3.26/0.99  --qbf_split                             512
% 3.26/0.99  
% 3.26/0.99  ------ BMC1 Options
% 3.26/0.99  
% 3.26/0.99  --bmc1_incremental                      false
% 3.26/0.99  --bmc1_axioms                           reachable_all
% 3.26/0.99  --bmc1_min_bound                        0
% 3.26/0.99  --bmc1_max_bound                        -1
% 3.26/0.99  --bmc1_max_bound_default                -1
% 3.26/0.99  --bmc1_symbol_reachability              true
% 3.26/0.99  --bmc1_property_lemmas                  false
% 3.26/0.99  --bmc1_k_induction                      false
% 3.26/0.99  --bmc1_non_equiv_states                 false
% 3.26/0.99  --bmc1_deadlock                         false
% 3.26/0.99  --bmc1_ucm                              false
% 3.26/0.99  --bmc1_add_unsat_core                   none
% 3.26/0.99  --bmc1_unsat_core_children              false
% 3.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.99  --bmc1_out_stat                         full
% 3.26/0.99  --bmc1_ground_init                      false
% 3.26/0.99  --bmc1_pre_inst_next_state              false
% 3.26/0.99  --bmc1_pre_inst_state                   false
% 3.26/0.99  --bmc1_pre_inst_reach_state             false
% 3.26/0.99  --bmc1_out_unsat_core                   false
% 3.26/0.99  --bmc1_aig_witness_out                  false
% 3.26/0.99  --bmc1_verbose                          false
% 3.26/0.99  --bmc1_dump_clauses_tptp                false
% 3.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.99  --bmc1_dump_file                        -
% 3.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.99  --bmc1_ucm_extend_mode                  1
% 3.26/0.99  --bmc1_ucm_init_mode                    2
% 3.26/0.99  --bmc1_ucm_cone_mode                    none
% 3.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.99  --bmc1_ucm_relax_model                  4
% 3.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.99  --bmc1_ucm_layered_model                none
% 3.26/0.99  --bmc1_ucm_max_lemma_size               10
% 3.26/0.99  
% 3.26/0.99  ------ AIG Options
% 3.26/0.99  
% 3.26/0.99  --aig_mode                              false
% 3.26/0.99  
% 3.26/0.99  ------ Instantiation Options
% 3.26/0.99  
% 3.26/0.99  --instantiation_flag                    true
% 3.26/0.99  --inst_sos_flag                         false
% 3.26/0.99  --inst_sos_phase                        true
% 3.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel_side                     none
% 3.26/0.99  --inst_solver_per_active                1400
% 3.26/0.99  --inst_solver_calls_frac                1.
% 3.26/0.99  --inst_passive_queue_type               priority_queues
% 3.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.99  --inst_passive_queues_freq              [25;2]
% 3.26/0.99  --inst_dismatching                      true
% 3.26/0.99  --inst_eager_unprocessed_to_passive     true
% 3.26/0.99  --inst_prop_sim_given                   true
% 3.26/0.99  --inst_prop_sim_new                     false
% 3.26/0.99  --inst_subs_new                         false
% 3.26/0.99  --inst_eq_res_simp                      false
% 3.26/0.99  --inst_subs_given                       false
% 3.26/0.99  --inst_orphan_elimination               true
% 3.26/0.99  --inst_learning_loop_flag               true
% 3.26/0.99  --inst_learning_start                   3000
% 3.26/0.99  --inst_learning_factor                  2
% 3.26/0.99  --inst_start_prop_sim_after_learn       3
% 3.26/0.99  --inst_sel_renew                        solver
% 3.26/0.99  --inst_lit_activity_flag                true
% 3.26/0.99  --inst_restr_to_given                   false
% 3.26/0.99  --inst_activity_threshold               500
% 3.26/0.99  --inst_out_proof                        true
% 3.26/0.99  
% 3.26/0.99  ------ Resolution Options
% 3.26/0.99  
% 3.26/0.99  --resolution_flag                       false
% 3.26/0.99  --res_lit_sel                           adaptive
% 3.26/0.99  --res_lit_sel_side                      none
% 3.26/0.99  --res_ordering                          kbo
% 3.26/0.99  --res_to_prop_solver                    active
% 3.26/0.99  --res_prop_simpl_new                    false
% 3.26/0.99  --res_prop_simpl_given                  true
% 3.26/0.99  --res_passive_queue_type                priority_queues
% 3.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.99  --res_passive_queues_freq               [15;5]
% 3.26/0.99  --res_forward_subs                      full
% 3.26/0.99  --res_backward_subs                     full
% 3.26/0.99  --res_forward_subs_resolution           true
% 3.26/0.99  --res_backward_subs_resolution          true
% 3.26/0.99  --res_orphan_elimination                true
% 3.26/0.99  --res_time_limit                        2.
% 3.26/0.99  --res_out_proof                         true
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Options
% 3.26/0.99  
% 3.26/0.99  --superposition_flag                    true
% 3.26/0.99  --sup_passive_queue_type                priority_queues
% 3.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.99  --demod_completeness_check              fast
% 3.26/0.99  --demod_use_ground                      true
% 3.26/0.99  --sup_to_prop_solver                    passive
% 3.26/0.99  --sup_prop_simpl_new                    true
% 3.26/0.99  --sup_prop_simpl_given                  true
% 3.26/0.99  --sup_fun_splitting                     false
% 3.26/0.99  --sup_smt_interval                      50000
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Simplification Setup
% 3.26/0.99  
% 3.26/0.99  --sup_indices_passive                   []
% 3.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_full_bw                           [BwDemod]
% 3.26/0.99  --sup_immed_triv                        [TrivRules]
% 3.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_immed_bw_main                     []
% 3.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  
% 3.26/0.99  ------ Combination Options
% 3.26/0.99  
% 3.26/0.99  --comb_res_mult                         3
% 3.26/0.99  --comb_sup_mult                         2
% 3.26/0.99  --comb_inst_mult                        10
% 3.26/0.99  
% 3.26/0.99  ------ Debug Options
% 3.26/0.99  
% 3.26/0.99  --dbg_backtrace                         false
% 3.26/0.99  --dbg_dump_prop_clauses                 false
% 3.26/0.99  --dbg_dump_prop_clauses_file            -
% 3.26/0.99  --dbg_out_stat                          false
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  ------ Proving...
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  % SZS status Theorem for theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  fof(f5,conjecture,(
% 3.26/0.99    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f6,negated_conjecture,(
% 3.26/0.99    ~! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 3.26/0.99    inference(negated_conjecture,[],[f5])).
% 3.26/0.99  
% 3.26/0.99  fof(f11,plain,(
% 3.26/0.99    ? [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <~> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) & v1_relat_1(X3))),
% 3.26/0.99    inference(ennf_transformation,[],[f6])).
% 3.26/0.99  
% 3.26/0.99  fof(f23,plain,(
% 3.26/0.99    ? [X0,X1,X2,X3] : ((((~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) & v1_relat_1(X3))),
% 3.26/0.99    inference(nnf_transformation,[],[f11])).
% 3.26/0.99  
% 3.26/0.99  fof(f24,plain,(
% 3.26/0.99    ? [X0,X1,X2,X3] : ((~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) & v1_relat_1(X3))),
% 3.26/0.99    inference(flattening,[],[f23])).
% 3.26/0.99  
% 3.26/0.99  fof(f25,plain,(
% 3.26/0.99    ? [X0,X1,X2,X3] : ((~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) & v1_relat_1(X3)) => ((~r2_hidden(k4_tarski(sK6,sK7),sK9) | ~r2_hidden(sK6,sK8) | ~r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))) & ((r2_hidden(k4_tarski(sK6,sK7),sK9) & r2_hidden(sK6,sK8)) | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))) & v1_relat_1(sK9))),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f26,plain,(
% 3.26/0.99    (~r2_hidden(k4_tarski(sK6,sK7),sK9) | ~r2_hidden(sK6,sK8) | ~r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))) & ((r2_hidden(k4_tarski(sK6,sK7),sK9) & r2_hidden(sK6,sK8)) | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))) & v1_relat_1(sK9)),
% 3.26/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f24,f25])).
% 3.26/0.99  
% 3.26/0.99  fof(f43,plain,(
% 3.26/0.99    r2_hidden(k4_tarski(sK6,sK7),sK9) | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))),
% 3.26/0.99    inference(cnf_transformation,[],[f26])).
% 3.26/0.99  
% 3.26/0.99  fof(f2,axiom,(
% 3.26/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f8,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.26/0.99    inference(ennf_transformation,[],[f2])).
% 3.26/0.99  
% 3.26/0.99  fof(f17,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.26/0.99    inference(nnf_transformation,[],[f8])).
% 3.26/0.99  
% 3.26/0.99  fof(f18,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.26/0.99    inference(rectify,[],[f17])).
% 3.26/0.99  
% 3.26/0.99  fof(f21,plain,(
% 3.26/0.99    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f20,plain,(
% 3.26/0.99    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f19,plain,(
% 3.26/0.99    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f22,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.26/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f21,f20,f19])).
% 3.26/0.99  
% 3.26/0.99  fof(f33,plain,(
% 3.26/0.99    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f22])).
% 3.26/0.99  
% 3.26/0.99  fof(f51,plain,(
% 3.26/0.99    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.26/0.99    inference(equality_resolution,[],[f33])).
% 3.26/0.99  
% 3.26/0.99  fof(f3,axiom,(
% 3.26/0.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f9,plain,(
% 3.26/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.26/0.99    inference(ennf_transformation,[],[f3])).
% 3.26/0.99  
% 3.26/0.99  fof(f10,plain,(
% 3.26/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.26/0.99    inference(flattening,[],[f9])).
% 3.26/0.99  
% 3.26/0.99  fof(f39,plain,(
% 3.26/0.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f10])).
% 3.26/0.99  
% 3.26/0.99  fof(f1,axiom,(
% 3.26/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f7,plain,(
% 3.26/0.99    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 3.26/0.99    inference(ennf_transformation,[],[f1])).
% 3.26/0.99  
% 3.26/0.99  fof(f12,plain,(
% 3.26/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 3.26/0.99    inference(nnf_transformation,[],[f7])).
% 3.26/0.99  
% 3.26/0.99  fof(f13,plain,(
% 3.26/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 3.26/0.99    inference(flattening,[],[f12])).
% 3.26/0.99  
% 3.26/0.99  fof(f14,plain,(
% 3.26/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 3.26/0.99    inference(rectify,[],[f13])).
% 3.26/0.99  
% 3.26/0.99  fof(f15,plain,(
% 3.26/0.99    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1))))),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f16,plain,(
% 3.26/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 3.26/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 3.26/0.99  
% 3.26/0.99  fof(f28,plain,(
% 3.26/0.99    ( ! [X4,X0,X5,X1] : (X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),X1) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f16])).
% 3.26/0.99  
% 3.26/0.99  fof(f47,plain,(
% 3.26/0.99    ( ! [X4,X0,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.26/0.99    inference(equality_resolution,[],[f28])).
% 3.26/0.99  
% 3.26/0.99  fof(f4,axiom,(
% 3.26/0.99    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f40,plain,(
% 3.26/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.26/0.99    inference(cnf_transformation,[],[f4])).
% 3.26/0.99  
% 3.26/0.99  fof(f41,plain,(
% 3.26/0.99    v1_relat_1(sK9)),
% 3.26/0.99    inference(cnf_transformation,[],[f26])).
% 3.26/0.99  
% 3.26/0.99  fof(f35,plain,(
% 3.26/0.99    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f22])).
% 3.26/0.99  
% 3.26/0.99  fof(f49,plain,(
% 3.26/0.99    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.26/0.99    inference(equality_resolution,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f44,plain,(
% 3.26/0.99    ~r2_hidden(k4_tarski(sK6,sK7),sK9) | ~r2_hidden(sK6,sK8) | ~r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))),
% 3.26/0.99    inference(cnf_transformation,[],[f26])).
% 3.26/0.99  
% 3.26/0.99  fof(f42,plain,(
% 3.26/0.99    r2_hidden(sK6,sK8) | r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))),
% 3.26/0.99    inference(cnf_transformation,[],[f26])).
% 3.26/0.99  
% 3.26/0.99  fof(f27,plain,(
% 3.26/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f16])).
% 3.26/0.99  
% 3.26/0.99  fof(f48,plain,(
% 3.26/0.99    ( ! [X4,X0,X5] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.26/0.99    inference(equality_resolution,[],[f27])).
% 3.26/0.99  
% 3.26/0.99  fof(f29,plain,(
% 3.26/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f16])).
% 3.26/0.99  
% 3.26/0.99  fof(f45,plain,(
% 3.26/0.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,X5),X1) | ~r2_hidden(X5,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.26/0.99    inference(equality_resolution,[],[f29])).
% 3.26/0.99  
% 3.26/0.99  fof(f46,plain,(
% 3.26/0.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) | ~r2_hidden(X5,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.26/0.99    inference(equality_resolution,[],[f45])).
% 3.26/0.99  
% 3.26/0.99  fof(f34,plain,(
% 3.26/0.99    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f22])).
% 3.26/0.99  
% 3.26/0.99  fof(f50,plain,(
% 3.26/0.99    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.26/0.99    inference(equality_resolution,[],[f34])).
% 3.26/0.99  
% 3.26/0.99  cnf(c_15,negated_conjecture,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))
% 3.26/0.99      | r2_hidden(k4_tarski(sK6,sK7),sK9) ),
% 3.26/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_499,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) = iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_11,plain,
% 3.26/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
% 3.26/0.99      | ~ v1_relat_1(X3)
% 3.26/0.99      | ~ v1_relat_1(X2)
% 3.26/0.99      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 3.26/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_503,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2) = iProver_top
% 3.26/0.99      | v1_relat_1(X3) != iProver_top
% 3.26/0.99      | v1_relat_1(X2) != iProver_top
% 3.26/0.99      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_12,plain,
% 3.26/0.99      ( ~ v1_relat_1(X0)
% 3.26/0.99      | ~ v1_relat_1(X1)
% 3.26/0.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.26/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_502,plain,
% 3.26/0.99      ( v1_relat_1(X0) != iProver_top
% 3.26/0.99      | v1_relat_1(X1) != iProver_top
% 3.26/0.99      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_588,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2) = iProver_top
% 3.26/0.99      | v1_relat_1(X3) != iProver_top
% 3.26/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.26/0.99      inference(forward_subsumption_resolution,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_503,c_502]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4,plain,
% 3.26/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
% 3.26/0.99      | ~ v1_relat_1(k6_relat_1(X2))
% 3.26/0.99      | X0 = X1 ),
% 3.26/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_510,plain,
% 3.26/0.99      ( X0 = X1
% 3.26/0.99      | r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) != iProver_top
% 3.26/0.99      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_13,plain,
% 3.26/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.26/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_501,plain,
% 3.26/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_536,plain,
% 3.26/0.99      ( X0 = X1
% 3.26/0.99      | r2_hidden(k4_tarski(X1,X0),k6_relat_1(X2)) != iProver_top ),
% 3.26/0.99      inference(forward_subsumption_resolution,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_510,c_501]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1635,plain,
% 3.26/0.99      ( sK5(k6_relat_1(X0),X1,X2,X3) = X2
% 3.26/0.99      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 3.26/0.99      | v1_relat_1(X1) != iProver_top
% 3.26/0.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_588,c_536]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_22,plain,
% 3.26/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1998,plain,
% 3.26/0.99      ( v1_relat_1(X1) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 3.26/0.99      | sK5(k6_relat_1(X0),X1,X2,X3) = X2 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_1635,c_22]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1999,plain,
% 3.26/0.99      ( sK5(k6_relat_1(X0),X1,X2,X3) = X2
% 3.26/0.99      | r2_hidden(k4_tarski(X2,X3),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 3.26/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_1998]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2012,plain,
% 3.26/0.99      ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6
% 3.26/0.99      | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
% 3.26/0.99      | v1_relat_1(sK9) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_499,c_1999]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_17,negated_conjecture,
% 3.26/0.99      ( v1_relat_1(sK9) ),
% 3.26/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_18,plain,
% 3.26/0.99      ( v1_relat_1(sK9) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2093,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
% 3.26/0.99      | sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_2012,c_18]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2094,plain,
% 3.26/0.99      ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6
% 3.26/0.99      | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_2093]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_9,plain,
% 3.26/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.26/0.99      | ~ r2_hidden(k4_tarski(X3,X0),X4)
% 3.26/0.99      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
% 3.26/0.99      | ~ v1_relat_1(X2)
% 3.26/0.99      | ~ v1_relat_1(X4)
% 3.26/0.99      | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
% 3.26/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_505,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
% 3.26/0.99      | v1_relat_1(X2) != iProver_top
% 3.26/0.99      | v1_relat_1(X4) != iProver_top
% 3.26/0.99      | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_609,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
% 3.26/0.99      | v1_relat_1(X2) != iProver_top
% 3.26/0.99      | v1_relat_1(X4) != iProver_top ),
% 3.26/0.99      inference(forward_subsumption_resolution,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_505,c_502]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_5584,plain,
% 3.26/0.99      ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
% 3.26/0.99      | v1_relat_1(X1) != iProver_top
% 3.26/0.99      | v1_relat_1(sK9) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_2094,c_609]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6024,plain,
% 3.26/0.99      ( v1_relat_1(X1) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top
% 3.26/0.99      | sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_5584,c_18]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6025,plain,
% 3.26/0.99      ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
% 3.26/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_6024]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_14,negated_conjecture,
% 3.26/0.99      ( ~ r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))
% 3.26/0.99      | ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
% 3.26/0.99      | ~ r2_hidden(sK6,sK8) ),
% 3.26/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_500,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(sK6,sK7),sK9) != iProver_top
% 3.26/0.99      | r2_hidden(sK6,sK8) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6035,plain,
% 3.26/0.99      ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6
% 3.26/0.99      | r2_hidden(k4_tarski(sK6,sK7),sK9) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(sK6,sK6),k6_relat_1(sK8)) != iProver_top
% 3.26/0.99      | r2_hidden(sK6,sK8) != iProver_top
% 3.26/0.99      | v1_relat_1(k6_relat_1(sK8)) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_6025,c_500]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_16,negated_conjecture,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9))
% 3.26/0.99      | r2_hidden(sK6,sK8) ),
% 3.26/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_498,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) = iProver_top
% 3.26/0.99      | r2_hidden(sK6,sK8) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_5,plain,
% 3.26/0.99      ( r2_hidden(X0,X1)
% 3.26/0.99      | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
% 3.26/0.99      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 3.26/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_509,plain,
% 3.26/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top
% 3.26/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_542,plain,
% 3.26/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
% 3.26/0.99      inference(forward_subsumption_resolution,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_509,c_501]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1634,plain,
% 3.26/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3)) != iProver_top
% 3.26/0.99      | v1_relat_1(X3) != iProver_top
% 3.26/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_588,c_542]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1754,plain,
% 3.26/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3)) != iProver_top
% 3.26/0.99      | v1_relat_1(X3) != iProver_top ),
% 3.26/0.99      inference(forward_subsumption_resolution,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_1634,c_501]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1764,plain,
% 3.26/0.99      ( r2_hidden(sK6,sK8) = iProver_top
% 3.26/0.99      | v1_relat_1(sK9) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_498,c_1754]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1842,plain,
% 3.26/0.99      ( r2_hidden(sK6,sK8) | ~ v1_relat_1(sK9) ),
% 3.26/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1764]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3,plain,
% 3.26/0.99      ( ~ r2_hidden(X0,X1)
% 3.26/0.99      | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
% 3.26/0.99      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 3.26/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1926,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK6),k6_relat_1(sK8))
% 3.26/0.99      | ~ r2_hidden(sK6,sK8)
% 3.26/0.99      | ~ v1_relat_1(k6_relat_1(sK8)) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2095,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),sK9)
% 3.26/0.99      | sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6 ),
% 3.26/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2094]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2652,plain,
% 3.26/0.99      ( v1_relat_1(k6_relat_1(sK8)) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6080,plain,
% 3.26/0.99      ( ~ r2_hidden(k4_tarski(sK6,sK7),sK9)
% 3.26/0.99      | ~ r2_hidden(k4_tarski(sK6,sK6),k6_relat_1(sK8))
% 3.26/0.99      | ~ r2_hidden(sK6,sK8)
% 3.26/0.99      | ~ v1_relat_1(k6_relat_1(sK8))
% 3.26/0.99      | sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6 ),
% 3.26/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6035]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6259,plain,
% 3.26/0.99      ( sK5(k6_relat_1(sK8),sK9,sK6,sK7) = sK6 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_6035,c_17,c_1842,c_1926,c_2095,c_2652,c_6080]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_10,plain,
% 3.26/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 3.26/0.99      | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
% 3.26/0.99      | ~ v1_relat_1(X3)
% 3.26/0.99      | ~ v1_relat_1(X2)
% 3.26/0.99      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 3.26/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_504,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3) = iProver_top
% 3.26/0.99      | v1_relat_1(X3) != iProver_top
% 3.26/0.99      | v1_relat_1(X2) != iProver_top
% 3.26/0.99      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_598,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3) = iProver_top
% 3.26/0.99      | v1_relat_1(X3) != iProver_top
% 3.26/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.26/0.99      inference(forward_subsumption_resolution,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_504,c_502]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6262,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top
% 3.26/0.99      | v1_relat_1(k6_relat_1(sK8)) != iProver_top
% 3.26/0.99      | v1_relat_1(sK9) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_6259,c_598]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_20,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),k5_relat_1(k6_relat_1(sK8),sK9)) = iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2653,plain,
% 3.26/0.99      ( v1_relat_1(k6_relat_1(sK8)) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_2652]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6319,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),sK9) = iProver_top ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_6262,c_18,c_20,c_2653]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6324,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
% 3.26/0.99      | v1_relat_1(X1) != iProver_top
% 3.26/0.99      | v1_relat_1(sK9) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_6319,c_609]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6426,plain,
% 3.26/0.99      ( v1_relat_1(X1) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_6324,c_18]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6427,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(X0,sK7),k5_relat_1(X1,sK9)) = iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(X0,sK6),X1) != iProver_top
% 3.26/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_6426]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6436,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK7),sK9) != iProver_top
% 3.26/0.99      | r2_hidden(k4_tarski(sK6,sK6),k6_relat_1(sK8)) != iProver_top
% 3.26/0.99      | r2_hidden(sK6,sK8) != iProver_top
% 3.26/0.99      | v1_relat_1(k6_relat_1(sK8)) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_6427,c_500]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1927,plain,
% 3.26/0.99      ( r2_hidden(k4_tarski(sK6,sK6),k6_relat_1(sK8)) = iProver_top
% 3.26/0.99      | r2_hidden(sK6,sK8) != iProver_top
% 3.26/0.99      | v1_relat_1(k6_relat_1(sK8)) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1926]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(contradiction,plain,
% 3.26/0.99      ( $false ),
% 3.26/0.99      inference(minisat,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_6436,c_6319,c_2653,c_1927,c_1764,c_18]) ).
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  ------                               Statistics
% 3.26/0.99  
% 3.26/0.99  ------ General
% 3.26/0.99  
% 3.26/0.99  abstr_ref_over_cycles:                  0
% 3.26/0.99  abstr_ref_under_cycles:                 0
% 3.26/0.99  gc_basic_clause_elim:                   0
% 3.26/0.99  forced_gc_time:                         0
% 3.26/0.99  parsing_time:                           0.01
% 3.26/0.99  unif_index_cands_time:                  0.
% 3.26/0.99  unif_index_add_time:                    0.
% 3.26/0.99  orderings_time:                         0.
% 3.26/0.99  out_proof_time:                         0.012
% 3.26/0.99  total_time:                             0.323
% 3.26/0.99  num_of_symbols:                         46
% 3.26/0.99  num_of_terms:                           15161
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing
% 3.26/0.99  
% 3.26/0.99  num_of_splits:                          0
% 3.26/0.99  num_of_split_atoms:                     0
% 3.26/0.99  num_of_reused_defs:                     0
% 3.26/0.99  num_eq_ax_congr_red:                    34
% 3.26/0.99  num_of_sem_filtered_clauses:            1
% 3.26/0.99  num_of_subtypes:                        0
% 3.26/0.99  monotx_restored_types:                  0
% 3.26/0.99  sat_num_of_epr_types:                   0
% 3.26/0.99  sat_num_of_non_cyclic_types:            0
% 3.26/0.99  sat_guarded_non_collapsed_types:        0
% 3.26/0.99  num_pure_diseq_elim:                    0
% 3.26/0.99  simp_replaced_by:                       0
% 3.26/0.99  res_preprocessed:                       69
% 3.26/0.99  prep_upred:                             0
% 3.26/0.99  prep_unflattend:                        0
% 3.26/0.99  smt_new_axioms:                         0
% 3.26/0.99  pred_elim_cands:                        2
% 3.26/0.99  pred_elim:                              0
% 3.26/0.99  pred_elim_cl:                           0
% 3.26/0.99  pred_elim_cycles:                       1
% 3.26/0.99  merged_defs:                            0
% 3.26/0.99  merged_defs_ncl:                        0
% 3.26/0.99  bin_hyper_res:                          0
% 3.26/0.99  prep_cycles:                            3
% 3.26/0.99  pred_elim_time:                         0.
% 3.26/0.99  splitting_time:                         0.
% 3.26/0.99  sem_filter_time:                        0.
% 3.26/0.99  monotx_time:                            0.001
% 3.26/0.99  subtype_inf_time:                       0.
% 3.26/0.99  
% 3.26/0.99  ------ Problem properties
% 3.26/0.99  
% 3.26/0.99  clauses:                                18
% 3.26/0.99  conjectures:                            4
% 3.26/0.99  epr:                                    1
% 3.26/0.99  horn:                                   12
% 3.26/0.99  ground:                                 4
% 3.26/0.99  unary:                                  2
% 3.26/0.99  binary:                                 2
% 3.26/0.99  lits:                                   69
% 3.26/0.99  lits_eq:                                9
% 3.26/0.99  fd_pure:                                0
% 3.26/0.99  fd_pseudo:                              0
% 3.26/0.99  fd_cond:                                0
% 3.26/0.99  fd_pseudo_cond:                         7
% 3.26/0.99  ac_symbols:                             0
% 3.26/0.99  
% 3.26/0.99  ------ Propositional Solver
% 3.26/0.99  
% 3.26/0.99  prop_solver_calls:                      23
% 3.26/0.99  prop_fast_solver_calls:                 691
% 3.26/0.99  smt_solver_calls:                       0
% 3.26/0.99  smt_fast_solver_calls:                  0
% 3.26/0.99  prop_num_of_clauses:                    3096
% 3.26/0.99  prop_preprocess_simplified:             6556
% 3.26/0.99  prop_fo_subsumed:                       29
% 3.26/0.99  prop_solver_time:                       0.
% 3.26/0.99  smt_solver_time:                        0.
% 3.26/0.99  smt_fast_solver_time:                   0.
% 3.26/0.99  prop_fast_solver_time:                  0.
% 3.26/0.99  prop_unsat_core_time:                   0.
% 3.26/0.99  
% 3.26/0.99  ------ QBF
% 3.26/0.99  
% 3.26/0.99  qbf_q_res:                              0
% 3.26/0.99  qbf_num_tautologies:                    0
% 3.26/0.99  qbf_prep_cycles:                        0
% 3.26/0.99  
% 3.26/0.99  ------ BMC1
% 3.26/0.99  
% 3.26/0.99  bmc1_current_bound:                     -1
% 3.26/0.99  bmc1_last_solved_bound:                 -1
% 3.26/0.99  bmc1_unsat_core_size:                   -1
% 3.26/0.99  bmc1_unsat_core_parents_size:           -1
% 3.26/0.99  bmc1_merge_next_fun:                    0
% 3.26/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.26/0.99  
% 3.26/0.99  ------ Instantiation
% 3.26/0.99  
% 3.26/0.99  inst_num_of_clauses:                    717
% 3.26/0.99  inst_num_in_passive:                    489
% 3.26/0.99  inst_num_in_active:                     128
% 3.26/0.99  inst_num_in_unprocessed:                100
% 3.26/0.99  inst_num_of_loops:                      190
% 3.26/0.99  inst_num_of_learning_restarts:          0
% 3.26/0.99  inst_num_moves_active_passive:          60
% 3.26/0.99  inst_lit_activity:                      0
% 3.26/0.99  inst_lit_activity_moves:                1
% 3.26/0.99  inst_num_tautologies:                   0
% 3.26/0.99  inst_num_prop_implied:                  0
% 3.26/0.99  inst_num_existing_simplified:           0
% 3.26/0.99  inst_num_eq_res_simplified:             0
% 3.26/0.99  inst_num_child_elim:                    0
% 3.26/0.99  inst_num_of_dismatching_blockings:      208
% 3.26/0.99  inst_num_of_non_proper_insts:           331
% 3.26/0.99  inst_num_of_duplicates:                 0
% 3.26/0.99  inst_inst_num_from_inst_to_res:         0
% 3.26/0.99  inst_dismatching_checking_time:         0.
% 3.26/0.99  
% 3.26/0.99  ------ Resolution
% 3.26/0.99  
% 3.26/0.99  res_num_of_clauses:                     0
% 3.26/0.99  res_num_in_passive:                     0
% 3.26/0.99  res_num_in_active:                      0
% 3.26/0.99  res_num_of_loops:                       72
% 3.26/0.99  res_forward_subset_subsumed:            9
% 3.26/0.99  res_backward_subset_subsumed:           0
% 3.26/0.99  res_forward_subsumed:                   0
% 3.26/0.99  res_backward_subsumed:                  0
% 3.26/0.99  res_forward_subsumption_resolution:     0
% 3.26/0.99  res_backward_subsumption_resolution:    0
% 3.26/0.99  res_clause_to_clause_subsumption:       269
% 3.26/0.99  res_orphan_elimination:                 0
% 3.26/0.99  res_tautology_del:                      7
% 3.26/0.99  res_num_eq_res_simplified:              0
% 3.26/0.99  res_num_sel_changes:                    0
% 3.26/0.99  res_moves_from_active_to_pass:          0
% 3.26/0.99  
% 3.26/0.99  ------ Superposition
% 3.26/0.99  
% 3.26/0.99  sup_time_total:                         0.
% 3.26/0.99  sup_time_generating:                    0.
% 3.26/0.99  sup_time_sim_full:                      0.
% 3.26/0.99  sup_time_sim_immed:                     0.
% 3.26/0.99  
% 3.26/0.99  sup_num_of_clauses:                     102
% 3.26/0.99  sup_num_in_active:                      36
% 3.26/0.99  sup_num_in_passive:                     66
% 3.26/0.99  sup_num_of_loops:                       37
% 3.26/0.99  sup_fw_superposition:                   54
% 3.26/0.99  sup_bw_superposition:                   53
% 3.26/0.99  sup_immediate_simplified:               7
% 3.26/0.99  sup_given_eliminated:                   0
% 3.26/0.99  comparisons_done:                       0
% 3.26/0.99  comparisons_avoided:                    6
% 3.26/0.99  
% 3.26/0.99  ------ Simplifications
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  sim_fw_subset_subsumed:                 5
% 3.26/0.99  sim_bw_subset_subsumed:                 5
% 3.26/0.99  sim_fw_subsumed:                        3
% 3.26/0.99  sim_bw_subsumed:                        0
% 3.26/0.99  sim_fw_subsumption_res:                 11
% 3.26/0.99  sim_bw_subsumption_res:                 0
% 3.26/0.99  sim_tautology_del:                      7
% 3.26/0.99  sim_eq_tautology_del:                   3
% 3.26/0.99  sim_eq_res_simp:                        0
% 3.26/0.99  sim_fw_demodulated:                     0
% 3.26/0.99  sim_bw_demodulated:                     0
% 3.26/0.99  sim_light_normalised:                   0
% 3.26/0.99  sim_joinable_taut:                      0
% 3.26/0.99  sim_joinable_simp:                      0
% 3.26/0.99  sim_ac_normalised:                      0
% 3.26/0.99  sim_smt_subsumption:                    0
% 3.26/0.99  
%------------------------------------------------------------------------------
