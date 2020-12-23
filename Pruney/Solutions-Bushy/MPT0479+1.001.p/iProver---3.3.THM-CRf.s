%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0479+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:24 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
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
