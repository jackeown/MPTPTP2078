%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:35 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 131 expanded)
%              Number of clauses        :   39 (  39 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  469 ( 766 expanded)
%              Number of equality atoms :  109 ( 147 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK7(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f31,f34,f33,f32])).

fof(f53,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f43,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f66,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k1_relat_1(X1),X0)
         => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( k5_relat_1(k6_relat_1(X0),X1) != X1
        & r1_tarski(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k5_relat_1(k6_relat_1(sK9),sK10) != sK10
      & r1_tarski(k1_relat_1(sK10),sK9)
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k5_relat_1(k6_relat_1(sK9),sK10) != sK10
    & r1_tarski(k1_relat_1(sK10),sK9)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f18,f38])).

fof(f63,plain,(
    r1_tarski(k1_relat_1(sK10),sK9) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    ! [X2,X0,X5,X1] :
      ( k5_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).

fof(f48,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    k5_relat_1(k6_relat_1(sK9),sK10) != sK10 ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6319,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),k5_relat_1(k6_relat_1(sK9),sK10))
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_6320,plain,
    ( r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),k5_relat_1(k6_relat_1(sK9),sK10)) != iProver_top
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) = iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6319])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2770,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK9),sK10))
    | ~ v1_relat_1(k6_relat_1(sK9))
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2771,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK9),sK10)) = iProver_top
    | v1_relat_1(k6_relat_1(sK9)) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2770])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1105,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK7(k6_relat_1(sK9),sK10,sK10)),X1)
    | r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK9),sK10,sK10)),k5_relat_1(X1,sK10))
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,sK10))
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1797,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
    | ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK7(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9))
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),k5_relat_1(k6_relat_1(sK9),sK10))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK9),sK10))
    | ~ v1_relat_1(k6_relat_1(sK9))
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_1105])).

cnf(c_1798,plain,
    ( r2_hidden(k4_tarski(sK7(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) != iProver_top
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK7(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),k5_relat_1(k6_relat_1(sK9),sK10)) = iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK9),sK10)) != iProver_top
    | v1_relat_1(k6_relat_1(sK9)) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1797])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1661,plain,
    ( ~ r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),sK9)
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK5(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9))
    | ~ v1_relat_1(k6_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1662,plain,
    ( r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),sK9) != iProver_top
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK5(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9)) = iProver_top
    | v1_relat_1(k6_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1661])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k1_relat_1(sK10),sK9) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_271,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_relat_1(sK10) != X1
    | sK9 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_272,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK10))
    | r2_hidden(X0,sK9) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_1375,plain,
    ( ~ r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),k1_relat_1(sK10))
    | r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),sK9) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_1376,plain,
    ( r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),k1_relat_1(sK10)) != iProver_top
    | r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK6(X1,X2,X3)),X2)
    | ~ r2_hidden(k4_tarski(sK5(X1,X2,X3),X0),X1)
    | ~ r2_hidden(k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X2) = X3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1084,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
    | ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),X0),k6_relat_1(sK9))
    | ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
    | ~ v1_relat_1(k6_relat_1(sK9))
    | ~ v1_relat_1(sK10)
    | k5_relat_1(k6_relat_1(sK9),sK10) = sK10 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1332,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK5(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9))
    | ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
    | ~ v1_relat_1(k6_relat_1(sK9))
    | ~ v1_relat_1(sK10)
    | k5_relat_1(k6_relat_1(sK9),sK10) = sK10 ),
    inference(instantiation,[status(thm)],[c_1084])).

cnf(c_1333,plain,
    ( k5_relat_1(k6_relat_1(sK9),sK10) = sK10
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK5(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) != iProver_top
    | v1_relat_1(k6_relat_1(sK9)) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1332])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1155,plain,
    ( v1_relat_1(k6_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1156,plain,
    ( v1_relat_1(k6_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1123,plain,
    ( r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),k1_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1124,plain,
    ( r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),k1_relat_1(sK10)) = iProver_top
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_13,plain,
    ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1081,plain,
    ( r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK7(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9))
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
    | ~ v1_relat_1(k6_relat_1(sK9))
    | ~ v1_relat_1(sK10)
    | k5_relat_1(k6_relat_1(sK9),sK10) = sK10 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1082,plain,
    ( k5_relat_1(k6_relat_1(sK9),sK10) = sK10
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK7(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9)) = iProver_top
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) = iProver_top
    | v1_relat_1(k6_relat_1(sK9)) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_12,plain,
    ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1072,plain,
    ( r2_hidden(k4_tarski(sK7(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
    | ~ v1_relat_1(k6_relat_1(sK9))
    | ~ v1_relat_1(sK10)
    | k5_relat_1(k6_relat_1(sK9),sK10) = sK10 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1073,plain,
    ( k5_relat_1(k6_relat_1(sK9),sK10) = sK10
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) = iProver_top
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) = iProver_top
    | v1_relat_1(k6_relat_1(sK9)) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1072])).

cnf(c_22,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK9),sK10) != sK10 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6320,c_2771,c_1798,c_1662,c_1376,c_1333,c_1156,c_1124,c_1082,c_1073,c_22,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:55:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.17/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/0.93  
% 3.17/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.17/0.93  
% 3.17/0.93  ------  iProver source info
% 3.17/0.93  
% 3.17/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.17/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.17/0.93  git: non_committed_changes: false
% 3.17/0.93  git: last_make_outside_of_git: false
% 3.17/0.93  
% 3.17/0.93  ------ 
% 3.17/0.93  
% 3.17/0.93  ------ Input Options
% 3.17/0.93  
% 3.17/0.93  --out_options                           all
% 3.17/0.93  --tptp_safe_out                         true
% 3.17/0.93  --problem_path                          ""
% 3.17/0.93  --include_path                          ""
% 3.17/0.93  --clausifier                            res/vclausify_rel
% 3.17/0.93  --clausifier_options                    --mode clausify
% 3.17/0.93  --stdin                                 false
% 3.17/0.93  --stats_out                             all
% 3.17/0.93  
% 3.17/0.93  ------ General Options
% 3.17/0.93  
% 3.17/0.93  --fof                                   false
% 3.17/0.93  --time_out_real                         305.
% 3.17/0.93  --time_out_virtual                      -1.
% 3.17/0.93  --symbol_type_check                     false
% 3.17/0.93  --clausify_out                          false
% 3.17/0.93  --sig_cnt_out                           false
% 3.17/0.93  --trig_cnt_out                          false
% 3.17/0.93  --trig_cnt_out_tolerance                1.
% 3.17/0.93  --trig_cnt_out_sk_spl                   false
% 3.17/0.93  --abstr_cl_out                          false
% 3.17/0.93  
% 3.17/0.93  ------ Global Options
% 3.17/0.93  
% 3.17/0.93  --schedule                              default
% 3.17/0.93  --add_important_lit                     false
% 3.17/0.93  --prop_solver_per_cl                    1000
% 3.17/0.93  --min_unsat_core                        false
% 3.17/0.93  --soft_assumptions                      false
% 3.17/0.93  --soft_lemma_size                       3
% 3.17/0.93  --prop_impl_unit_size                   0
% 3.17/0.93  --prop_impl_unit                        []
% 3.17/0.93  --share_sel_clauses                     true
% 3.17/0.93  --reset_solvers                         false
% 3.17/0.93  --bc_imp_inh                            [conj_cone]
% 3.17/0.93  --conj_cone_tolerance                   3.
% 3.17/0.93  --extra_neg_conj                        none
% 3.17/0.93  --large_theory_mode                     true
% 3.17/0.93  --prolific_symb_bound                   200
% 3.17/0.93  --lt_threshold                          2000
% 3.17/0.93  --clause_weak_htbl                      true
% 3.17/0.93  --gc_record_bc_elim                     false
% 3.17/0.93  
% 3.17/0.93  ------ Preprocessing Options
% 3.17/0.93  
% 3.17/0.93  --preprocessing_flag                    true
% 3.17/0.93  --time_out_prep_mult                    0.1
% 3.17/0.93  --splitting_mode                        input
% 3.17/0.93  --splitting_grd                         true
% 3.17/0.93  --splitting_cvd                         false
% 3.17/0.93  --splitting_cvd_svl                     false
% 3.17/0.93  --splitting_nvd                         32
% 3.17/0.93  --sub_typing                            true
% 3.17/0.93  --prep_gs_sim                           true
% 3.17/0.93  --prep_unflatten                        true
% 3.17/0.93  --prep_res_sim                          true
% 3.17/0.93  --prep_upred                            true
% 3.17/0.93  --prep_sem_filter                       exhaustive
% 3.17/0.93  --prep_sem_filter_out                   false
% 3.17/0.93  --pred_elim                             true
% 3.17/0.93  --res_sim_input                         true
% 3.17/0.93  --eq_ax_congr_red                       true
% 3.17/0.93  --pure_diseq_elim                       true
% 3.17/0.93  --brand_transform                       false
% 3.17/0.93  --non_eq_to_eq                          false
% 3.17/0.93  --prep_def_merge                        true
% 3.17/0.93  --prep_def_merge_prop_impl              false
% 3.17/0.93  --prep_def_merge_mbd                    true
% 3.17/0.93  --prep_def_merge_tr_red                 false
% 3.17/0.93  --prep_def_merge_tr_cl                  false
% 3.17/0.93  --smt_preprocessing                     true
% 3.17/0.93  --smt_ac_axioms                         fast
% 3.17/0.93  --preprocessed_out                      false
% 3.17/0.93  --preprocessed_stats                    false
% 3.17/0.93  
% 3.17/0.93  ------ Abstraction refinement Options
% 3.17/0.93  
% 3.17/0.93  --abstr_ref                             []
% 3.17/0.93  --abstr_ref_prep                        false
% 3.17/0.93  --abstr_ref_until_sat                   false
% 3.17/0.93  --abstr_ref_sig_restrict                funpre
% 3.17/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/0.93  --abstr_ref_under                       []
% 3.17/0.93  
% 3.17/0.93  ------ SAT Options
% 3.17/0.93  
% 3.17/0.93  --sat_mode                              false
% 3.17/0.93  --sat_fm_restart_options                ""
% 3.17/0.93  --sat_gr_def                            false
% 3.17/0.93  --sat_epr_types                         true
% 3.17/0.93  --sat_non_cyclic_types                  false
% 3.17/0.93  --sat_finite_models                     false
% 3.17/0.93  --sat_fm_lemmas                         false
% 3.17/0.93  --sat_fm_prep                           false
% 3.17/0.93  --sat_fm_uc_incr                        true
% 3.17/0.93  --sat_out_model                         small
% 3.17/0.93  --sat_out_clauses                       false
% 3.17/0.93  
% 3.17/0.93  ------ QBF Options
% 3.17/0.93  
% 3.17/0.93  --qbf_mode                              false
% 3.17/0.93  --qbf_elim_univ                         false
% 3.17/0.93  --qbf_dom_inst                          none
% 3.17/0.93  --qbf_dom_pre_inst                      false
% 3.17/0.93  --qbf_sk_in                             false
% 3.17/0.93  --qbf_pred_elim                         true
% 3.17/0.93  --qbf_split                             512
% 3.17/0.93  
% 3.17/0.93  ------ BMC1 Options
% 3.17/0.93  
% 3.17/0.93  --bmc1_incremental                      false
% 3.17/0.93  --bmc1_axioms                           reachable_all
% 3.17/0.93  --bmc1_min_bound                        0
% 3.17/0.93  --bmc1_max_bound                        -1
% 3.17/0.93  --bmc1_max_bound_default                -1
% 3.17/0.93  --bmc1_symbol_reachability              true
% 3.17/0.93  --bmc1_property_lemmas                  false
% 3.17/0.93  --bmc1_k_induction                      false
% 3.17/0.93  --bmc1_non_equiv_states                 false
% 3.17/0.93  --bmc1_deadlock                         false
% 3.17/0.93  --bmc1_ucm                              false
% 3.17/0.93  --bmc1_add_unsat_core                   none
% 3.17/0.93  --bmc1_unsat_core_children              false
% 3.17/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/0.93  --bmc1_out_stat                         full
% 3.17/0.93  --bmc1_ground_init                      false
% 3.17/0.93  --bmc1_pre_inst_next_state              false
% 3.17/0.93  --bmc1_pre_inst_state                   false
% 3.17/0.93  --bmc1_pre_inst_reach_state             false
% 3.17/0.93  --bmc1_out_unsat_core                   false
% 3.17/0.93  --bmc1_aig_witness_out                  false
% 3.17/0.93  --bmc1_verbose                          false
% 3.17/0.93  --bmc1_dump_clauses_tptp                false
% 3.17/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.17/0.93  --bmc1_dump_file                        -
% 3.17/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.17/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.17/0.93  --bmc1_ucm_extend_mode                  1
% 3.17/0.93  --bmc1_ucm_init_mode                    2
% 3.17/0.93  --bmc1_ucm_cone_mode                    none
% 3.17/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.17/0.93  --bmc1_ucm_relax_model                  4
% 3.17/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.17/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/0.93  --bmc1_ucm_layered_model                none
% 3.17/0.93  --bmc1_ucm_max_lemma_size               10
% 3.17/0.93  
% 3.17/0.93  ------ AIG Options
% 3.17/0.93  
% 3.17/0.93  --aig_mode                              false
% 3.17/0.93  
% 3.17/0.93  ------ Instantiation Options
% 3.17/0.93  
% 3.17/0.93  --instantiation_flag                    true
% 3.17/0.93  --inst_sos_flag                         false
% 3.17/0.93  --inst_sos_phase                        true
% 3.17/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/0.93  --inst_lit_sel_side                     num_symb
% 3.17/0.93  --inst_solver_per_active                1400
% 3.17/0.93  --inst_solver_calls_frac                1.
% 3.17/0.93  --inst_passive_queue_type               priority_queues
% 3.17/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/0.93  --inst_passive_queues_freq              [25;2]
% 3.17/0.93  --inst_dismatching                      true
% 3.17/0.93  --inst_eager_unprocessed_to_passive     true
% 3.17/0.93  --inst_prop_sim_given                   true
% 3.17/0.93  --inst_prop_sim_new                     false
% 3.17/0.93  --inst_subs_new                         false
% 3.17/0.93  --inst_eq_res_simp                      false
% 3.17/0.93  --inst_subs_given                       false
% 3.17/0.93  --inst_orphan_elimination               true
% 3.17/0.93  --inst_learning_loop_flag               true
% 3.17/0.93  --inst_learning_start                   3000
% 3.17/0.93  --inst_learning_factor                  2
% 3.17/0.93  --inst_start_prop_sim_after_learn       3
% 3.17/0.93  --inst_sel_renew                        solver
% 3.17/0.93  --inst_lit_activity_flag                true
% 3.17/0.93  --inst_restr_to_given                   false
% 3.17/0.93  --inst_activity_threshold               500
% 3.17/0.93  --inst_out_proof                        true
% 3.17/0.93  
% 3.17/0.93  ------ Resolution Options
% 3.17/0.93  
% 3.17/0.93  --resolution_flag                       true
% 3.17/0.93  --res_lit_sel                           adaptive
% 3.17/0.93  --res_lit_sel_side                      none
% 3.17/0.93  --res_ordering                          kbo
% 3.17/0.93  --res_to_prop_solver                    active
% 3.17/0.93  --res_prop_simpl_new                    false
% 3.17/0.93  --res_prop_simpl_given                  true
% 3.17/0.93  --res_passive_queue_type                priority_queues
% 3.17/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/0.93  --res_passive_queues_freq               [15;5]
% 3.17/0.93  --res_forward_subs                      full
% 3.17/0.93  --res_backward_subs                     full
% 3.17/0.93  --res_forward_subs_resolution           true
% 3.17/0.93  --res_backward_subs_resolution          true
% 3.17/0.93  --res_orphan_elimination                true
% 3.17/0.93  --res_time_limit                        2.
% 3.17/0.93  --res_out_proof                         true
% 3.17/0.93  
% 3.17/0.93  ------ Superposition Options
% 3.17/0.93  
% 3.17/0.93  --superposition_flag                    true
% 3.17/0.93  --sup_passive_queue_type                priority_queues
% 3.17/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.17/0.93  --demod_completeness_check              fast
% 3.17/0.93  --demod_use_ground                      true
% 3.17/0.93  --sup_to_prop_solver                    passive
% 3.17/0.93  --sup_prop_simpl_new                    true
% 3.17/0.93  --sup_prop_simpl_given                  true
% 3.17/0.93  --sup_fun_splitting                     false
% 3.17/0.93  --sup_smt_interval                      50000
% 3.17/0.93  
% 3.17/0.93  ------ Superposition Simplification Setup
% 3.17/0.93  
% 3.17/0.93  --sup_indices_passive                   []
% 3.17/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.93  --sup_full_bw                           [BwDemod]
% 3.17/0.93  --sup_immed_triv                        [TrivRules]
% 3.17/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.93  --sup_immed_bw_main                     []
% 3.17/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.93  
% 3.17/0.93  ------ Combination Options
% 3.17/0.93  
% 3.17/0.93  --comb_res_mult                         3
% 3.17/0.93  --comb_sup_mult                         2
% 3.17/0.93  --comb_inst_mult                        10
% 3.17/0.93  
% 3.17/0.93  ------ Debug Options
% 3.17/0.93  
% 3.17/0.93  --dbg_backtrace                         false
% 3.17/0.93  --dbg_dump_prop_clauses                 false
% 3.17/0.93  --dbg_dump_prop_clauses_file            -
% 3.17/0.93  --dbg_out_stat                          false
% 3.17/0.93  ------ Parsing...
% 3.17/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.17/0.93  
% 3.17/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.17/0.93  
% 3.17/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.17/0.93  
% 3.17/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.17/0.93  ------ Proving...
% 3.17/0.93  ------ Problem Properties 
% 3.17/0.93  
% 3.17/0.93  
% 3.17/0.93  clauses                                 24
% 3.17/0.93  conjectures                             2
% 3.17/0.93  EPR                                     1
% 3.17/0.93  Horn                                    19
% 3.17/0.93  unary                                   3
% 3.17/0.93  binary                                  3
% 3.17/0.93  lits                                    85
% 3.17/0.93  lits eq                                 12
% 3.17/0.93  fd_pure                                 0
% 3.17/0.93  fd_pseudo                               0
% 3.17/0.93  fd_cond                                 0
% 3.17/0.93  fd_pseudo_cond                          9
% 3.17/0.93  AC symbols                              0
% 3.17/0.93  
% 3.17/0.93  ------ Schedule dynamic 5 is on 
% 3.17/0.93  
% 3.17/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.17/0.93  
% 3.17/0.93  
% 3.17/0.93  ------ 
% 3.17/0.93  Current options:
% 3.17/0.93  ------ 
% 3.17/0.93  
% 3.17/0.93  ------ Input Options
% 3.17/0.93  
% 3.17/0.93  --out_options                           all
% 3.17/0.93  --tptp_safe_out                         true
% 3.17/0.93  --problem_path                          ""
% 3.17/0.93  --include_path                          ""
% 3.17/0.93  --clausifier                            res/vclausify_rel
% 3.17/0.93  --clausifier_options                    --mode clausify
% 3.17/0.93  --stdin                                 false
% 3.17/0.93  --stats_out                             all
% 3.17/0.93  
% 3.17/0.93  ------ General Options
% 3.17/0.93  
% 3.17/0.93  --fof                                   false
% 3.17/0.93  --time_out_real                         305.
% 3.17/0.93  --time_out_virtual                      -1.
% 3.17/0.93  --symbol_type_check                     false
% 3.17/0.93  --clausify_out                          false
% 3.17/0.93  --sig_cnt_out                           false
% 3.17/0.93  --trig_cnt_out                          false
% 3.17/0.93  --trig_cnt_out_tolerance                1.
% 3.17/0.93  --trig_cnt_out_sk_spl                   false
% 3.17/0.93  --abstr_cl_out                          false
% 3.17/0.93  
% 3.17/0.93  ------ Global Options
% 3.17/0.93  
% 3.17/0.93  --schedule                              default
% 3.17/0.93  --add_important_lit                     false
% 3.17/0.93  --prop_solver_per_cl                    1000
% 3.17/0.93  --min_unsat_core                        false
% 3.17/0.93  --soft_assumptions                      false
% 3.17/0.93  --soft_lemma_size                       3
% 3.17/0.93  --prop_impl_unit_size                   0
% 3.17/0.93  --prop_impl_unit                        []
% 3.17/0.93  --share_sel_clauses                     true
% 3.17/0.93  --reset_solvers                         false
% 3.17/0.93  --bc_imp_inh                            [conj_cone]
% 3.17/0.93  --conj_cone_tolerance                   3.
% 3.17/0.93  --extra_neg_conj                        none
% 3.17/0.93  --large_theory_mode                     true
% 3.17/0.93  --prolific_symb_bound                   200
% 3.17/0.93  --lt_threshold                          2000
% 3.17/0.93  --clause_weak_htbl                      true
% 3.17/0.93  --gc_record_bc_elim                     false
% 3.17/0.93  
% 3.17/0.93  ------ Preprocessing Options
% 3.17/0.93  
% 3.17/0.93  --preprocessing_flag                    true
% 3.17/0.93  --time_out_prep_mult                    0.1
% 3.17/0.93  --splitting_mode                        input
% 3.17/0.93  --splitting_grd                         true
% 3.17/0.93  --splitting_cvd                         false
% 3.17/0.93  --splitting_cvd_svl                     false
% 3.17/0.93  --splitting_nvd                         32
% 3.17/0.93  --sub_typing                            true
% 3.17/0.93  --prep_gs_sim                           true
% 3.17/0.93  --prep_unflatten                        true
% 3.17/0.93  --prep_res_sim                          true
% 3.17/0.93  --prep_upred                            true
% 3.17/0.93  --prep_sem_filter                       exhaustive
% 3.17/0.93  --prep_sem_filter_out                   false
% 3.17/0.93  --pred_elim                             true
% 3.17/0.93  --res_sim_input                         true
% 3.17/0.93  --eq_ax_congr_red                       true
% 3.17/0.93  --pure_diseq_elim                       true
% 3.17/0.93  --brand_transform                       false
% 3.17/0.93  --non_eq_to_eq                          false
% 3.17/0.93  --prep_def_merge                        true
% 3.17/0.93  --prep_def_merge_prop_impl              false
% 3.17/0.93  --prep_def_merge_mbd                    true
% 3.17/0.93  --prep_def_merge_tr_red                 false
% 3.17/0.93  --prep_def_merge_tr_cl                  false
% 3.17/0.93  --smt_preprocessing                     true
% 3.17/0.93  --smt_ac_axioms                         fast
% 3.17/0.93  --preprocessed_out                      false
% 3.17/0.93  --preprocessed_stats                    false
% 3.17/0.93  
% 3.17/0.93  ------ Abstraction refinement Options
% 3.17/0.93  
% 3.17/0.93  --abstr_ref                             []
% 3.17/0.93  --abstr_ref_prep                        false
% 3.17/0.93  --abstr_ref_until_sat                   false
% 3.17/0.93  --abstr_ref_sig_restrict                funpre
% 3.17/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/0.93  --abstr_ref_under                       []
% 3.17/0.93  
% 3.17/0.93  ------ SAT Options
% 3.17/0.93  
% 3.17/0.93  --sat_mode                              false
% 3.17/0.93  --sat_fm_restart_options                ""
% 3.17/0.93  --sat_gr_def                            false
% 3.17/0.93  --sat_epr_types                         true
% 3.17/0.93  --sat_non_cyclic_types                  false
% 3.17/0.93  --sat_finite_models                     false
% 3.17/0.93  --sat_fm_lemmas                         false
% 3.17/0.93  --sat_fm_prep                           false
% 3.17/0.93  --sat_fm_uc_incr                        true
% 3.17/0.93  --sat_out_model                         small
% 3.17/0.93  --sat_out_clauses                       false
% 3.17/0.93  
% 3.17/0.93  ------ QBF Options
% 3.17/0.93  
% 3.17/0.93  --qbf_mode                              false
% 3.17/0.93  --qbf_elim_univ                         false
% 3.17/0.93  --qbf_dom_inst                          none
% 3.17/0.93  --qbf_dom_pre_inst                      false
% 3.17/0.93  --qbf_sk_in                             false
% 3.17/0.93  --qbf_pred_elim                         true
% 3.17/0.93  --qbf_split                             512
% 3.17/0.93  
% 3.17/0.93  ------ BMC1 Options
% 3.17/0.93  
% 3.17/0.93  --bmc1_incremental                      false
% 3.17/0.93  --bmc1_axioms                           reachable_all
% 3.17/0.93  --bmc1_min_bound                        0
% 3.17/0.93  --bmc1_max_bound                        -1
% 3.17/0.93  --bmc1_max_bound_default                -1
% 3.17/0.93  --bmc1_symbol_reachability              true
% 3.17/0.93  --bmc1_property_lemmas                  false
% 3.17/0.93  --bmc1_k_induction                      false
% 3.17/0.93  --bmc1_non_equiv_states                 false
% 3.17/0.93  --bmc1_deadlock                         false
% 3.17/0.93  --bmc1_ucm                              false
% 3.17/0.93  --bmc1_add_unsat_core                   none
% 3.17/0.93  --bmc1_unsat_core_children              false
% 3.17/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/0.93  --bmc1_out_stat                         full
% 3.17/0.93  --bmc1_ground_init                      false
% 3.17/0.93  --bmc1_pre_inst_next_state              false
% 3.17/0.93  --bmc1_pre_inst_state                   false
% 3.17/0.93  --bmc1_pre_inst_reach_state             false
% 3.17/0.93  --bmc1_out_unsat_core                   false
% 3.17/0.93  --bmc1_aig_witness_out                  false
% 3.17/0.93  --bmc1_verbose                          false
% 3.17/0.93  --bmc1_dump_clauses_tptp                false
% 3.17/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.17/0.93  --bmc1_dump_file                        -
% 3.17/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.17/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.17/0.93  --bmc1_ucm_extend_mode                  1
% 3.17/0.93  --bmc1_ucm_init_mode                    2
% 3.17/0.93  --bmc1_ucm_cone_mode                    none
% 3.17/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.17/0.93  --bmc1_ucm_relax_model                  4
% 3.17/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.17/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/0.93  --bmc1_ucm_layered_model                none
% 3.17/0.93  --bmc1_ucm_max_lemma_size               10
% 3.17/0.93  
% 3.17/0.93  ------ AIG Options
% 3.17/0.93  
% 3.17/0.93  --aig_mode                              false
% 3.17/0.93  
% 3.17/0.93  ------ Instantiation Options
% 3.17/0.93  
% 3.17/0.93  --instantiation_flag                    true
% 3.17/0.93  --inst_sos_flag                         false
% 3.17/0.93  --inst_sos_phase                        true
% 3.17/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/0.93  --inst_lit_sel_side                     none
% 3.17/0.93  --inst_solver_per_active                1400
% 3.17/0.93  --inst_solver_calls_frac                1.
% 3.17/0.93  --inst_passive_queue_type               priority_queues
% 3.17/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/0.93  --inst_passive_queues_freq              [25;2]
% 3.17/0.93  --inst_dismatching                      true
% 3.17/0.93  --inst_eager_unprocessed_to_passive     true
% 3.17/0.93  --inst_prop_sim_given                   true
% 3.17/0.93  --inst_prop_sim_new                     false
% 3.17/0.93  --inst_subs_new                         false
% 3.17/0.93  --inst_eq_res_simp                      false
% 3.17/0.93  --inst_subs_given                       false
% 3.17/0.93  --inst_orphan_elimination               true
% 3.17/0.93  --inst_learning_loop_flag               true
% 3.17/0.93  --inst_learning_start                   3000
% 3.17/0.93  --inst_learning_factor                  2
% 3.17/0.93  --inst_start_prop_sim_after_learn       3
% 3.17/0.93  --inst_sel_renew                        solver
% 3.17/0.93  --inst_lit_activity_flag                true
% 3.17/0.93  --inst_restr_to_given                   false
% 3.17/0.93  --inst_activity_threshold               500
% 3.17/0.93  --inst_out_proof                        true
% 3.17/0.93  
% 3.17/0.93  ------ Resolution Options
% 3.17/0.93  
% 3.17/0.93  --resolution_flag                       false
% 3.17/0.93  --res_lit_sel                           adaptive
% 3.17/0.93  --res_lit_sel_side                      none
% 3.17/0.93  --res_ordering                          kbo
% 3.17/0.93  --res_to_prop_solver                    active
% 3.17/0.93  --res_prop_simpl_new                    false
% 3.17/0.93  --res_prop_simpl_given                  true
% 3.17/0.93  --res_passive_queue_type                priority_queues
% 3.17/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/0.93  --res_passive_queues_freq               [15;5]
% 3.17/0.93  --res_forward_subs                      full
% 3.17/0.93  --res_backward_subs                     full
% 3.17/0.93  --res_forward_subs_resolution           true
% 3.17/0.93  --res_backward_subs_resolution          true
% 3.17/0.93  --res_orphan_elimination                true
% 3.17/0.93  --res_time_limit                        2.
% 3.17/0.93  --res_out_proof                         true
% 3.17/0.93  
% 3.17/0.93  ------ Superposition Options
% 3.17/0.93  
% 3.17/0.93  --superposition_flag                    true
% 3.17/0.93  --sup_passive_queue_type                priority_queues
% 3.17/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.17/0.93  --demod_completeness_check              fast
% 3.17/0.93  --demod_use_ground                      true
% 3.17/0.93  --sup_to_prop_solver                    passive
% 3.17/0.93  --sup_prop_simpl_new                    true
% 3.17/0.93  --sup_prop_simpl_given                  true
% 3.17/0.93  --sup_fun_splitting                     false
% 3.17/0.93  --sup_smt_interval                      50000
% 3.17/0.93  
% 3.17/0.93  ------ Superposition Simplification Setup
% 3.17/0.93  
% 3.17/0.93  --sup_indices_passive                   []
% 3.17/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.93  --sup_full_bw                           [BwDemod]
% 3.17/0.93  --sup_immed_triv                        [TrivRules]
% 3.17/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.93  --sup_immed_bw_main                     []
% 3.17/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.93  
% 3.17/0.93  ------ Combination Options
% 3.17/0.93  
% 3.17/0.93  --comb_res_mult                         3
% 3.17/0.93  --comb_sup_mult                         2
% 3.17/0.93  --comb_inst_mult                        10
% 3.17/0.93  
% 3.17/0.93  ------ Debug Options
% 3.17/0.93  
% 3.17/0.93  --dbg_backtrace                         false
% 3.17/0.93  --dbg_dump_prop_clauses                 false
% 3.17/0.93  --dbg_dump_prop_clauses_file            -
% 3.17/0.93  --dbg_out_stat                          false
% 3.17/0.93  
% 3.17/0.93  
% 3.17/0.93  
% 3.17/0.93  
% 3.17/0.93  ------ Proving...
% 3.17/0.93  
% 3.17/0.93  
% 3.17/0.93  % SZS status Theorem for theBenchmark.p
% 3.17/0.93  
% 3.17/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.17/0.93  
% 3.17/0.93  fof(f7,axiom,(
% 3.17/0.93    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 3.17/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.93  
% 3.17/0.93  fof(f16,plain,(
% 3.17/0.93    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 3.17/0.93    inference(ennf_transformation,[],[f7])).
% 3.17/0.93  
% 3.17/0.93  fof(f36,plain,(
% 3.17/0.93    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 3.17/0.93    inference(nnf_transformation,[],[f16])).
% 3.17/0.93  
% 3.17/0.93  fof(f37,plain,(
% 3.17/0.93    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 3.17/0.93    inference(flattening,[],[f36])).
% 3.17/0.93  
% 3.17/0.93  fof(f60,plain,(
% 3.17/0.93    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X3)) )),
% 3.17/0.93    inference(cnf_transformation,[],[f37])).
% 3.17/0.93  
% 3.17/0.93  fof(f5,axiom,(
% 3.17/0.93    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.17/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.93  
% 3.17/0.93  fof(f14,plain,(
% 3.17/0.93    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.17/0.93    inference(ennf_transformation,[],[f5])).
% 3.17/0.93  
% 3.17/0.93  fof(f15,plain,(
% 3.17/0.93    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.17/0.93    inference(flattening,[],[f14])).
% 3.17/0.93  
% 3.17/0.93  fof(f57,plain,(
% 3.17/0.93    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.17/0.93    inference(cnf_transformation,[],[f15])).
% 3.17/0.93  
% 3.17/0.93  fof(f4,axiom,(
% 3.17/0.93    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.17/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.93  
% 3.17/0.93  fof(f13,plain,(
% 3.17/0.93    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.17/0.93    inference(ennf_transformation,[],[f4])).
% 3.17/0.93  
% 3.17/0.93  fof(f30,plain,(
% 3.17/0.93    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.17/0.93    inference(nnf_transformation,[],[f13])).
% 3.17/0.93  
% 3.17/0.93  fof(f31,plain,(
% 3.17/0.93    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.17/0.93    inference(rectify,[],[f30])).
% 3.17/0.93  
% 3.17/0.93  fof(f34,plain,(
% 3.17/0.93    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X0)))),
% 3.17/0.93    introduced(choice_axiom,[])).
% 3.17/0.93  
% 3.17/0.93  fof(f33,plain,(
% 3.17/0.93    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK7(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK7(X0,X1,X2)),X0)))) )),
% 3.17/0.93    introduced(choice_axiom,[])).
% 3.17/0.93  
% 3.17/0.93  fof(f32,plain,(
% 3.17/0.93    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2))))),
% 3.17/0.93    introduced(choice_axiom,[])).
% 3.17/0.93  
% 3.17/0.93  fof(f35,plain,(
% 3.17/0.93    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.17/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f31,f34,f33,f32])).
% 3.17/0.93  
% 3.17/0.93  fof(f53,plain,(
% 3.17/0.93    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.17/0.93    inference(cnf_transformation,[],[f35])).
% 3.17/0.93  
% 3.17/0.93  fof(f71,plain,(
% 3.17/0.93    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.17/0.93    inference(equality_resolution,[],[f53])).
% 3.17/0.93  
% 3.17/0.93  fof(f2,axiom,(
% 3.17/0.93    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 3.17/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.93  
% 3.17/0.93  fof(f12,plain,(
% 3.17/0.93    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 3.17/0.93    inference(ennf_transformation,[],[f2])).
% 3.17/0.93  
% 3.17/0.93  fof(f19,plain,(
% 3.17/0.93    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 3.17/0.93    inference(nnf_transformation,[],[f12])).
% 3.17/0.93  
% 3.17/0.93  fof(f20,plain,(
% 3.17/0.93    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 3.17/0.93    inference(flattening,[],[f19])).
% 3.17/0.93  
% 3.17/0.93  fof(f21,plain,(
% 3.17/0.93    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 3.17/0.93    inference(rectify,[],[f20])).
% 3.17/0.93  
% 3.17/0.93  fof(f22,plain,(
% 3.17/0.93    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1))))),
% 3.17/0.93    introduced(choice_axiom,[])).
% 3.17/0.93  
% 3.17/0.93  fof(f23,plain,(
% 3.17/0.93    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 3.17/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 3.17/0.93  
% 3.17/0.93  fof(f43,plain,(
% 3.17/0.93    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.17/0.93    inference(cnf_transformation,[],[f23])).
% 3.17/0.93  
% 3.17/0.93  fof(f65,plain,(
% 3.17/0.93    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,X5),X1) | ~r2_hidden(X5,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.17/0.93    inference(equality_resolution,[],[f43])).
% 3.17/0.93  
% 3.17/0.93  fof(f66,plain,(
% 3.17/0.93    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) | ~r2_hidden(X5,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.17/0.93    inference(equality_resolution,[],[f65])).
% 3.17/0.93  
% 3.17/0.93  fof(f1,axiom,(
% 3.17/0.93    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.17/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.93  
% 3.17/0.93  fof(f10,plain,(
% 3.17/0.93    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.17/0.93    inference(unused_predicate_definition_removal,[],[f1])).
% 3.17/0.93  
% 3.17/0.93  fof(f11,plain,(
% 3.17/0.93    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.17/0.93    inference(ennf_transformation,[],[f10])).
% 3.17/0.93  
% 3.17/0.93  fof(f40,plain,(
% 3.17/0.93    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.17/0.93    inference(cnf_transformation,[],[f11])).
% 3.17/0.93  
% 3.17/0.93  fof(f8,conjecture,(
% 3.17/0.93    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.17/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.93  
% 3.17/0.93  fof(f9,negated_conjecture,(
% 3.17/0.93    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.17/0.93    inference(negated_conjecture,[],[f8])).
% 3.17/0.93  
% 3.17/0.93  fof(f17,plain,(
% 3.17/0.93    ? [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.17/0.93    inference(ennf_transformation,[],[f9])).
% 3.17/0.93  
% 3.17/0.93  fof(f18,plain,(
% 3.17/0.93    ? [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0) & v1_relat_1(X1))),
% 3.17/0.93    inference(flattening,[],[f17])).
% 3.17/0.93  
% 3.17/0.93  fof(f38,plain,(
% 3.17/0.93    ? [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0) & v1_relat_1(X1)) => (k5_relat_1(k6_relat_1(sK9),sK10) != sK10 & r1_tarski(k1_relat_1(sK10),sK9) & v1_relat_1(sK10))),
% 3.17/0.93    introduced(choice_axiom,[])).
% 3.17/0.93  
% 3.17/0.93  fof(f39,plain,(
% 3.17/0.93    k5_relat_1(k6_relat_1(sK9),sK10) != sK10 & r1_tarski(k1_relat_1(sK10),sK9) & v1_relat_1(sK10)),
% 3.17/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f18,f38])).
% 3.17/0.93  
% 3.17/0.93  fof(f63,plain,(
% 3.17/0.93    r1_tarski(k1_relat_1(sK10),sK9)),
% 3.17/0.93    inference(cnf_transformation,[],[f39])).
% 3.17/0.93  
% 3.17/0.93  fof(f56,plain,(
% 3.17/0.93    ( ! [X2,X0,X5,X1] : (k5_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.17/0.93    inference(cnf_transformation,[],[f35])).
% 3.17/0.93  
% 3.17/0.93  fof(f6,axiom,(
% 3.17/0.93    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.17/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.93  
% 3.17/0.93  fof(f58,plain,(
% 3.17/0.93    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.17/0.93    inference(cnf_transformation,[],[f6])).
% 3.17/0.93  
% 3.17/0.93  fof(f3,axiom,(
% 3.17/0.93    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.17/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.93  
% 3.17/0.93  fof(f24,plain,(
% 3.17/0.93    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.17/0.93    inference(nnf_transformation,[],[f3])).
% 3.17/0.93  
% 3.17/0.93  fof(f25,plain,(
% 3.17/0.93    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.17/0.93    inference(rectify,[],[f24])).
% 3.17/0.93  
% 3.17/0.93  fof(f28,plain,(
% 3.17/0.93    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 3.17/0.93    introduced(choice_axiom,[])).
% 3.17/0.93  
% 3.17/0.93  fof(f27,plain,(
% 3.17/0.93    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 3.17/0.93    introduced(choice_axiom,[])).
% 3.17/0.93  
% 3.17/0.93  fof(f26,plain,(
% 3.17/0.93    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.17/0.93    introduced(choice_axiom,[])).
% 3.17/0.93  
% 3.17/0.93  fof(f29,plain,(
% 3.17/0.93    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.17/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).
% 3.17/0.93  
% 3.17/0.93  fof(f48,plain,(
% 3.17/0.93    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 3.17/0.93    inference(cnf_transformation,[],[f29])).
% 3.17/0.93  
% 3.17/0.93  fof(f69,plain,(
% 3.17/0.93    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 3.17/0.93    inference(equality_resolution,[],[f48])).
% 3.17/0.93  
% 3.17/0.93  fof(f54,plain,(
% 3.17/0.93    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.17/0.93    inference(cnf_transformation,[],[f35])).
% 3.17/0.93  
% 3.17/0.93  fof(f55,plain,(
% 3.17/0.93    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.17/0.93    inference(cnf_transformation,[],[f35])).
% 3.17/0.93  
% 3.17/0.93  fof(f64,plain,(
% 3.17/0.93    k5_relat_1(k6_relat_1(sK9),sK10) != sK10),
% 3.17/0.93    inference(cnf_transformation,[],[f39])).
% 3.17/0.93  
% 3.17/0.93  fof(f62,plain,(
% 3.17/0.93    v1_relat_1(sK10)),
% 3.17/0.93    inference(cnf_transformation,[],[f39])).
% 3.17/0.93  
% 3.17/0.93  cnf(c_20,plain,
% 3.17/0.93      ( r2_hidden(k4_tarski(X0,X1),X2)
% 3.17/0.93      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2))
% 3.17/0.93      | ~ v1_relat_1(X2) ),
% 3.17/0.93      inference(cnf_transformation,[],[f60]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_6319,plain,
% 3.17/0.93      ( ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),k5_relat_1(k6_relat_1(sK9),sK10))
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
% 3.17/0.93      | ~ v1_relat_1(sK10) ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_20]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_6320,plain,
% 3.17/0.93      ( r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),k5_relat_1(k6_relat_1(sK9),sK10)) != iProver_top
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) = iProver_top
% 3.17/0.93      | v1_relat_1(sK10) != iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_6319]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_17,plain,
% 3.17/0.93      ( ~ v1_relat_1(X0)
% 3.17/0.93      | ~ v1_relat_1(X1)
% 3.17/0.93      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.17/0.93      inference(cnf_transformation,[],[f57]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_2770,plain,
% 3.17/0.93      ( v1_relat_1(k5_relat_1(k6_relat_1(sK9),sK10))
% 3.17/0.93      | ~ v1_relat_1(k6_relat_1(sK9))
% 3.17/0.93      | ~ v1_relat_1(sK10) ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_17]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_2771,plain,
% 3.17/0.93      ( v1_relat_1(k5_relat_1(k6_relat_1(sK9),sK10)) = iProver_top
% 3.17/0.93      | v1_relat_1(k6_relat_1(sK9)) != iProver_top
% 3.17/0.93      | v1_relat_1(sK10) != iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_2770]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_14,plain,
% 3.17/0.93      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.17/0.93      | ~ r2_hidden(k4_tarski(X3,X0),X4)
% 3.17/0.93      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
% 3.17/0.93      | ~ v1_relat_1(X2)
% 3.17/0.93      | ~ v1_relat_1(X4)
% 3.17/0.93      | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
% 3.17/0.93      inference(cnf_transformation,[],[f71]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1105,plain,
% 3.17/0.93      ( ~ r2_hidden(k4_tarski(X0,sK7(k6_relat_1(sK9),sK10,sK10)),X1)
% 3.17/0.93      | r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK9),sK10,sK10)),k5_relat_1(X1,sK10))
% 3.17/0.93      | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
% 3.17/0.93      | ~ v1_relat_1(X1)
% 3.17/0.93      | ~ v1_relat_1(k5_relat_1(X1,sK10))
% 3.17/0.93      | ~ v1_relat_1(sK10) ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_14]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1797,plain,
% 3.17/0.93      ( ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
% 3.17/0.93      | ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK7(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9))
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),k5_relat_1(k6_relat_1(sK9),sK10))
% 3.17/0.93      | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK9),sK10))
% 3.17/0.93      | ~ v1_relat_1(k6_relat_1(sK9))
% 3.17/0.93      | ~ v1_relat_1(sK10) ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_1105]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1798,plain,
% 3.17/0.93      ( r2_hidden(k4_tarski(sK7(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) != iProver_top
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK7(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9)) != iProver_top
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),k5_relat_1(k6_relat_1(sK9),sK10)) = iProver_top
% 3.17/0.93      | v1_relat_1(k5_relat_1(k6_relat_1(sK9),sK10)) != iProver_top
% 3.17/0.93      | v1_relat_1(k6_relat_1(sK9)) != iProver_top
% 3.17/0.93      | v1_relat_1(sK10) != iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_1797]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_4,plain,
% 3.17/0.93      ( ~ r2_hidden(X0,X1)
% 3.17/0.93      | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
% 3.17/0.93      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 3.17/0.93      inference(cnf_transformation,[],[f66]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1661,plain,
% 3.17/0.93      ( ~ r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),sK9)
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK5(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9))
% 3.17/0.93      | ~ v1_relat_1(k6_relat_1(sK9)) ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_4]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1662,plain,
% 3.17/0.93      ( r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),sK9) != iProver_top
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK5(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9)) = iProver_top
% 3.17/0.93      | v1_relat_1(k6_relat_1(sK9)) != iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_1661]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_0,plain,
% 3.17/0.93      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.17/0.93      inference(cnf_transformation,[],[f40]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_23,negated_conjecture,
% 3.17/0.93      ( r1_tarski(k1_relat_1(sK10),sK9) ),
% 3.17/0.93      inference(cnf_transformation,[],[f63]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_271,plain,
% 3.17/0.93      ( ~ r2_hidden(X0,X1)
% 3.17/0.93      | r2_hidden(X0,X2)
% 3.17/0.93      | k1_relat_1(sK10) != X1
% 3.17/0.93      | sK9 != X2 ),
% 3.17/0.93      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_272,plain,
% 3.17/0.93      ( ~ r2_hidden(X0,k1_relat_1(sK10)) | r2_hidden(X0,sK9) ),
% 3.17/0.93      inference(unflattening,[status(thm)],[c_271]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1375,plain,
% 3.17/0.93      ( ~ r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),k1_relat_1(sK10))
% 3.17/0.93      | r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),sK9) ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_272]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1376,plain,
% 3.17/0.93      ( r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),k1_relat_1(sK10)) != iProver_top
% 3.17/0.93      | r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),sK9) = iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_11,plain,
% 3.17/0.93      ( ~ r2_hidden(k4_tarski(X0,sK6(X1,X2,X3)),X2)
% 3.17/0.93      | ~ r2_hidden(k4_tarski(sK5(X1,X2,X3),X0),X1)
% 3.17/0.93      | ~ r2_hidden(k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)),X3)
% 3.17/0.93      | ~ v1_relat_1(X2)
% 3.17/0.93      | ~ v1_relat_1(X3)
% 3.17/0.93      | ~ v1_relat_1(X1)
% 3.17/0.93      | k5_relat_1(X1,X2) = X3 ),
% 3.17/0.93      inference(cnf_transformation,[],[f56]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1084,plain,
% 3.17/0.93      ( ~ r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
% 3.17/0.93      | ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),X0),k6_relat_1(sK9))
% 3.17/0.93      | ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
% 3.17/0.93      | ~ v1_relat_1(k6_relat_1(sK9))
% 3.17/0.93      | ~ v1_relat_1(sK10)
% 3.17/0.93      | k5_relat_1(k6_relat_1(sK9),sK10) = sK10 ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_11]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1332,plain,
% 3.17/0.93      ( ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK5(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9))
% 3.17/0.93      | ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
% 3.17/0.93      | ~ v1_relat_1(k6_relat_1(sK9))
% 3.17/0.93      | ~ v1_relat_1(sK10)
% 3.17/0.93      | k5_relat_1(k6_relat_1(sK9),sK10) = sK10 ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_1084]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1333,plain,
% 3.17/0.93      ( k5_relat_1(k6_relat_1(sK9),sK10) = sK10
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK5(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9)) != iProver_top
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) != iProver_top
% 3.17/0.93      | v1_relat_1(k6_relat_1(sK9)) != iProver_top
% 3.17/0.93      | v1_relat_1(sK10) != iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_1332]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_18,plain,
% 3.17/0.93      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.17/0.93      inference(cnf_transformation,[],[f58]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1155,plain,
% 3.17/0.93      ( v1_relat_1(k6_relat_1(sK9)) ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_18]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1156,plain,
% 3.17/0.93      ( v1_relat_1(k6_relat_1(sK9)) = iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_9,plain,
% 3.17/0.93      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 3.17/0.93      inference(cnf_transformation,[],[f69]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1123,plain,
% 3.17/0.93      ( r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),k1_relat_1(sK10))
% 3.17/0.93      | ~ r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_9]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1124,plain,
% 3.17/0.93      ( r2_hidden(sK5(k6_relat_1(sK9),sK10,sK10),k1_relat_1(sK10)) = iProver_top
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) != iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_13,plain,
% 3.17/0.93      ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X0)
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
% 3.17/0.93      | ~ v1_relat_1(X1)
% 3.17/0.93      | ~ v1_relat_1(X2)
% 3.17/0.93      | ~ v1_relat_1(X0)
% 3.17/0.93      | k5_relat_1(X0,X1) = X2 ),
% 3.17/0.93      inference(cnf_transformation,[],[f54]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1081,plain,
% 3.17/0.93      ( r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK7(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9))
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
% 3.17/0.93      | ~ v1_relat_1(k6_relat_1(sK9))
% 3.17/0.93      | ~ v1_relat_1(sK10)
% 3.17/0.93      | k5_relat_1(k6_relat_1(sK9),sK10) = sK10 ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_13]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1082,plain,
% 3.17/0.93      ( k5_relat_1(k6_relat_1(sK9),sK10) = sK10
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK7(k6_relat_1(sK9),sK10,sK10)),k6_relat_1(sK9)) = iProver_top
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) = iProver_top
% 3.17/0.93      | v1_relat_1(k6_relat_1(sK9)) != iProver_top
% 3.17/0.93      | v1_relat_1(sK10) != iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_1081]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_12,plain,
% 3.17/0.93      ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X1)
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
% 3.17/0.93      | ~ v1_relat_1(X1)
% 3.17/0.93      | ~ v1_relat_1(X2)
% 3.17/0.93      | ~ v1_relat_1(X0)
% 3.17/0.93      | k5_relat_1(X0,X1) = X2 ),
% 3.17/0.93      inference(cnf_transformation,[],[f55]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1072,plain,
% 3.17/0.93      ( r2_hidden(k4_tarski(sK7(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10)
% 3.17/0.93      | ~ v1_relat_1(k6_relat_1(sK9))
% 3.17/0.93      | ~ v1_relat_1(sK10)
% 3.17/0.93      | k5_relat_1(k6_relat_1(sK9),sK10) = sK10 ),
% 3.17/0.93      inference(instantiation,[status(thm)],[c_12]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_1073,plain,
% 3.17/0.93      ( k5_relat_1(k6_relat_1(sK9),sK10) = sK10
% 3.17/0.93      | r2_hidden(k4_tarski(sK7(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) = iProver_top
% 3.17/0.93      | r2_hidden(k4_tarski(sK5(k6_relat_1(sK9),sK10,sK10),sK6(k6_relat_1(sK9),sK10,sK10)),sK10) = iProver_top
% 3.17/0.93      | v1_relat_1(k6_relat_1(sK9)) != iProver_top
% 3.17/0.93      | v1_relat_1(sK10) != iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_1072]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_22,negated_conjecture,
% 3.17/0.93      ( k5_relat_1(k6_relat_1(sK9),sK10) != sK10 ),
% 3.17/0.93      inference(cnf_transformation,[],[f64]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_24,negated_conjecture,
% 3.17/0.93      ( v1_relat_1(sK10) ),
% 3.17/0.93      inference(cnf_transformation,[],[f62]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(c_25,plain,
% 3.17/0.93      ( v1_relat_1(sK10) = iProver_top ),
% 3.17/0.93      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.17/0.93  
% 3.17/0.93  cnf(contradiction,plain,
% 3.17/0.93      ( $false ),
% 3.17/0.93      inference(minisat,
% 3.17/0.93                [status(thm)],
% 3.17/0.93                [c_6320,c_2771,c_1798,c_1662,c_1376,c_1333,c_1156,c_1124,
% 3.17/0.93                 c_1082,c_1073,c_22,c_25]) ).
% 3.17/0.93  
% 3.17/0.93  
% 3.17/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 3.17/0.93  
% 3.17/0.93  ------                               Statistics
% 3.17/0.93  
% 3.17/0.93  ------ General
% 3.17/0.93  
% 3.17/0.93  abstr_ref_over_cycles:                  0
% 3.17/0.93  abstr_ref_under_cycles:                 0
% 3.17/0.93  gc_basic_clause_elim:                   0
% 3.17/0.93  forced_gc_time:                         0
% 3.17/0.93  parsing_time:                           0.009
% 3.17/0.93  unif_index_cands_time:                  0.
% 3.17/0.93  unif_index_add_time:                    0.
% 3.17/0.93  orderings_time:                         0.
% 3.17/0.93  out_proof_time:                         0.008
% 3.17/0.93  total_time:                             0.223
% 3.17/0.93  num_of_symbols:                         49
% 3.17/0.93  num_of_terms:                           7792
% 3.17/0.93  
% 3.17/0.93  ------ Preprocessing
% 3.17/0.93  
% 3.17/0.93  num_of_splits:                          0
% 3.17/0.93  num_of_split_atoms:                     0
% 3.17/0.93  num_of_reused_defs:                     0
% 3.17/0.93  num_eq_ax_congr_red:                    69
% 3.17/0.93  num_of_sem_filtered_clauses:            1
% 3.17/0.93  num_of_subtypes:                        0
% 3.17/0.93  monotx_restored_types:                  0
% 3.17/0.93  sat_num_of_epr_types:                   0
% 3.17/0.93  sat_num_of_non_cyclic_types:            0
% 3.17/0.93  sat_guarded_non_collapsed_types:        0
% 3.17/0.93  num_pure_diseq_elim:                    0
% 3.17/0.93  simp_replaced_by:                       0
% 3.17/0.93  res_preprocessed:                       114
% 3.17/0.93  prep_upred:                             0
% 3.17/0.93  prep_unflattend:                        2
% 3.17/0.93  smt_new_axioms:                         0
% 3.17/0.93  pred_elim_cands:                        2
% 3.17/0.93  pred_elim:                              1
% 3.17/0.93  pred_elim_cl:                           1
% 3.17/0.93  pred_elim_cycles:                       3
% 3.17/0.93  merged_defs:                            0
% 3.17/0.93  merged_defs_ncl:                        0
% 3.17/0.93  bin_hyper_res:                          0
% 3.17/0.93  prep_cycles:                            4
% 3.17/0.93  pred_elim_time:                         0.001
% 3.17/0.93  splitting_time:                         0.
% 3.17/0.93  sem_filter_time:                        0.
% 3.17/0.93  monotx_time:                            0.
% 3.17/0.93  subtype_inf_time:                       0.
% 3.17/0.93  
% 3.17/0.93  ------ Problem properties
% 3.17/0.93  
% 3.17/0.93  clauses:                                24
% 3.17/0.93  conjectures:                            2
% 3.17/0.93  epr:                                    1
% 3.17/0.93  horn:                                   19
% 3.17/0.93  ground:                                 2
% 3.17/0.93  unary:                                  3
% 3.17/0.93  binary:                                 3
% 3.17/0.93  lits:                                   85
% 3.17/0.93  lits_eq:                                12
% 3.17/0.93  fd_pure:                                0
% 3.17/0.93  fd_pseudo:                              0
% 3.17/0.93  fd_cond:                                0
% 3.17/0.93  fd_pseudo_cond:                         9
% 3.17/0.93  ac_symbols:                             0
% 3.17/0.93  
% 3.17/0.93  ------ Propositional Solver
% 3.17/0.93  
% 3.17/0.93  prop_solver_calls:                      28
% 3.17/0.93  prop_fast_solver_calls:                 950
% 3.17/0.93  smt_solver_calls:                       0
% 3.17/0.93  smt_fast_solver_calls:                  0
% 3.17/0.93  prop_num_of_clauses:                    2378
% 3.17/0.93  prop_preprocess_simplified:             6679
% 3.17/0.93  prop_fo_subsumed:                       0
% 3.17/0.93  prop_solver_time:                       0.
% 3.17/0.93  smt_solver_time:                        0.
% 3.17/0.93  smt_fast_solver_time:                   0.
% 3.17/0.93  prop_fast_solver_time:                  0.
% 3.17/0.93  prop_unsat_core_time:                   0.
% 3.17/0.93  
% 3.17/0.93  ------ QBF
% 3.17/0.93  
% 3.17/0.93  qbf_q_res:                              0
% 3.17/0.93  qbf_num_tautologies:                    0
% 3.17/0.93  qbf_prep_cycles:                        0
% 3.17/0.93  
% 3.17/0.93  ------ BMC1
% 3.17/0.93  
% 3.17/0.93  bmc1_current_bound:                     -1
% 3.17/0.93  bmc1_last_solved_bound:                 -1
% 3.17/0.93  bmc1_unsat_core_size:                   -1
% 3.17/0.93  bmc1_unsat_core_parents_size:           -1
% 3.17/0.93  bmc1_merge_next_fun:                    0
% 3.17/0.93  bmc1_unsat_core_clauses_time:           0.
% 3.17/0.93  
% 3.17/0.93  ------ Instantiation
% 3.17/0.93  
% 3.17/0.93  inst_num_of_clauses:                    593
% 3.17/0.93  inst_num_in_passive:                    337
% 3.17/0.93  inst_num_in_active:                     217
% 3.17/0.93  inst_num_in_unprocessed:                38
% 3.17/0.93  inst_num_of_loops:                      259
% 3.17/0.93  inst_num_of_learning_restarts:          0
% 3.17/0.93  inst_num_moves_active_passive:          39
% 3.17/0.93  inst_lit_activity:                      0
% 3.17/0.93  inst_lit_activity_moves:                0
% 3.17/0.93  inst_num_tautologies:                   0
% 3.17/0.93  inst_num_prop_implied:                  0
% 3.17/0.93  inst_num_existing_simplified:           0
% 3.17/0.93  inst_num_eq_res_simplified:             0
% 3.17/0.93  inst_num_child_elim:                    0
% 3.17/0.93  inst_num_of_dismatching_blockings:      68
% 3.17/0.93  inst_num_of_non_proper_insts:           429
% 3.17/0.93  inst_num_of_duplicates:                 0
% 3.17/0.93  inst_inst_num_from_inst_to_res:         0
% 3.17/0.93  inst_dismatching_checking_time:         0.
% 3.17/0.93  
% 3.17/0.93  ------ Resolution
% 3.17/0.93  
% 3.17/0.93  res_num_of_clauses:                     0
% 3.17/0.93  res_num_in_passive:                     0
% 3.17/0.93  res_num_in_active:                      0
% 3.17/0.93  res_num_of_loops:                       118
% 3.17/0.93  res_forward_subset_subsumed:            19
% 3.17/0.93  res_backward_subset_subsumed:           0
% 3.17/0.93  res_forward_subsumed:                   0
% 3.17/0.93  res_backward_subsumed:                  0
% 3.17/0.93  res_forward_subsumption_resolution:     0
% 3.17/0.93  res_backward_subsumption_resolution:    0
% 3.17/0.93  res_clause_to_clause_subsumption:       512
% 3.17/0.93  res_orphan_elimination:                 0
% 3.17/0.93  res_tautology_del:                      17
% 3.17/0.93  res_num_eq_res_simplified:              0
% 3.17/0.93  res_num_sel_changes:                    0
% 3.17/0.93  res_moves_from_active_to_pass:          0
% 3.17/0.93  
% 3.17/0.93  ------ Superposition
% 3.17/0.93  
% 3.17/0.93  sup_time_total:                         0.
% 3.17/0.93  sup_time_generating:                    0.
% 3.17/0.93  sup_time_sim_full:                      0.
% 3.17/0.93  sup_time_sim_immed:                     0.
% 3.17/0.93  
% 3.17/0.93  sup_num_of_clauses:                     190
% 3.17/0.93  sup_num_in_active:                      50
% 3.17/0.93  sup_num_in_passive:                     140
% 3.17/0.93  sup_num_of_loops:                       50
% 3.17/0.93  sup_fw_superposition:                   52
% 3.17/0.93  sup_bw_superposition:                   124
% 3.17/0.93  sup_immediate_simplified:               2
% 3.17/0.93  sup_given_eliminated:                   0
% 3.17/0.93  comparisons_done:                       0
% 3.17/0.93  comparisons_avoided:                    8
% 3.17/0.93  
% 3.17/0.93  ------ Simplifications
% 3.17/0.93  
% 3.17/0.93  
% 3.17/0.93  sim_fw_subset_subsumed:                 1
% 3.17/0.93  sim_bw_subset_subsumed:                 0
% 3.17/0.93  sim_fw_subsumed:                        1
% 3.17/0.93  sim_bw_subsumed:                        0
% 3.17/0.93  sim_fw_subsumption_res:                 7
% 3.17/0.93  sim_bw_subsumption_res:                 0
% 3.17/0.93  sim_tautology_del:                      6
% 3.17/0.93  sim_eq_tautology_del:                   2
% 3.17/0.93  sim_eq_res_simp:                        2
% 3.17/0.93  sim_fw_demodulated:                     0
% 3.17/0.93  sim_bw_demodulated:                     0
% 3.17/0.93  sim_light_normalised:                   0
% 3.17/0.93  sim_joinable_taut:                      0
% 3.17/0.93  sim_joinable_simp:                      0
% 3.17/0.93  sim_ac_normalised:                      0
% 3.17/0.93  sim_smt_subsumption:                    0
% 3.17/0.93  
%------------------------------------------------------------------------------
