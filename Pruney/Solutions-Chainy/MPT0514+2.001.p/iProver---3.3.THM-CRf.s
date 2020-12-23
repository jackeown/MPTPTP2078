%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:23 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 218 expanded)
%              Number of clauses        :   73 (  85 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  599 (1351 expanded)
%              Number of equality atoms :  109 ( 190 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
            & r2_hidden(sK0(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK0(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                    & r2_hidden(sK0(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f33,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

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

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f12])).

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
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
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
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f41,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f35,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f39,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) != k5_relat_1(k7_relat_1(X1,X0),X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) != k5_relat_1(k7_relat_1(X1,X0),X2)
          & v1_relat_1(X2) )
     => ( k7_relat_1(k5_relat_1(X1,sK8),X0) != k5_relat_1(k7_relat_1(X1,X0),sK8)
        & v1_relat_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_relat_1(k5_relat_1(X1,X2),X0) != k5_relat_1(k7_relat_1(X1,X0),X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(k5_relat_1(sK7,X2),sK6) != k5_relat_1(k7_relat_1(sK7,sK6),X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) != k5_relat_1(k7_relat_1(sK7,sK6),sK8)
    & v1_relat_1(sK8)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f17,f30,f29])).

fof(f50,plain,(
    k7_relat_1(k5_relat_1(sK7,sK8),sK6) != k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_349,plain,
    ( r2_hidden(X0_43,X0_44)
    | ~ r2_hidden(k4_tarski(X0_43,X1_43),k7_relat_1(X1_44,X0_44))
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(k7_relat_1(X1_44,X0_44)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_5259,plain,
    ( r2_hidden(sK0(X0_44,X1_44,X2_44),X3_44)
    | ~ r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK5(k7_relat_1(X4_44,X3_44),X5_44,sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44))),k7_relat_1(X4_44,X3_44))
    | ~ v1_relat_1(X4_44)
    | ~ v1_relat_1(k7_relat_1(X4_44,X3_44)) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_12514,plain,
    ( r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(k7_relat_1(sK7,sK6),sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6))
    | ~ v1_relat_1(k7_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_5259])).

cnf(c_12515,plain,
    ( r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(k7_relat_1(sK7,sK6),sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(k7_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12514])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_345,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),X0_44)
    | ~ r2_hidden(k4_tarski(X2_43,X0_43),X1_44)
    | r2_hidden(k4_tarski(X2_43,X1_43),k5_relat_1(X1_44,X0_44))
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(k5_relat_1(X1_44,X0_44)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_6693,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),X0_43),X0_44)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),X0_43),k5_relat_1(k7_relat_1(sK7,sK6),X0_44))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6))
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),X0_44))
    | ~ v1_relat_1(k7_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_8706,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK8)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6))
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | ~ v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | ~ v1_relat_1(k7_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6693])).

cnf(c_8707,plain,
    ( r2_hidden(k4_tarski(sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) = iProver_top
    | v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
    | v1_relat_1(k7_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8706])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_351,plain,
    ( ~ r2_hidden(X0_43,X0_44)
    | ~ r2_hidden(k4_tarski(X0_43,X1_43),X1_44)
    | r2_hidden(k4_tarski(X0_43,X1_43),k7_relat_1(X1_44,X0_44))
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(k7_relat_1(X1_44,X0_44)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1234,plain,
    ( ~ r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),X0_43),X0_44)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),X0_43),k7_relat_1(X0_44,sK6))
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(k7_relat_1(X0_44,sK6)) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_3394,plain,
    ( ~ r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),sK7)
    | ~ v1_relat_1(k7_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_3395,plain,
    ( r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6)) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),sK7) != iProver_top
    | v1_relat_1(k7_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3394])).

cnf(c_12,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_343,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44))
    | r2_hidden(k4_tarski(X0_43,sK5(X0_44,X1_44,X0_43,X1_43)),X0_44)
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(k5_relat_1(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_342,plain,
    ( ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X1_44)
    | v1_relat_1(k5_relat_1(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_460,plain,
    ( ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X1_44)
    | r2_hidden(k4_tarski(X0_43,sK5(X0_44,X1_44,X0_43,X1_43)),X0_44)
    | ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_342])).

cnf(c_461,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44))
    | r2_hidden(k4_tarski(X0_43,sK5(X0_44,X1_44,X0_43,X1_43)),X0_44)
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(X0_44) ),
    inference(renaming,[status(thm)],[c_460])).

cnf(c_821,plain,
    ( r2_hidden(k4_tarski(sK0(X0_44,X1_44,k5_relat_1(X2_44,X3_44)),sK5(X2_44,X3_44,sK0(X0_44,X1_44,k5_relat_1(X2_44,X3_44)),sK1(X0_44,X1_44,k5_relat_1(X2_44,X3_44)))),X2_44)
    | ~ r2_hidden(k4_tarski(sK0(X0_44,X1_44,k5_relat_1(X2_44,X3_44)),sK1(X0_44,X1_44,k5_relat_1(X2_44,X3_44))),k5_relat_1(X2_44,X3_44))
    | ~ v1_relat_1(X2_44)
    | ~ v1_relat_1(X3_44) ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_2481,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(k7_relat_1(sK7,sK6),sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | ~ v1_relat_1(k7_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_2482,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(k7_relat_1(sK7,sK6),sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6)) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
    | v1_relat_1(k7_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2481])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,plain,
    ( r1_tarski(k5_relat_1(k7_relat_1(X0,X1),X2),k5_relat_1(X0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_203,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | k5_relat_1(X3,X4) != X2
    | k5_relat_1(k7_relat_1(X3,X5),X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_204,plain,
    ( r2_hidden(X0,k5_relat_1(X1,X2))
    | ~ r2_hidden(X0,k5_relat_1(k7_relat_1(X1,X3),X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_337,plain,
    ( r2_hidden(X0_43,k5_relat_1(X0_44,X1_44))
    | ~ r2_hidden(X0_43,k5_relat_1(k7_relat_1(X0_44,X2_44),X1_44))
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_204])).

cnf(c_811,plain,
    ( r2_hidden(k4_tarski(sK0(X0_44,X1_44,k5_relat_1(k7_relat_1(X2_44,X3_44),X4_44)),sK1(X0_44,X1_44,k5_relat_1(k7_relat_1(X2_44,X3_44),X4_44))),k5_relat_1(X2_44,X4_44))
    | ~ r2_hidden(k4_tarski(sK0(X0_44,X1_44,k5_relat_1(k7_relat_1(X2_44,X3_44),X4_44)),sK1(X0_44,X1_44,k5_relat_1(k7_relat_1(X2_44,X3_44),X4_44))),k5_relat_1(k7_relat_1(X2_44,X3_44),X4_44))
    | ~ v1_relat_1(X2_44)
    | ~ v1_relat_1(X4_44) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_2478,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_2479,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2478])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_341,plain,
    ( ~ v1_relat_1(X0_44)
    | v1_relat_1(k7_relat_1(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1744,plain,
    ( ~ v1_relat_1(X0_44)
    | v1_relat_1(k7_relat_1(X0_44,sK6)) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1745,plain,
    ( v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k7_relat_1(X0_44,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1744])).

cnf(c_1747,plain,
    ( v1_relat_1(k7_relat_1(sK7,sK6)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_1225,plain,
    ( ~ v1_relat_1(X0_44)
    | v1_relat_1(k5_relat_1(k7_relat_1(X1_44,X2_44),X0_44))
    | ~ v1_relat_1(k7_relat_1(X1_44,X2_44)) ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_1726,plain,
    ( v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | ~ v1_relat_1(k7_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_1727,plain,
    ( v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8)) = iProver_top
    | v1_relat_1(k7_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1726])).

cnf(c_1382,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_1383,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_344,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44))
    | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_43,X1_43),X1_43),X1_44)
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(k5_relat_1(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_453,plain,
    ( ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X1_44)
    | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_43,X1_43),X1_43),X1_44)
    | ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_342])).

cnf(c_454,plain,
    ( ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44))
    | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_43,X1_43),X1_43),X1_44)
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(X0_44) ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_873,plain,
    ( r2_hidden(k4_tarski(sK5(X0_44,X1_44,sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),X1_44)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),k5_relat_1(X0_44,X1_44))
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(X0_44) ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_1252,plain,
    ( r2_hidden(k4_tarski(sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK8)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_1256,plain,
    ( r2_hidden(k4_tarski(sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_872,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK5(X0_44,X1_44,sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44))),X0_44)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),k5_relat_1(X0_44,X1_44))
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(X0_44) ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_1253,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),sK7)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_1254,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),sK7) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1253])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_354,plain,
    ( ~ r2_hidden(sK0(X0_44,X1_44,X2_44),X1_44)
    | ~ r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44)),X0_44)
    | ~ r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44)),X2_44)
    | ~ v1_relat_1(X2_44)
    | ~ v1_relat_1(X0_44)
    | k7_relat_1(X0_44,X1_44) = X2_44 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1244,plain,
    ( ~ r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_1245,plain,
    ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8)
    | r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_2,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_353,plain,
    ( r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44)),X2_44)
    | r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44)),X0_44)
    | ~ v1_relat_1(X2_44)
    | ~ v1_relat_1(X0_44)
    | k7_relat_1(X0_44,X1_44) = X2_44 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_871,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),X3_44)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),k5_relat_1(X0_44,X1_44))
    | ~ v1_relat_1(X3_44)
    | ~ v1_relat_1(k5_relat_1(X0_44,X1_44))
    | k7_relat_1(k5_relat_1(X0_44,X1_44),X2_44) = X3_44 ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_1089,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_1090,plain,
    ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8)) = iProver_top
    | v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1089])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_352,plain,
    ( r2_hidden(sK0(X0_44,X1_44,X2_44),X1_44)
    | r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44)),X2_44)
    | ~ v1_relat_1(X2_44)
    | ~ v1_relat_1(X0_44)
    | k7_relat_1(X0_44,X1_44) = X2_44 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_820,plain,
    ( r2_hidden(sK0(X0_44,X1_44,k5_relat_1(X2_44,X3_44)),X1_44)
    | r2_hidden(k4_tarski(sK0(X0_44,X1_44,k5_relat_1(X2_44,X3_44)),sK1(X0_44,X1_44,k5_relat_1(X2_44,X3_44))),k5_relat_1(X2_44,X3_44))
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(k5_relat_1(X2_44,X3_44))
    | k7_relat_1(X0_44,X1_44) = k5_relat_1(X2_44,X3_44) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_1072,plain,
    ( r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | ~ v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8))
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1073,plain,
    ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8)
    | r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6) = iProver_top
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) = iProver_top
    | v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1072])).

cnf(c_16,negated_conjecture,
    ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) != k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_340,negated_conjecture,
    ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) != k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12515,c_8707,c_3395,c_2482,c_2479,c_1747,c_1727,c_1383,c_1256,c_1254,c_1245,c_1090,c_1073,c_340,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:31:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.63/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.63/1.49  
% 7.63/1.49  ------  iProver source info
% 7.63/1.49  
% 7.63/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.63/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.63/1.49  git: non_committed_changes: false
% 7.63/1.49  git: last_make_outside_of_git: false
% 7.63/1.49  
% 7.63/1.49  ------ 
% 7.63/1.49  ------ Parsing...
% 7.63/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  ------ Proving...
% 7.63/1.49  ------ Problem Properties 
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  clauses                                 18
% 7.63/1.49  conjectures                             3
% 7.63/1.49  EPR                                     2
% 7.63/1.49  Horn                                    14
% 7.63/1.49  unary                                   3
% 7.63/1.49  binary                                  1
% 7.63/1.49  lits                                    76
% 7.63/1.49  lits eq                                 7
% 7.63/1.49  fd_pure                                 0
% 7.63/1.49  fd_pseudo                               0
% 7.63/1.49  fd_cond                                 0
% 7.63/1.49  fd_pseudo_cond                          6
% 7.63/1.49  AC symbols                              0
% 7.63/1.49  
% 7.63/1.49  ------ Input Options Time Limit: Unbounded
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ 
% 7.63/1.49  Current options:
% 7.63/1.49  ------ 
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  % SZS status Theorem for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  fof(f2,axiom,(
% 7.63/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f11,plain,(
% 7.63/1.49    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(ennf_transformation,[],[f2])).
% 7.63/1.49  
% 7.63/1.49  fof(f18,plain,(
% 7.63/1.49    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(nnf_transformation,[],[f11])).
% 7.63/1.49  
% 7.63/1.49  fof(f19,plain,(
% 7.63/1.49    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(flattening,[],[f18])).
% 7.63/1.49  
% 7.63/1.49  fof(f20,plain,(
% 7.63/1.49    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(rectify,[],[f19])).
% 7.63/1.49  
% 7.63/1.49  fof(f21,plain,(
% 7.63/1.49    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) & r2_hidden(sK0(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2))))),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f22,plain,(
% 7.63/1.49    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) & r2_hidden(sK0(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 7.63/1.49  
% 7.63/1.49  fof(f33,plain,(
% 7.63/1.49    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f22])).
% 7.63/1.49  
% 7.63/1.49  fof(f53,plain,(
% 7.63/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(equality_resolution,[],[f33])).
% 7.63/1.49  
% 7.63/1.49  fof(f3,axiom,(
% 7.63/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f12,plain,(
% 7.63/1.49    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(ennf_transformation,[],[f3])).
% 7.63/1.49  
% 7.63/1.49  fof(f23,plain,(
% 7.63/1.49    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(nnf_transformation,[],[f12])).
% 7.63/1.49  
% 7.63/1.49  fof(f24,plain,(
% 7.63/1.49    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(rectify,[],[f23])).
% 7.63/1.49  
% 7.63/1.49  fof(f27,plain,(
% 7.63/1.49    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f26,plain,(
% 7.63/1.49    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f25,plain,(
% 7.63/1.49    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f28,plain,(
% 7.63/1.49    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 7.63/1.49  
% 7.63/1.49  fof(f41,plain,(
% 7.63/1.49    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f28])).
% 7.63/1.49  
% 7.63/1.49  fof(f54,plain,(
% 7.63/1.49    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(equality_resolution,[],[f41])).
% 7.63/1.49  
% 7.63/1.49  fof(f35,plain,(
% 7.63/1.49    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f22])).
% 7.63/1.49  
% 7.63/1.49  fof(f51,plain,(
% 7.63/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(equality_resolution,[],[f35])).
% 7.63/1.49  
% 7.63/1.49  fof(f39,plain,(
% 7.63/1.49    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f28])).
% 7.63/1.49  
% 7.63/1.49  fof(f56,plain,(
% 7.63/1.49    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(equality_resolution,[],[f39])).
% 7.63/1.49  
% 7.63/1.49  fof(f4,axiom,(
% 7.63/1.49    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f13,plain,(
% 7.63/1.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.63/1.49    inference(ennf_transformation,[],[f4])).
% 7.63/1.49  
% 7.63/1.49  fof(f14,plain,(
% 7.63/1.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(flattening,[],[f13])).
% 7.63/1.49  
% 7.63/1.49  fof(f45,plain,(
% 7.63/1.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f14])).
% 7.63/1.49  
% 7.63/1.49  fof(f1,axiom,(
% 7.63/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f9,plain,(
% 7.63/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.63/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 7.63/1.49  
% 7.63/1.49  fof(f10,plain,(
% 7.63/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 7.63/1.49    inference(ennf_transformation,[],[f9])).
% 7.63/1.49  
% 7.63/1.49  fof(f32,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f10])).
% 7.63/1.49  
% 7.63/1.49  fof(f6,axiom,(
% 7.63/1.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f16,plain,(
% 7.63/1.49    ! [X0,X1] : (! [X2] : (r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 7.63/1.49    inference(ennf_transformation,[],[f6])).
% 7.63/1.49  
% 7.63/1.49  fof(f47,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f16])).
% 7.63/1.49  
% 7.63/1.49  fof(f5,axiom,(
% 7.63/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f15,plain,(
% 7.63/1.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(ennf_transformation,[],[f5])).
% 7.63/1.49  
% 7.63/1.49  fof(f46,plain,(
% 7.63/1.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f15])).
% 7.63/1.49  
% 7.63/1.49  fof(f40,plain,(
% 7.63/1.49    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f28])).
% 7.63/1.49  
% 7.63/1.49  fof(f55,plain,(
% 7.63/1.49    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(equality_resolution,[],[f40])).
% 7.63/1.49  
% 7.63/1.49  fof(f38,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f22])).
% 7.63/1.49  
% 7.63/1.49  fof(f37,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f22])).
% 7.63/1.49  
% 7.63/1.49  fof(f36,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f22])).
% 7.63/1.49  
% 7.63/1.49  fof(f7,conjecture,(
% 7.63/1.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 7.63/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f8,negated_conjecture,(
% 7.63/1.49    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 7.63/1.49    inference(negated_conjecture,[],[f7])).
% 7.63/1.49  
% 7.63/1.49  fof(f17,plain,(
% 7.63/1.49    ? [X0,X1] : (? [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) != k5_relat_1(k7_relat_1(X1,X0),X2) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 7.63/1.49    inference(ennf_transformation,[],[f8])).
% 7.63/1.49  
% 7.63/1.49  fof(f30,plain,(
% 7.63/1.49    ( ! [X0,X1] : (? [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) != k5_relat_1(k7_relat_1(X1,X0),X2) & v1_relat_1(X2)) => (k7_relat_1(k5_relat_1(X1,sK8),X0) != k5_relat_1(k7_relat_1(X1,X0),sK8) & v1_relat_1(sK8))) )),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f29,plain,(
% 7.63/1.49    ? [X0,X1] : (? [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) != k5_relat_1(k7_relat_1(X1,X0),X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(k5_relat_1(sK7,X2),sK6) != k5_relat_1(k7_relat_1(sK7,sK6),X2) & v1_relat_1(X2)) & v1_relat_1(sK7))),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f31,plain,(
% 7.63/1.49    (k7_relat_1(k5_relat_1(sK7,sK8),sK6) != k5_relat_1(k7_relat_1(sK7,sK6),sK8) & v1_relat_1(sK8)) & v1_relat_1(sK7)),
% 7.63/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f17,f30,f29])).
% 7.63/1.49  
% 7.63/1.49  fof(f50,plain,(
% 7.63/1.49    k7_relat_1(k5_relat_1(sK7,sK8),sK6) != k5_relat_1(k7_relat_1(sK7,sK6),sK8)),
% 7.63/1.49    inference(cnf_transformation,[],[f31])).
% 7.63/1.49  
% 7.63/1.49  fof(f49,plain,(
% 7.63/1.49    v1_relat_1(sK8)),
% 7.63/1.49    inference(cnf_transformation,[],[f31])).
% 7.63/1.49  
% 7.63/1.49  fof(f48,plain,(
% 7.63/1.49    v1_relat_1(sK7)),
% 7.63/1.49    inference(cnf_transformation,[],[f31])).
% 7.63/1.49  
% 7.63/1.49  cnf(c_6,plain,
% 7.63/1.49      ( r2_hidden(X0,X1)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
% 7.63/1.49      | ~ v1_relat_1(X3)
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_349,plain,
% 7.63/1.49      ( r2_hidden(X0_43,X0_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(X0_43,X1_43),k7_relat_1(X1_44,X0_44))
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(X1_44,X0_44)) ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_5259,plain,
% 7.63/1.49      ( r2_hidden(sK0(X0_44,X1_44,X2_44),X3_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK5(k7_relat_1(X4_44,X3_44),X5_44,sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44))),k7_relat_1(X4_44,X3_44))
% 7.63/1.49      | ~ v1_relat_1(X4_44)
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(X4_44,X3_44)) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_349]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_12514,plain,
% 7.63/1.49      ( r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(k7_relat_1(sK7,sK6),sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6))
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(sK7,sK6))
% 7.63/1.49      | ~ v1_relat_1(sK7) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_5259]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_12515,plain,
% 7.63/1.49      ( r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6) = iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(k7_relat_1(sK7,sK6),sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6)) != iProver_top
% 7.63/1.49      | v1_relat_1(k7_relat_1(sK7,sK6)) != iProver_top
% 7.63/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_12514]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_10,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(X3,X0),X4)
% 7.63/1.49      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
% 7.63/1.49      | ~ v1_relat_1(X4)
% 7.63/1.49      | ~ v1_relat_1(X2)
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_345,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(X0_43,X1_43),X0_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(X2_43,X0_43),X1_44)
% 7.63/1.49      | r2_hidden(k4_tarski(X2_43,X1_43),k5_relat_1(X1_44,X0_44))
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44)
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(X1_44,X0_44)) ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_6693,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),X0_43),X0_44)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),X0_43),k5_relat_1(k7_relat_1(sK7,sK6),X0_44))
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6))
% 7.63/1.49      | ~ v1_relat_1(X0_44)
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),X0_44))
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(sK7,sK6)) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_345]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_8706,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK8)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6))
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(sK7,sK6))
% 7.63/1.49      | ~ v1_relat_1(sK8) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_6693]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_8707,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK8) != iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6)) != iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) = iProver_top
% 7.63/1.49      | v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
% 7.63/1.49      | v1_relat_1(k7_relat_1(sK7,sK6)) != iProver_top
% 7.63/1.49      | v1_relat_1(sK8) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_8706]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_4,plain,
% 7.63/1.49      ( ~ r2_hidden(X0,X1)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 7.63/1.49      | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
% 7.63/1.49      | ~ v1_relat_1(X3)
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_351,plain,
% 7.63/1.49      ( ~ r2_hidden(X0_43,X0_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(X0_43,X1_43),X1_44)
% 7.63/1.49      | r2_hidden(k4_tarski(X0_43,X1_43),k7_relat_1(X1_44,X0_44))
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(X1_44,X0_44)) ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1234,plain,
% 7.63/1.49      ( ~ r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),X0_43),X0_44)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),X0_43),k7_relat_1(X0_44,sK6))
% 7.63/1.49      | ~ v1_relat_1(X0_44)
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(X0_44,sK6)) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_351]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_3394,plain,
% 7.63/1.49      ( ~ r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6))
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),sK7)
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(sK7,sK6))
% 7.63/1.49      | ~ v1_relat_1(sK7) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_1234]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_3395,plain,
% 7.63/1.49      ( r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6) != iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6)) = iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),sK7) != iProver_top
% 7.63/1.49      | v1_relat_1(k7_relat_1(sK7,sK6)) != iProver_top
% 7.63/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_3394]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_12,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 7.63/1.49      | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
% 7.63/1.49      | ~ v1_relat_1(X2)
% 7.63/1.49      | ~ v1_relat_1(X3)
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_343,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44))
% 7.63/1.49      | r2_hidden(k4_tarski(X0_43,sK5(X0_44,X1_44,X0_43,X1_43)),X0_44)
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44)
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(X0_44,X1_44)) ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_13,plain,
% 7.63/1.49      ( ~ v1_relat_1(X0)
% 7.63/1.49      | ~ v1_relat_1(X1)
% 7.63/1.49      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_342,plain,
% 7.63/1.49      ( ~ v1_relat_1(X0_44)
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | v1_relat_1(k5_relat_1(X0_44,X1_44)) ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_460,plain,
% 7.63/1.49      ( ~ v1_relat_1(X0_44)
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | r2_hidden(k4_tarski(X0_43,sK5(X0_44,X1_44,X0_43,X1_43)),X0_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44)) ),
% 7.63/1.49      inference(global_propositional_subsumption,
% 7.63/1.49                [status(thm)],
% 7.63/1.49                [c_343,c_342]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_461,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44))
% 7.63/1.49      | r2_hidden(k4_tarski(X0_43,sK5(X0_44,X1_44,X0_43,X1_43)),X0_44)
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44) ),
% 7.63/1.49      inference(renaming,[status(thm)],[c_460]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_821,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(X0_44,X1_44,k5_relat_1(X2_44,X3_44)),sK5(X2_44,X3_44,sK0(X0_44,X1_44,k5_relat_1(X2_44,X3_44)),sK1(X0_44,X1_44,k5_relat_1(X2_44,X3_44)))),X2_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(X0_44,X1_44,k5_relat_1(X2_44,X3_44)),sK1(X0_44,X1_44,k5_relat_1(X2_44,X3_44))),k5_relat_1(X2_44,X3_44))
% 7.63/1.49      | ~ v1_relat_1(X2_44)
% 7.63/1.49      | ~ v1_relat_1(X3_44) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_461]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_2481,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(k7_relat_1(sK7,sK6),sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6))
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(sK7,sK6))
% 7.63/1.49      | ~ v1_relat_1(sK8) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_821]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_2482,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(k7_relat_1(sK7,sK6),sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),k7_relat_1(sK7,sK6)) = iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
% 7.63/1.49      | v1_relat_1(k7_relat_1(sK7,sK6)) != iProver_top
% 7.63/1.49      | v1_relat_1(sK8) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_2481]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_0,plain,
% 7.63/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.63/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_15,plain,
% 7.63/1.49      ( r1_tarski(k5_relat_1(k7_relat_1(X0,X1),X2),k5_relat_1(X0,X2))
% 7.63/1.49      | ~ v1_relat_1(X2)
% 7.63/1.49      | ~ v1_relat_1(X0) ),
% 7.63/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_203,plain,
% 7.63/1.49      ( ~ r2_hidden(X0,X1)
% 7.63/1.49      | r2_hidden(X0,X2)
% 7.63/1.49      | ~ v1_relat_1(X3)
% 7.63/1.49      | ~ v1_relat_1(X4)
% 7.63/1.49      | k5_relat_1(X3,X4) != X2
% 7.63/1.49      | k5_relat_1(k7_relat_1(X3,X5),X4) != X1 ),
% 7.63/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_15]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_204,plain,
% 7.63/1.49      ( r2_hidden(X0,k5_relat_1(X1,X2))
% 7.63/1.49      | ~ r2_hidden(X0,k5_relat_1(k7_relat_1(X1,X3),X2))
% 7.63/1.49      | ~ v1_relat_1(X1)
% 7.63/1.49      | ~ v1_relat_1(X2) ),
% 7.63/1.49      inference(unflattening,[status(thm)],[c_203]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_337,plain,
% 7.63/1.49      ( r2_hidden(X0_43,k5_relat_1(X0_44,X1_44))
% 7.63/1.49      | ~ r2_hidden(X0_43,k5_relat_1(k7_relat_1(X0_44,X2_44),X1_44))
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44) ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_204]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_811,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(X0_44,X1_44,k5_relat_1(k7_relat_1(X2_44,X3_44),X4_44)),sK1(X0_44,X1_44,k5_relat_1(k7_relat_1(X2_44,X3_44),X4_44))),k5_relat_1(X2_44,X4_44))
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(X0_44,X1_44,k5_relat_1(k7_relat_1(X2_44,X3_44),X4_44)),sK1(X0_44,X1_44,k5_relat_1(k7_relat_1(X2_44,X3_44),X4_44))),k5_relat_1(k7_relat_1(X2_44,X3_44),X4_44))
% 7.63/1.49      | ~ v1_relat_1(X2_44)
% 7.63/1.49      | ~ v1_relat_1(X4_44) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_337]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_2478,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8))
% 7.63/1.49      | ~ v1_relat_1(sK8)
% 7.63/1.49      | ~ v1_relat_1(sK7) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_811]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_2479,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8)) = iProver_top
% 7.63/1.49      | v1_relat_1(sK8) != iProver_top
% 7.63/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_2478]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_14,plain,
% 7.63/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_341,plain,
% 7.63/1.49      ( ~ v1_relat_1(X0_44) | v1_relat_1(k7_relat_1(X0_44,X1_44)) ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1744,plain,
% 7.63/1.49      ( ~ v1_relat_1(X0_44) | v1_relat_1(k7_relat_1(X0_44,sK6)) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_341]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1745,plain,
% 7.63/1.49      ( v1_relat_1(X0_44) != iProver_top
% 7.63/1.49      | v1_relat_1(k7_relat_1(X0_44,sK6)) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_1744]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1747,plain,
% 7.63/1.49      ( v1_relat_1(k7_relat_1(sK7,sK6)) = iProver_top
% 7.63/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_1745]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1225,plain,
% 7.63/1.49      ( ~ v1_relat_1(X0_44)
% 7.63/1.49      | v1_relat_1(k5_relat_1(k7_relat_1(X1_44,X2_44),X0_44))
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(X1_44,X2_44)) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_342]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1726,plain,
% 7.63/1.49      ( v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | ~ v1_relat_1(k7_relat_1(sK7,sK6))
% 7.63/1.49      | ~ v1_relat_1(sK8) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_1225]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1727,plain,
% 7.63/1.49      ( v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8)) = iProver_top
% 7.63/1.49      | v1_relat_1(k7_relat_1(sK7,sK6)) != iProver_top
% 7.63/1.49      | v1_relat_1(sK8) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_1726]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1382,plain,
% 7.63/1.49      ( v1_relat_1(k5_relat_1(sK7,sK8))
% 7.63/1.49      | ~ v1_relat_1(sK8)
% 7.63/1.49      | ~ v1_relat_1(sK7) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_342]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1383,plain,
% 7.63/1.49      ( v1_relat_1(k5_relat_1(sK7,sK8)) = iProver_top
% 7.63/1.49      | v1_relat_1(sK8) != iProver_top
% 7.63/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_1382]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_11,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 7.63/1.49      | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
% 7.63/1.49      | ~ v1_relat_1(X2)
% 7.63/1.49      | ~ v1_relat_1(X3)
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_344,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44))
% 7.63/1.49      | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_43,X1_43),X1_43),X1_44)
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44)
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(X0_44,X1_44)) ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_453,plain,
% 7.63/1.49      ( ~ v1_relat_1(X0_44)
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_43,X1_43),X1_43),X1_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44)) ),
% 7.63/1.49      inference(global_propositional_subsumption,
% 7.63/1.49                [status(thm)],
% 7.63/1.49                [c_344,c_342]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_454,plain,
% 7.63/1.49      ( ~ r2_hidden(k4_tarski(X0_43,X1_43),k5_relat_1(X0_44,X1_44))
% 7.63/1.49      | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_43,X1_43),X1_43),X1_44)
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44) ),
% 7.63/1.49      inference(renaming,[status(thm)],[c_453]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_873,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK5(X0_44,X1_44,sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),X1_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),k5_relat_1(X0_44,X1_44))
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_454]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1252,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK8)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8))
% 7.63/1.49      | ~ v1_relat_1(sK8)
% 7.63/1.49      | ~ v1_relat_1(sK7) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_873]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1256,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),sK8) = iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8)) != iProver_top
% 7.63/1.49      | v1_relat_1(sK8) != iProver_top
% 7.63/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_1252]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_872,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK5(X0_44,X1_44,sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44))),X0_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),k5_relat_1(X0_44,X1_44))
% 7.63/1.49      | ~ v1_relat_1(X1_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_461]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1253,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),sK7)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8))
% 7.63/1.49      | ~ v1_relat_1(sK8)
% 7.63/1.49      | ~ v1_relat_1(sK7) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_872]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1254,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK5(sK7,sK8,sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)))),sK7) = iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8)) != iProver_top
% 7.63/1.49      | v1_relat_1(sK8) != iProver_top
% 7.63/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_1253]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1,plain,
% 7.63/1.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
% 7.63/1.49      | ~ v1_relat_1(X2)
% 7.63/1.49      | ~ v1_relat_1(X0)
% 7.63/1.49      | k7_relat_1(X0,X1) = X2 ),
% 7.63/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_354,plain,
% 7.63/1.49      ( ~ r2_hidden(sK0(X0_44,X1_44,X2_44),X1_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44)),X0_44)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44)),X2_44)
% 7.63/1.49      | ~ v1_relat_1(X2_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44)
% 7.63/1.49      | k7_relat_1(X0_44,X1_44) = X2_44 ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1244,plain,
% 7.63/1.49      ( ~ r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6)
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8))
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 7.63/1.49      | k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_354]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1245,plain,
% 7.63/1.49      ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8)
% 7.63/1.49      | r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6) != iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8)) != iProver_top
% 7.63/1.49      | v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
% 7.63/1.49      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_1244]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_2,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
% 7.63/1.49      | ~ v1_relat_1(X2)
% 7.63/1.49      | ~ v1_relat_1(X0)
% 7.63/1.49      | k7_relat_1(X0,X1) = X2 ),
% 7.63/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_353,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44)),X2_44)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44)),X0_44)
% 7.63/1.49      | ~ v1_relat_1(X2_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44)
% 7.63/1.49      | k7_relat_1(X0_44,X1_44) = X2_44 ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_871,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),X3_44)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(X0_44,X1_44),X2_44,X3_44),sK1(k5_relat_1(X0_44,X1_44),X2_44,X3_44)),k5_relat_1(X0_44,X1_44))
% 7.63/1.49      | ~ v1_relat_1(X3_44)
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(X0_44,X1_44))
% 7.63/1.49      | k7_relat_1(k5_relat_1(X0_44,X1_44),X2_44) = X3_44 ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_353]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1089,plain,
% 7.63/1.49      ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8))
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 7.63/1.49      | k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_871]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1090,plain,
% 7.63/1.49      ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) = iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(sK7,sK8)) = iProver_top
% 7.63/1.49      | v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
% 7.63/1.49      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_1089]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_3,plain,
% 7.63/1.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
% 7.63/1.49      | ~ v1_relat_1(X2)
% 7.63/1.49      | ~ v1_relat_1(X0)
% 7.63/1.49      | k7_relat_1(X0,X1) = X2 ),
% 7.63/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_352,plain,
% 7.63/1.49      ( r2_hidden(sK0(X0_44,X1_44,X2_44),X1_44)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(X0_44,X1_44,X2_44),sK1(X0_44,X1_44,X2_44)),X2_44)
% 7.63/1.49      | ~ v1_relat_1(X2_44)
% 7.63/1.49      | ~ v1_relat_1(X0_44)
% 7.63/1.49      | k7_relat_1(X0_44,X1_44) = X2_44 ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_820,plain,
% 7.63/1.49      ( r2_hidden(sK0(X0_44,X1_44,k5_relat_1(X2_44,X3_44)),X1_44)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(X0_44,X1_44,k5_relat_1(X2_44,X3_44)),sK1(X0_44,X1_44,k5_relat_1(X2_44,X3_44))),k5_relat_1(X2_44,X3_44))
% 7.63/1.49      | ~ v1_relat_1(X0_44)
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(X2_44,X3_44))
% 7.63/1.49      | k7_relat_1(X0_44,X1_44) = k5_relat_1(X2_44,X3_44) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_352]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1072,plain,
% 7.63/1.49      ( r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6)
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8))
% 7.63/1.49      | ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 7.63/1.49      | k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_820]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1073,plain,
% 7.63/1.49      ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) = k5_relat_1(k7_relat_1(sK7,sK6),sK8)
% 7.63/1.49      | r2_hidden(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK6) = iProver_top
% 7.63/1.49      | r2_hidden(k4_tarski(sK0(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8)),sK1(k5_relat_1(sK7,sK8),sK6,k5_relat_1(k7_relat_1(sK7,sK6),sK8))),k5_relat_1(k7_relat_1(sK7,sK6),sK8)) = iProver_top
% 7.63/1.49      | v1_relat_1(k5_relat_1(k7_relat_1(sK7,sK6),sK8)) != iProver_top
% 7.63/1.49      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_1072]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_16,negated_conjecture,
% 7.63/1.49      ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) != k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
% 7.63/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_340,negated_conjecture,
% 7.63/1.49      ( k7_relat_1(k5_relat_1(sK7,sK8),sK6) != k5_relat_1(k7_relat_1(sK7,sK6),sK8) ),
% 7.63/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_17,negated_conjecture,
% 7.63/1.49      ( v1_relat_1(sK8) ),
% 7.63/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_20,plain,
% 7.63/1.49      ( v1_relat_1(sK8) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_18,negated_conjecture,
% 7.63/1.49      ( v1_relat_1(sK7) ),
% 7.63/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_19,plain,
% 7.63/1.49      ( v1_relat_1(sK7) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(contradiction,plain,
% 7.63/1.49      ( $false ),
% 7.63/1.49      inference(minisat,
% 7.63/1.49                [status(thm)],
% 7.63/1.49                [c_12515,c_8707,c_3395,c_2482,c_2479,c_1747,c_1727,
% 7.63/1.49                 c_1383,c_1256,c_1254,c_1245,c_1090,c_1073,c_340,c_20,
% 7.63/1.49                 c_19]) ).
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  ------                               Statistics
% 7.63/1.49  
% 7.63/1.49  ------ Selected
% 7.63/1.49  
% 7.63/1.49  total_time:                             0.721
% 7.63/1.49  
%------------------------------------------------------------------------------
