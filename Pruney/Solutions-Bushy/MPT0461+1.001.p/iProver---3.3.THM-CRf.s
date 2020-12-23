%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0461+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 247 expanded)
%              Number of clauses        :   53 (  78 expanded)
%              Number of leaves         :   11 (  64 expanded)
%              Depth                    :   23
%              Number of atoms          :  411 (1250 expanded)
%              Number of equality atoms :  124 ( 160 expanded)
%              Maximal formula depth    :   16 (   6 average)
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
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
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
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( r1_tarski(X0,X1)
                 => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
          & r1_tarski(X0,X1)
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k5_relat_1(X0,sK8),k5_relat_1(X1,sK8))
        & r1_tarski(X0,X1)
        & v1_relat_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(sK7,X2))
            & r1_tarski(X0,sK7)
            & v1_relat_1(X2) )
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
                & r1_tarski(X0,X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK6,X2),k5_relat_1(X1,X2))
              & r1_tarski(sK6,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK8))
    & r1_tarski(sK6,sK7)
    & v1_relat_1(sK8)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f11,f24,f23,f22])).

fof(f39,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f29,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

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

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f30,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f31,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f40,plain,(
    ~ r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK8)) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_267,plain,
    ( r2_hidden(k4_tarski(sK0(X0_42,X1_42),sK1(X0_42,X1_42)),X0_42)
    | r1_tarski(X0_42,X1_42)
    | ~ v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_562,plain,
    ( r2_hidden(k4_tarski(sK0(X0_42,X1_42),sK1(X0_42,X1_42)),X0_42) = iProver_top
    | r1_tarski(X0_42,X1_42) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_268,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0_42,X1_42),sK1(X0_42,X1_42)),X1_42)
    | r1_tarski(X0_42,X1_42)
    | ~ v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_561,plain,
    ( r2_hidden(k4_tarski(sK0(X0_42,X1_42),sK1(X0_42,X1_42)),X1_42) != iProver_top
    | r1_tarski(X0_42,X1_42) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_991,plain,
    ( r1_tarski(X0_42,X0_42) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_562,c_561])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_257,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_572,plain,
    ( r1_tarski(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_8,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_260,plain,
    ( ~ r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42))
    | r2_hidden(k4_tarski(X0_44,sK5(X0_42,X1_42,X0_44,X1_44)),X0_42)
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | ~ v1_relat_1(k5_relat_1(X0_42,X1_42)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_569,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
    | r2_hidden(k4_tarski(X0_44,sK5(X0_42,X1_42,X0_44,X1_44)),X0_42) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(k5_relat_1(X0_42,X1_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_259,plain,
    ( ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | v1_relat_1(k5_relat_1(X0_42,X1_42)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_570,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(k5_relat_1(X0_42,X1_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_627,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
    | r2_hidden(k4_tarski(X0_44,sK5(X0_42,X1_42,X0_44,X1_44)),X0_42) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_569,c_570])).

cnf(c_2,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X0,X1),X3)
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_266,plain,
    ( ~ r2_hidden(k4_tarski(X0_44,X1_44),X0_42)
    | r2_hidden(k4_tarski(X0_44,X1_44),X1_42)
    | ~ r1_tarski(X0_42,X1_42)
    | ~ v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_563,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),X0_42) != iProver_top
    | r2_hidden(k4_tarski(X0_44,X1_44),X1_42) = iProver_top
    | r1_tarski(X0_42,X1_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_1414,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
    | r2_hidden(k4_tarski(X0_44,sK5(X0_42,X1_42,X0_44,X1_44)),X2_42) = iProver_top
    | r1_tarski(X0_42,X2_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_563])).

cnf(c_1664,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
    | r2_hidden(k4_tarski(X0_44,sK5(X0_42,X1_42,X0_44,X1_44)),X2_42) = iProver_top
    | r1_tarski(X3_42,X2_42) != iProver_top
    | r1_tarski(X0_42,X3_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X3_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_563])).

cnf(c_5521,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(sK6,X0_42)) != iProver_top
    | r2_hidden(k4_tarski(X0_44,sK5(sK6,X0_42,X0_44,X1_44)),X1_42) = iProver_top
    | r1_tarski(sK7,X1_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_572,c_1664])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5538,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(sK6,X0_42)) != iProver_top
    | r2_hidden(k4_tarski(X0_44,sK5(sK6,X0_42,X0_44,X1_44)),X1_42) = iProver_top
    | r1_tarski(sK7,X1_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5521,c_15,c_16])).

cnf(c_7,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_261,plain,
    ( ~ r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42))
    | r2_hidden(k4_tarski(sK5(X0_42,X1_42,X0_44,X1_44),X1_44),X1_42)
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | ~ v1_relat_1(k5_relat_1(X0_42,X1_42)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_568,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X0_42,X1_42,X0_44,X1_44),X1_44),X1_42) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(k5_relat_1(X0_42,X1_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_617,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X0_42,X1_42,X0_44,X1_44),X1_44),X1_42) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_568,c_570])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_262,plain,
    ( ~ r2_hidden(k4_tarski(X0_44,X1_44),X0_42)
    | ~ r2_hidden(k4_tarski(X2_44,X0_44),X1_42)
    | r2_hidden(k4_tarski(X2_44,X1_44),k5_relat_1(X1_42,X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | ~ v1_relat_1(k5_relat_1(X1_42,X0_42)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_567,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),X0_42) != iProver_top
    | r2_hidden(k4_tarski(X2_44,X0_44),X1_42) != iProver_top
    | r2_hidden(k4_tarski(X2_44,X1_44),k5_relat_1(X1_42,X0_42)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(k5_relat_1(X1_42,X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_638,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),X0_42) != iProver_top
    | r2_hidden(k4_tarski(X2_44,X0_44),X1_42) != iProver_top
    | r2_hidden(k4_tarski(X2_44,X1_44),k5_relat_1(X1_42,X0_42)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_567,c_570])).

cnf(c_1425,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
    | r2_hidden(k4_tarski(X2_44,X1_44),k5_relat_1(X2_42,X1_42)) = iProver_top
    | r2_hidden(k4_tarski(X2_44,sK5(X0_42,X1_42,X0_44,X1_44)),X2_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X2_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_638])).

cnf(c_5549,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) = iProver_top
    | r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(sK6,X1_42)) != iProver_top
    | r1_tarski(sK7,X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5538,c_1425])).

cnf(c_6267,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | r1_tarski(sK7,X0_42) != iProver_top
    | r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(sK6,X1_42)) != iProver_top
    | r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5549,c_15])).

cnf(c_6268,plain,
    ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) = iProver_top
    | r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(sK6,X1_42)) != iProver_top
    | r1_tarski(sK7,X0_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_6267])).

cnf(c_6284,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,X0_42),X1_42),sK1(k5_relat_1(sK6,X0_42),X1_42)),k5_relat_1(X2_42,X0_42)) = iProver_top
    | r1_tarski(k5_relat_1(sK6,X0_42),X1_42) = iProver_top
    | r1_tarski(sK7,X2_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X2_42) != iProver_top
    | v1_relat_1(k5_relat_1(sK6,X0_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_562,c_6268])).

cnf(c_10779,plain,
    ( r1_tarski(k5_relat_1(sK6,X0_42),k5_relat_1(X1_42,X0_42)) = iProver_top
    | r1_tarski(sK7,X1_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(k5_relat_1(sK6,X0_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6284,c_561])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK8)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_258,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK8)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_571,plain,
    ( r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_10856,plain,
    ( r1_tarski(sK7,sK7) != iProver_top
    | v1_relat_1(k5_relat_1(sK6,sK8)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_10779,c_571])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_779,plain,
    ( v1_relat_1(k5_relat_1(sK6,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_780,plain,
    ( v1_relat_1(k5_relat_1(sK6,sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_11047,plain,
    ( r1_tarski(sK7,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10856,c_15,c_16,c_17,c_780])).

cnf(c_11052,plain,
    ( v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_11047])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11052,c_16])).


%------------------------------------------------------------------------------
