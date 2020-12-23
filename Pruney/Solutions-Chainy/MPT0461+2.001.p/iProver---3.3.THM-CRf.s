%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:29 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
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
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 18:50:44 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.35/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/0.96  
% 3.35/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/0.96  
% 3.35/0.96  ------  iProver source info
% 3.35/0.96  
% 3.35/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.35/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/0.96  git: non_committed_changes: false
% 3.35/0.96  git: last_make_outside_of_git: false
% 3.35/0.96  
% 3.35/0.96  ------ 
% 3.35/0.96  
% 3.35/0.96  ------ Input Options
% 3.35/0.96  
% 3.35/0.96  --out_options                           all
% 3.35/0.96  --tptp_safe_out                         true
% 3.35/0.96  --problem_path                          ""
% 3.35/0.96  --include_path                          ""
% 3.35/0.96  --clausifier                            res/vclausify_rel
% 3.35/0.96  --clausifier_options                    --mode clausify
% 3.35/0.96  --stdin                                 false
% 3.35/0.96  --stats_out                             all
% 3.35/0.96  
% 3.35/0.96  ------ General Options
% 3.35/0.96  
% 3.35/0.96  --fof                                   false
% 3.35/0.96  --time_out_real                         305.
% 3.35/0.96  --time_out_virtual                      -1.
% 3.35/0.96  --symbol_type_check                     false
% 3.35/0.96  --clausify_out                          false
% 3.35/0.96  --sig_cnt_out                           false
% 3.35/0.96  --trig_cnt_out                          false
% 3.35/0.96  --trig_cnt_out_tolerance                1.
% 3.35/0.96  --trig_cnt_out_sk_spl                   false
% 3.35/0.96  --abstr_cl_out                          false
% 3.35/0.96  
% 3.35/0.96  ------ Global Options
% 3.35/0.96  
% 3.35/0.96  --schedule                              default
% 3.35/0.96  --add_important_lit                     false
% 3.35/0.96  --prop_solver_per_cl                    1000
% 3.35/0.96  --min_unsat_core                        false
% 3.35/0.96  --soft_assumptions                      false
% 3.35/0.96  --soft_lemma_size                       3
% 3.35/0.96  --prop_impl_unit_size                   0
% 3.35/0.96  --prop_impl_unit                        []
% 3.35/0.96  --share_sel_clauses                     true
% 3.35/0.96  --reset_solvers                         false
% 3.35/0.96  --bc_imp_inh                            [conj_cone]
% 3.35/0.96  --conj_cone_tolerance                   3.
% 3.35/0.96  --extra_neg_conj                        none
% 3.35/0.96  --large_theory_mode                     true
% 3.35/0.96  --prolific_symb_bound                   200
% 3.35/0.96  --lt_threshold                          2000
% 3.35/0.96  --clause_weak_htbl                      true
% 3.35/0.96  --gc_record_bc_elim                     false
% 3.35/0.96  
% 3.35/0.96  ------ Preprocessing Options
% 3.35/0.96  
% 3.35/0.96  --preprocessing_flag                    true
% 3.35/0.96  --time_out_prep_mult                    0.1
% 3.35/0.96  --splitting_mode                        input
% 3.35/0.96  --splitting_grd                         true
% 3.35/0.96  --splitting_cvd                         false
% 3.35/0.96  --splitting_cvd_svl                     false
% 3.35/0.96  --splitting_nvd                         32
% 3.35/0.96  --sub_typing                            true
% 3.35/0.96  --prep_gs_sim                           true
% 3.35/0.96  --prep_unflatten                        true
% 3.35/0.96  --prep_res_sim                          true
% 3.35/0.96  --prep_upred                            true
% 3.35/0.96  --prep_sem_filter                       exhaustive
% 3.35/0.96  --prep_sem_filter_out                   false
% 3.35/0.96  --pred_elim                             true
% 3.35/0.96  --res_sim_input                         true
% 3.35/0.96  --eq_ax_congr_red                       true
% 3.35/0.96  --pure_diseq_elim                       true
% 3.35/0.96  --brand_transform                       false
% 3.35/0.96  --non_eq_to_eq                          false
% 3.35/0.96  --prep_def_merge                        true
% 3.35/0.96  --prep_def_merge_prop_impl              false
% 3.35/0.96  --prep_def_merge_mbd                    true
% 3.35/0.96  --prep_def_merge_tr_red                 false
% 3.35/0.96  --prep_def_merge_tr_cl                  false
% 3.35/0.96  --smt_preprocessing                     true
% 3.35/0.96  --smt_ac_axioms                         fast
% 3.35/0.96  --preprocessed_out                      false
% 3.35/0.96  --preprocessed_stats                    false
% 3.35/0.96  
% 3.35/0.96  ------ Abstraction refinement Options
% 3.35/0.96  
% 3.35/0.96  --abstr_ref                             []
% 3.35/0.96  --abstr_ref_prep                        false
% 3.35/0.96  --abstr_ref_until_sat                   false
% 3.35/0.96  --abstr_ref_sig_restrict                funpre
% 3.35/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.96  --abstr_ref_under                       []
% 3.35/0.96  
% 3.35/0.96  ------ SAT Options
% 3.35/0.96  
% 3.35/0.96  --sat_mode                              false
% 3.35/0.96  --sat_fm_restart_options                ""
% 3.35/0.96  --sat_gr_def                            false
% 3.35/0.96  --sat_epr_types                         true
% 3.35/0.96  --sat_non_cyclic_types                  false
% 3.35/0.96  --sat_finite_models                     false
% 3.35/0.96  --sat_fm_lemmas                         false
% 3.35/0.96  --sat_fm_prep                           false
% 3.35/0.96  --sat_fm_uc_incr                        true
% 3.35/0.96  --sat_out_model                         small
% 3.35/0.96  --sat_out_clauses                       false
% 3.35/0.96  
% 3.35/0.96  ------ QBF Options
% 3.35/0.96  
% 3.35/0.96  --qbf_mode                              false
% 3.35/0.96  --qbf_elim_univ                         false
% 3.35/0.96  --qbf_dom_inst                          none
% 3.35/0.96  --qbf_dom_pre_inst                      false
% 3.35/0.96  --qbf_sk_in                             false
% 3.35/0.96  --qbf_pred_elim                         true
% 3.35/0.96  --qbf_split                             512
% 3.35/0.96  
% 3.35/0.96  ------ BMC1 Options
% 3.35/0.96  
% 3.35/0.96  --bmc1_incremental                      false
% 3.35/0.96  --bmc1_axioms                           reachable_all
% 3.35/0.96  --bmc1_min_bound                        0
% 3.35/0.96  --bmc1_max_bound                        -1
% 3.35/0.96  --bmc1_max_bound_default                -1
% 3.35/0.96  --bmc1_symbol_reachability              true
% 3.35/0.96  --bmc1_property_lemmas                  false
% 3.35/0.96  --bmc1_k_induction                      false
% 3.35/0.96  --bmc1_non_equiv_states                 false
% 3.35/0.96  --bmc1_deadlock                         false
% 3.35/0.96  --bmc1_ucm                              false
% 3.35/0.96  --bmc1_add_unsat_core                   none
% 3.35/0.96  --bmc1_unsat_core_children              false
% 3.35/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.96  --bmc1_out_stat                         full
% 3.35/0.96  --bmc1_ground_init                      false
% 3.35/0.96  --bmc1_pre_inst_next_state              false
% 3.35/0.96  --bmc1_pre_inst_state                   false
% 3.35/0.96  --bmc1_pre_inst_reach_state             false
% 3.35/0.96  --bmc1_out_unsat_core                   false
% 3.35/0.96  --bmc1_aig_witness_out                  false
% 3.35/0.96  --bmc1_verbose                          false
% 3.35/0.96  --bmc1_dump_clauses_tptp                false
% 3.35/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.96  --bmc1_dump_file                        -
% 3.35/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.96  --bmc1_ucm_extend_mode                  1
% 3.35/0.96  --bmc1_ucm_init_mode                    2
% 3.35/0.96  --bmc1_ucm_cone_mode                    none
% 3.35/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.96  --bmc1_ucm_relax_model                  4
% 3.35/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.96  --bmc1_ucm_layered_model                none
% 3.35/0.96  --bmc1_ucm_max_lemma_size               10
% 3.35/0.96  
% 3.35/0.96  ------ AIG Options
% 3.35/0.96  
% 3.35/0.96  --aig_mode                              false
% 3.35/0.96  
% 3.35/0.96  ------ Instantiation Options
% 3.35/0.96  
% 3.35/0.96  --instantiation_flag                    true
% 3.35/0.96  --inst_sos_flag                         false
% 3.35/0.96  --inst_sos_phase                        true
% 3.35/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.96  --inst_lit_sel_side                     num_symb
% 3.35/0.96  --inst_solver_per_active                1400
% 3.35/0.96  --inst_solver_calls_frac                1.
% 3.35/0.96  --inst_passive_queue_type               priority_queues
% 3.35/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.96  --inst_passive_queues_freq              [25;2]
% 3.35/0.96  --inst_dismatching                      true
% 3.35/0.96  --inst_eager_unprocessed_to_passive     true
% 3.35/0.96  --inst_prop_sim_given                   true
% 3.35/0.96  --inst_prop_sim_new                     false
% 3.35/0.96  --inst_subs_new                         false
% 3.35/0.96  --inst_eq_res_simp                      false
% 3.35/0.96  --inst_subs_given                       false
% 3.35/0.96  --inst_orphan_elimination               true
% 3.35/0.96  --inst_learning_loop_flag               true
% 3.35/0.96  --inst_learning_start                   3000
% 3.35/0.96  --inst_learning_factor                  2
% 3.35/0.96  --inst_start_prop_sim_after_learn       3
% 3.35/0.96  --inst_sel_renew                        solver
% 3.35/0.96  --inst_lit_activity_flag                true
% 3.35/0.96  --inst_restr_to_given                   false
% 3.35/0.96  --inst_activity_threshold               500
% 3.35/0.96  --inst_out_proof                        true
% 3.35/0.96  
% 3.35/0.96  ------ Resolution Options
% 3.35/0.96  
% 3.35/0.96  --resolution_flag                       true
% 3.35/0.96  --res_lit_sel                           adaptive
% 3.35/0.96  --res_lit_sel_side                      none
% 3.35/0.96  --res_ordering                          kbo
% 3.35/0.96  --res_to_prop_solver                    active
% 3.35/0.96  --res_prop_simpl_new                    false
% 3.35/0.96  --res_prop_simpl_given                  true
% 3.35/0.96  --res_passive_queue_type                priority_queues
% 3.35/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.96  --res_passive_queues_freq               [15;5]
% 3.35/0.96  --res_forward_subs                      full
% 3.35/0.96  --res_backward_subs                     full
% 3.35/0.96  --res_forward_subs_resolution           true
% 3.35/0.96  --res_backward_subs_resolution          true
% 3.35/0.96  --res_orphan_elimination                true
% 3.35/0.96  --res_time_limit                        2.
% 3.35/0.96  --res_out_proof                         true
% 3.35/0.96  
% 3.35/0.96  ------ Superposition Options
% 3.35/0.96  
% 3.35/0.96  --superposition_flag                    true
% 3.35/0.96  --sup_passive_queue_type                priority_queues
% 3.35/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.96  --demod_completeness_check              fast
% 3.35/0.96  --demod_use_ground                      true
% 3.35/0.96  --sup_to_prop_solver                    passive
% 3.35/0.96  --sup_prop_simpl_new                    true
% 3.35/0.96  --sup_prop_simpl_given                  true
% 3.35/0.96  --sup_fun_splitting                     false
% 3.35/0.96  --sup_smt_interval                      50000
% 3.35/0.96  
% 3.35/0.96  ------ Superposition Simplification Setup
% 3.35/0.96  
% 3.35/0.96  --sup_indices_passive                   []
% 3.35/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.96  --sup_full_bw                           [BwDemod]
% 3.35/0.96  --sup_immed_triv                        [TrivRules]
% 3.35/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.96  --sup_immed_bw_main                     []
% 3.35/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.96  
% 3.35/0.96  ------ Combination Options
% 3.35/0.96  
% 3.35/0.96  --comb_res_mult                         3
% 3.35/0.96  --comb_sup_mult                         2
% 3.35/0.96  --comb_inst_mult                        10
% 3.35/0.96  
% 3.35/0.96  ------ Debug Options
% 3.35/0.96  
% 3.35/0.96  --dbg_backtrace                         false
% 3.35/0.96  --dbg_dump_prop_clauses                 false
% 3.35/0.96  --dbg_dump_prop_clauses_file            -
% 3.35/0.96  --dbg_out_stat                          false
% 3.35/0.96  ------ Parsing...
% 3.35/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/0.96  
% 3.35/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.35/0.96  
% 3.35/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/0.96  
% 3.35/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/0.96  ------ Proving...
% 3.35/0.96  ------ Problem Properties 
% 3.35/0.96  
% 3.35/0.96  
% 3.35/0.96  clauses                                 15
% 3.35/0.96  conjectures                             5
% 3.35/0.96  EPR                                     4
% 3.35/0.96  Horn                                    12
% 3.35/0.96  unary                                   5
% 3.35/0.96  binary                                  0
% 3.35/0.96  lits                                    53
% 3.35/0.96  lits eq                                 3
% 3.35/0.96  fd_pure                                 0
% 3.35/0.96  fd_pseudo                               0
% 3.35/0.96  fd_cond                                 0
% 3.35/0.96  fd_pseudo_cond                          3
% 3.35/0.96  AC symbols                              0
% 3.35/0.96  
% 3.35/0.96  ------ Schedule dynamic 5 is on 
% 3.35/0.96  
% 3.35/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.35/0.96  
% 3.35/0.96  
% 3.35/0.96  ------ 
% 3.35/0.96  Current options:
% 3.35/0.96  ------ 
% 3.35/0.96  
% 3.35/0.96  ------ Input Options
% 3.35/0.96  
% 3.35/0.96  --out_options                           all
% 3.35/0.96  --tptp_safe_out                         true
% 3.35/0.96  --problem_path                          ""
% 3.35/0.96  --include_path                          ""
% 3.35/0.96  --clausifier                            res/vclausify_rel
% 3.35/0.96  --clausifier_options                    --mode clausify
% 3.35/0.96  --stdin                                 false
% 3.35/0.96  --stats_out                             all
% 3.35/0.96  
% 3.35/0.96  ------ General Options
% 3.35/0.96  
% 3.35/0.96  --fof                                   false
% 3.35/0.96  --time_out_real                         305.
% 3.35/0.96  --time_out_virtual                      -1.
% 3.35/0.96  --symbol_type_check                     false
% 3.35/0.96  --clausify_out                          false
% 3.35/0.96  --sig_cnt_out                           false
% 3.35/0.96  --trig_cnt_out                          false
% 3.35/0.96  --trig_cnt_out_tolerance                1.
% 3.35/0.96  --trig_cnt_out_sk_spl                   false
% 3.35/0.96  --abstr_cl_out                          false
% 3.35/0.96  
% 3.35/0.96  ------ Global Options
% 3.35/0.96  
% 3.35/0.96  --schedule                              default
% 3.35/0.96  --add_important_lit                     false
% 3.35/0.96  --prop_solver_per_cl                    1000
% 3.35/0.96  --min_unsat_core                        false
% 3.35/0.96  --soft_assumptions                      false
% 3.35/0.96  --soft_lemma_size                       3
% 3.35/0.96  --prop_impl_unit_size                   0
% 3.35/0.96  --prop_impl_unit                        []
% 3.35/0.96  --share_sel_clauses                     true
% 3.35/0.96  --reset_solvers                         false
% 3.35/0.96  --bc_imp_inh                            [conj_cone]
% 3.35/0.96  --conj_cone_tolerance                   3.
% 3.35/0.96  --extra_neg_conj                        none
% 3.35/0.96  --large_theory_mode                     true
% 3.35/0.96  --prolific_symb_bound                   200
% 3.35/0.96  --lt_threshold                          2000
% 3.35/0.96  --clause_weak_htbl                      true
% 3.35/0.96  --gc_record_bc_elim                     false
% 3.35/0.96  
% 3.35/0.96  ------ Preprocessing Options
% 3.35/0.96  
% 3.35/0.96  --preprocessing_flag                    true
% 3.35/0.96  --time_out_prep_mult                    0.1
% 3.35/0.96  --splitting_mode                        input
% 3.35/0.96  --splitting_grd                         true
% 3.35/0.96  --splitting_cvd                         false
% 3.35/0.96  --splitting_cvd_svl                     false
% 3.35/0.96  --splitting_nvd                         32
% 3.35/0.96  --sub_typing                            true
% 3.35/0.96  --prep_gs_sim                           true
% 3.35/0.96  --prep_unflatten                        true
% 3.35/0.96  --prep_res_sim                          true
% 3.35/0.96  --prep_upred                            true
% 3.35/0.96  --prep_sem_filter                       exhaustive
% 3.35/0.96  --prep_sem_filter_out                   false
% 3.35/0.96  --pred_elim                             true
% 3.35/0.96  --res_sim_input                         true
% 3.35/0.96  --eq_ax_congr_red                       true
% 3.35/0.96  --pure_diseq_elim                       true
% 3.35/0.96  --brand_transform                       false
% 3.35/0.96  --non_eq_to_eq                          false
% 3.35/0.96  --prep_def_merge                        true
% 3.35/0.96  --prep_def_merge_prop_impl              false
% 3.35/0.96  --prep_def_merge_mbd                    true
% 3.35/0.96  --prep_def_merge_tr_red                 false
% 3.35/0.96  --prep_def_merge_tr_cl                  false
% 3.35/0.96  --smt_preprocessing                     true
% 3.35/0.96  --smt_ac_axioms                         fast
% 3.35/0.96  --preprocessed_out                      false
% 3.35/0.96  --preprocessed_stats                    false
% 3.35/0.96  
% 3.35/0.96  ------ Abstraction refinement Options
% 3.35/0.96  
% 3.35/0.96  --abstr_ref                             []
% 3.35/0.96  --abstr_ref_prep                        false
% 3.35/0.96  --abstr_ref_until_sat                   false
% 3.35/0.96  --abstr_ref_sig_restrict                funpre
% 3.35/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.96  --abstr_ref_under                       []
% 3.35/0.96  
% 3.35/0.96  ------ SAT Options
% 3.35/0.96  
% 3.35/0.96  --sat_mode                              false
% 3.35/0.96  --sat_fm_restart_options                ""
% 3.35/0.96  --sat_gr_def                            false
% 3.35/0.96  --sat_epr_types                         true
% 3.35/0.96  --sat_non_cyclic_types                  false
% 3.35/0.96  --sat_finite_models                     false
% 3.35/0.96  --sat_fm_lemmas                         false
% 3.35/0.96  --sat_fm_prep                           false
% 3.35/0.96  --sat_fm_uc_incr                        true
% 3.35/0.96  --sat_out_model                         small
% 3.35/0.96  --sat_out_clauses                       false
% 3.35/0.96  
% 3.35/0.96  ------ QBF Options
% 3.35/0.96  
% 3.35/0.96  --qbf_mode                              false
% 3.35/0.96  --qbf_elim_univ                         false
% 3.35/0.96  --qbf_dom_inst                          none
% 3.35/0.96  --qbf_dom_pre_inst                      false
% 3.35/0.96  --qbf_sk_in                             false
% 3.35/0.96  --qbf_pred_elim                         true
% 3.35/0.96  --qbf_split                             512
% 3.35/0.96  
% 3.35/0.96  ------ BMC1 Options
% 3.35/0.96  
% 3.35/0.96  --bmc1_incremental                      false
% 3.35/0.96  --bmc1_axioms                           reachable_all
% 3.35/0.96  --bmc1_min_bound                        0
% 3.35/0.96  --bmc1_max_bound                        -1
% 3.35/0.96  --bmc1_max_bound_default                -1
% 3.35/0.96  --bmc1_symbol_reachability              true
% 3.35/0.96  --bmc1_property_lemmas                  false
% 3.35/0.96  --bmc1_k_induction                      false
% 3.35/0.96  --bmc1_non_equiv_states                 false
% 3.35/0.96  --bmc1_deadlock                         false
% 3.35/0.96  --bmc1_ucm                              false
% 3.35/0.96  --bmc1_add_unsat_core                   none
% 3.35/0.96  --bmc1_unsat_core_children              false
% 3.35/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.96  --bmc1_out_stat                         full
% 3.35/0.96  --bmc1_ground_init                      false
% 3.35/0.96  --bmc1_pre_inst_next_state              false
% 3.35/0.96  --bmc1_pre_inst_state                   false
% 3.35/0.96  --bmc1_pre_inst_reach_state             false
% 3.35/0.96  --bmc1_out_unsat_core                   false
% 3.35/0.96  --bmc1_aig_witness_out                  false
% 3.35/0.96  --bmc1_verbose                          false
% 3.35/0.96  --bmc1_dump_clauses_tptp                false
% 3.35/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.96  --bmc1_dump_file                        -
% 3.35/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.96  --bmc1_ucm_extend_mode                  1
% 3.35/0.96  --bmc1_ucm_init_mode                    2
% 3.35/0.96  --bmc1_ucm_cone_mode                    none
% 3.35/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.96  --bmc1_ucm_relax_model                  4
% 3.35/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.96  --bmc1_ucm_layered_model                none
% 3.35/0.96  --bmc1_ucm_max_lemma_size               10
% 3.35/0.96  
% 3.35/0.96  ------ AIG Options
% 3.35/0.96  
% 3.35/0.96  --aig_mode                              false
% 3.35/0.96  
% 3.35/0.96  ------ Instantiation Options
% 3.35/0.96  
% 3.35/0.96  --instantiation_flag                    true
% 3.35/0.96  --inst_sos_flag                         false
% 3.35/0.96  --inst_sos_phase                        true
% 3.35/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.96  --inst_lit_sel_side                     none
% 3.35/0.96  --inst_solver_per_active                1400
% 3.35/0.96  --inst_solver_calls_frac                1.
% 3.35/0.96  --inst_passive_queue_type               priority_queues
% 3.35/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.96  --inst_passive_queues_freq              [25;2]
% 3.35/0.96  --inst_dismatching                      true
% 3.35/0.96  --inst_eager_unprocessed_to_passive     true
% 3.35/0.96  --inst_prop_sim_given                   true
% 3.35/0.96  --inst_prop_sim_new                     false
% 3.35/0.96  --inst_subs_new                         false
% 3.35/0.96  --inst_eq_res_simp                      false
% 3.35/0.96  --inst_subs_given                       false
% 3.35/0.96  --inst_orphan_elimination               true
% 3.35/0.96  --inst_learning_loop_flag               true
% 3.35/0.96  --inst_learning_start                   3000
% 3.35/0.96  --inst_learning_factor                  2
% 3.35/0.96  --inst_start_prop_sim_after_learn       3
% 3.35/0.96  --inst_sel_renew                        solver
% 3.35/0.96  --inst_lit_activity_flag                true
% 3.35/0.96  --inst_restr_to_given                   false
% 3.35/0.96  --inst_activity_threshold               500
% 3.35/0.96  --inst_out_proof                        true
% 3.35/0.96  
% 3.35/0.96  ------ Resolution Options
% 3.35/0.96  
% 3.35/0.96  --resolution_flag                       false
% 3.35/0.96  --res_lit_sel                           adaptive
% 3.35/0.96  --res_lit_sel_side                      none
% 3.35/0.96  --res_ordering                          kbo
% 3.35/0.96  --res_to_prop_solver                    active
% 3.35/0.96  --res_prop_simpl_new                    false
% 3.35/0.96  --res_prop_simpl_given                  true
% 3.35/0.96  --res_passive_queue_type                priority_queues
% 3.35/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.96  --res_passive_queues_freq               [15;5]
% 3.35/0.96  --res_forward_subs                      full
% 3.35/0.96  --res_backward_subs                     full
% 3.35/0.96  --res_forward_subs_resolution           true
% 3.35/0.96  --res_backward_subs_resolution          true
% 3.35/0.96  --res_orphan_elimination                true
% 3.35/0.96  --res_time_limit                        2.
% 3.35/0.96  --res_out_proof                         true
% 3.35/0.96  
% 3.35/0.96  ------ Superposition Options
% 3.35/0.96  
% 3.35/0.96  --superposition_flag                    true
% 3.35/0.96  --sup_passive_queue_type                priority_queues
% 3.35/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.96  --demod_completeness_check              fast
% 3.35/0.96  --demod_use_ground                      true
% 3.35/0.96  --sup_to_prop_solver                    passive
% 3.35/0.96  --sup_prop_simpl_new                    true
% 3.35/0.96  --sup_prop_simpl_given                  true
% 3.35/0.96  --sup_fun_splitting                     false
% 3.35/0.96  --sup_smt_interval                      50000
% 3.35/0.96  
% 3.35/0.96  ------ Superposition Simplification Setup
% 3.35/0.96  
% 3.35/0.96  --sup_indices_passive                   []
% 3.35/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.96  --sup_full_bw                           [BwDemod]
% 3.35/0.96  --sup_immed_triv                        [TrivRules]
% 3.35/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.96  --sup_immed_bw_main                     []
% 3.35/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.96  
% 3.35/0.96  ------ Combination Options
% 3.35/0.96  
% 3.35/0.96  --comb_res_mult                         3
% 3.35/0.96  --comb_sup_mult                         2
% 3.35/0.96  --comb_inst_mult                        10
% 3.35/0.96  
% 3.35/0.96  ------ Debug Options
% 3.35/0.96  
% 3.35/0.96  --dbg_backtrace                         false
% 3.35/0.96  --dbg_dump_prop_clauses                 false
% 3.35/0.96  --dbg_dump_prop_clauses_file            -
% 3.35/0.96  --dbg_out_stat                          false
% 3.35/0.96  
% 3.35/0.96  
% 3.35/0.96  
% 3.35/0.96  
% 3.35/0.96  ------ Proving...
% 3.35/0.96  
% 3.35/0.96  
% 3.35/0.96  % SZS status Theorem for theBenchmark.p
% 3.35/0.96  
% 3.35/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/0.96  
% 3.35/0.96  fof(f1,axiom,(
% 3.35/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 3.35/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.96  
% 3.35/0.96  fof(f6,plain,(
% 3.35/0.96    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 3.35/0.96    inference(ennf_transformation,[],[f1])).
% 3.35/0.96  
% 3.35/0.96  fof(f12,plain,(
% 3.35/0.96    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.35/0.96    inference(nnf_transformation,[],[f6])).
% 3.35/0.96  
% 3.35/0.96  fof(f13,plain,(
% 3.35/0.96    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.35/0.96    inference(rectify,[],[f12])).
% 3.35/0.96  
% 3.35/0.96  fof(f14,plain,(
% 3.35/0.96    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)))),
% 3.35/0.96    introduced(choice_axiom,[])).
% 3.35/0.96  
% 3.35/0.96  fof(f15,plain,(
% 3.35/0.96    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.35/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 3.35/0.96  
% 3.35/0.96  fof(f27,plain,(
% 3.35/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 3.35/0.96    inference(cnf_transformation,[],[f15])).
% 3.35/0.96  
% 3.35/0.96  fof(f28,plain,(
% 3.35/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 3.35/0.96    inference(cnf_transformation,[],[f15])).
% 3.35/0.96  
% 3.35/0.96  fof(f4,conjecture,(
% 3.35/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))))))),
% 3.35/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.96  
% 3.35/0.96  fof(f5,negated_conjecture,(
% 3.35/0.96    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))))))),
% 3.35/0.96    inference(negated_conjecture,[],[f4])).
% 3.35/0.96  
% 3.35/0.96  fof(f10,plain,(
% 3.35/0.96    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.35/0.96    inference(ennf_transformation,[],[f5])).
% 3.35/0.96  
% 3.35/0.96  fof(f11,plain,(
% 3.35/0.96    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.35/0.96    inference(flattening,[],[f10])).
% 3.35/0.96  
% 3.35/0.96  fof(f24,plain,(
% 3.35/0.96    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(X0,sK8),k5_relat_1(X1,sK8)) & r1_tarski(X0,X1) & v1_relat_1(sK8))) )),
% 3.35/0.96    introduced(choice_axiom,[])).
% 3.35/0.96  
% 3.35/0.96  fof(f23,plain,(
% 3.35/0.96    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(sK7,X2)) & r1_tarski(X0,sK7) & v1_relat_1(X2)) & v1_relat_1(sK7))) )),
% 3.35/0.96    introduced(choice_axiom,[])).
% 3.35/0.96  
% 3.35/0.96  fof(f22,plain,(
% 3.35/0.96    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK6,X2),k5_relat_1(X1,X2)) & r1_tarski(sK6,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK6))),
% 3.35/0.96    introduced(choice_axiom,[])).
% 3.35/0.96  
% 3.35/0.96  fof(f25,plain,(
% 3.35/0.96    ((~r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK8)) & r1_tarski(sK6,sK7) & v1_relat_1(sK8)) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 3.35/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f11,f24,f23,f22])).
% 3.35/0.96  
% 3.35/0.96  fof(f39,plain,(
% 3.35/0.96    r1_tarski(sK6,sK7)),
% 3.35/0.96    inference(cnf_transformation,[],[f25])).
% 3.35/0.96  
% 3.35/0.96  fof(f2,axiom,(
% 3.35/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.35/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.96  
% 3.35/0.96  fof(f7,plain,(
% 3.35/0.96    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.35/0.96    inference(ennf_transformation,[],[f2])).
% 3.35/0.96  
% 3.35/0.96  fof(f16,plain,(
% 3.35/0.96    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.35/0.96    inference(nnf_transformation,[],[f7])).
% 3.35/0.96  
% 3.35/0.96  fof(f17,plain,(
% 3.35/0.96    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.35/0.96    inference(rectify,[],[f16])).
% 3.35/0.96  
% 3.35/0.96  fof(f20,plain,(
% 3.35/0.96    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 3.35/0.96    introduced(choice_axiom,[])).
% 3.35/0.96  
% 3.35/0.96  fof(f19,plain,(
% 3.35/0.96    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 3.35/0.96    introduced(choice_axiom,[])).
% 3.35/0.96  
% 3.35/0.96  fof(f18,plain,(
% 3.35/0.96    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 3.35/0.96    introduced(choice_axiom,[])).
% 3.35/0.96  
% 3.35/0.96  fof(f21,plain,(
% 3.35/0.96    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.35/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f20,f19,f18])).
% 3.35/0.96  
% 3.35/0.96  fof(f29,plain,(
% 3.35/0.96    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.35/0.96    inference(cnf_transformation,[],[f21])).
% 3.35/0.96  
% 3.35/0.96  fof(f43,plain,(
% 3.35/0.96    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.35/0.96    inference(equality_resolution,[],[f29])).
% 3.35/0.96  
% 3.35/0.96  fof(f3,axiom,(
% 3.35/0.96    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.35/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.96  
% 3.35/0.96  fof(f8,plain,(
% 3.35/0.96    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.35/0.96    inference(ennf_transformation,[],[f3])).
% 3.35/0.96  
% 3.35/0.96  fof(f9,plain,(
% 3.35/0.96    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.35/0.96    inference(flattening,[],[f8])).
% 3.35/0.96  
% 3.35/0.96  fof(f35,plain,(
% 3.35/0.96    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.35/0.96    inference(cnf_transformation,[],[f9])).
% 3.35/0.96  
% 3.35/0.96  fof(f26,plain,(
% 3.35/0.96    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 3.35/0.96    inference(cnf_transformation,[],[f15])).
% 3.35/0.96  
% 3.35/0.96  fof(f36,plain,(
% 3.35/0.96    v1_relat_1(sK6)),
% 3.35/0.96    inference(cnf_transformation,[],[f25])).
% 3.35/0.96  
% 3.35/0.96  fof(f37,plain,(
% 3.35/0.96    v1_relat_1(sK7)),
% 3.35/0.96    inference(cnf_transformation,[],[f25])).
% 3.35/0.96  
% 3.35/0.96  fof(f30,plain,(
% 3.35/0.96    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.35/0.96    inference(cnf_transformation,[],[f21])).
% 3.35/0.96  
% 3.35/0.96  fof(f42,plain,(
% 3.35/0.96    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.35/0.96    inference(equality_resolution,[],[f30])).
% 3.35/0.96  
% 3.35/0.96  fof(f31,plain,(
% 3.35/0.96    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.35/0.96    inference(cnf_transformation,[],[f21])).
% 3.35/0.96  
% 3.35/0.96  fof(f41,plain,(
% 3.35/0.96    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.35/0.96    inference(equality_resolution,[],[f31])).
% 3.35/0.96  
% 3.35/0.96  fof(f40,plain,(
% 3.35/0.96    ~r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK8))),
% 3.35/0.96    inference(cnf_transformation,[],[f25])).
% 3.35/0.96  
% 3.35/0.96  fof(f38,plain,(
% 3.35/0.96    v1_relat_1(sK8)),
% 3.35/0.96    inference(cnf_transformation,[],[f25])).
% 3.35/0.96  
% 3.35/0.96  cnf(c_1,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
% 3.35/0.96      | r1_tarski(X0,X1)
% 3.35/0.96      | ~ v1_relat_1(X0) ),
% 3.35/0.96      inference(cnf_transformation,[],[f27]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_267,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(sK0(X0_42,X1_42),sK1(X0_42,X1_42)),X0_42)
% 3.35/0.96      | r1_tarski(X0_42,X1_42)
% 3.35/0.96      | ~ v1_relat_1(X0_42) ),
% 3.35/0.96      inference(subtyping,[status(esa)],[c_1]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_562,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(sK0(X0_42,X1_42),sK1(X0_42,X1_42)),X0_42) = iProver_top
% 3.35/0.96      | r1_tarski(X0_42,X1_42) = iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_0,plain,
% 3.35/0.96      ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
% 3.35/0.96      | r1_tarski(X0,X1)
% 3.35/0.96      | ~ v1_relat_1(X0) ),
% 3.35/0.96      inference(cnf_transformation,[],[f28]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_268,plain,
% 3.35/0.96      ( ~ r2_hidden(k4_tarski(sK0(X0_42,X1_42),sK1(X0_42,X1_42)),X1_42)
% 3.35/0.96      | r1_tarski(X0_42,X1_42)
% 3.35/0.96      | ~ v1_relat_1(X0_42) ),
% 3.35/0.96      inference(subtyping,[status(esa)],[c_0]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_561,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(sK0(X0_42,X1_42),sK1(X0_42,X1_42)),X1_42) != iProver_top
% 3.35/0.96      | r1_tarski(X0_42,X1_42) = iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_991,plain,
% 3.35/0.96      ( r1_tarski(X0_42,X0_42) = iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top ),
% 3.35/0.96      inference(superposition,[status(thm)],[c_562,c_561]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_11,negated_conjecture,
% 3.35/0.96      ( r1_tarski(sK6,sK7) ),
% 3.35/0.96      inference(cnf_transformation,[],[f39]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_257,negated_conjecture,
% 3.35/0.96      ( r1_tarski(sK6,sK7) ),
% 3.35/0.96      inference(subtyping,[status(esa)],[c_11]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_572,plain,
% 3.35/0.96      ( r1_tarski(sK6,sK7) = iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_8,plain,
% 3.35/0.96      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 3.35/0.96      | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
% 3.35/0.96      | ~ v1_relat_1(X2)
% 3.35/0.96      | ~ v1_relat_1(X3)
% 3.35/0.96      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 3.35/0.96      inference(cnf_transformation,[],[f43]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_260,plain,
% 3.35/0.96      ( ~ r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42))
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,sK5(X0_42,X1_42,X0_44,X1_44)),X0_42)
% 3.35/0.96      | ~ v1_relat_1(X0_42)
% 3.35/0.96      | ~ v1_relat_1(X1_42)
% 3.35/0.96      | ~ v1_relat_1(k5_relat_1(X0_42,X1_42)) ),
% 3.35/0.96      inference(subtyping,[status(esa)],[c_8]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_569,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,sK5(X0_42,X1_42,X0_44,X1_44)),X0_42) = iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(k5_relat_1(X0_42,X1_42)) != iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_9,plain,
% 3.35/0.96      ( ~ v1_relat_1(X0)
% 3.35/0.96      | ~ v1_relat_1(X1)
% 3.35/0.96      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 3.35/0.96      inference(cnf_transformation,[],[f35]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_259,plain,
% 3.35/0.96      ( ~ v1_relat_1(X0_42)
% 3.35/0.96      | ~ v1_relat_1(X1_42)
% 3.35/0.96      | v1_relat_1(k5_relat_1(X0_42,X1_42)) ),
% 3.35/0.96      inference(subtyping,[status(esa)],[c_9]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_570,plain,
% 3.35/0.96      ( v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(k5_relat_1(X0_42,X1_42)) = iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_259]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_627,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,sK5(X0_42,X1_42,X0_44,X1_44)),X0_42) = iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top ),
% 3.35/0.96      inference(forward_subsumption_resolution,
% 3.35/0.96                [status(thm)],
% 3.35/0.96                [c_569,c_570]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_2,plain,
% 3.35/0.96      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.35/0.96      | r2_hidden(k4_tarski(X0,X1),X3)
% 3.35/0.96      | ~ r1_tarski(X2,X3)
% 3.35/0.96      | ~ v1_relat_1(X2) ),
% 3.35/0.96      inference(cnf_transformation,[],[f26]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_266,plain,
% 3.35/0.96      ( ~ r2_hidden(k4_tarski(X0_44,X1_44),X0_42)
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,X1_44),X1_42)
% 3.35/0.96      | ~ r1_tarski(X0_42,X1_42)
% 3.35/0.96      | ~ v1_relat_1(X0_42) ),
% 3.35/0.96      inference(subtyping,[status(esa)],[c_2]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_563,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),X0_42) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,X1_44),X1_42) = iProver_top
% 3.35/0.96      | r1_tarski(X0_42,X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_1414,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,sK5(X0_42,X1_42,X0_44,X1_44)),X2_42) = iProver_top
% 3.35/0.96      | r1_tarski(X0_42,X2_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top ),
% 3.35/0.96      inference(superposition,[status(thm)],[c_627,c_563]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_1664,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,sK5(X0_42,X1_42,X0_44,X1_44)),X2_42) = iProver_top
% 3.35/0.96      | r1_tarski(X3_42,X2_42) != iProver_top
% 3.35/0.96      | r1_tarski(X0_42,X3_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X3_42) != iProver_top ),
% 3.35/0.96      inference(superposition,[status(thm)],[c_1414,c_563]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_5521,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(sK6,X0_42)) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,sK5(sK6,X0_42,X0_44,X1_44)),X1_42) = iProver_top
% 3.35/0.96      | r1_tarski(sK7,X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(sK7) != iProver_top
% 3.35/0.96      | v1_relat_1(sK6) != iProver_top ),
% 3.35/0.96      inference(superposition,[status(thm)],[c_572,c_1664]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_14,negated_conjecture,
% 3.35/0.96      ( v1_relat_1(sK6) ),
% 3.35/0.96      inference(cnf_transformation,[],[f36]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_15,plain,
% 3.35/0.96      ( v1_relat_1(sK6) = iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_13,negated_conjecture,
% 3.35/0.96      ( v1_relat_1(sK7) ),
% 3.35/0.96      inference(cnf_transformation,[],[f37]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_16,plain,
% 3.35/0.96      ( v1_relat_1(sK7) = iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_5538,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(sK6,X0_42)) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,sK5(sK6,X0_42,X0_44,X1_44)),X1_42) = iProver_top
% 3.35/0.96      | r1_tarski(sK7,X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top ),
% 3.35/0.96      inference(global_propositional_subsumption,
% 3.35/0.96                [status(thm)],
% 3.35/0.96                [c_5521,c_15,c_16]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_7,plain,
% 3.35/0.96      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 3.35/0.96      | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
% 3.35/0.96      | ~ v1_relat_1(X2)
% 3.35/0.96      | ~ v1_relat_1(X3)
% 3.35/0.96      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 3.35/0.96      inference(cnf_transformation,[],[f42]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_261,plain,
% 3.35/0.96      ( ~ r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42))
% 3.35/0.96      | r2_hidden(k4_tarski(sK5(X0_42,X1_42,X0_44,X1_44),X1_44),X1_42)
% 3.35/0.96      | ~ v1_relat_1(X0_42)
% 3.35/0.96      | ~ v1_relat_1(X1_42)
% 3.35/0.96      | ~ v1_relat_1(k5_relat_1(X0_42,X1_42)) ),
% 3.35/0.96      inference(subtyping,[status(esa)],[c_7]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_568,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(sK5(X0_42,X1_42,X0_44,X1_44),X1_44),X1_42) = iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(k5_relat_1(X0_42,X1_42)) != iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_617,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(sK5(X0_42,X1_42,X0_44,X1_44),X1_44),X1_42) = iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top ),
% 3.35/0.96      inference(forward_subsumption_resolution,
% 3.35/0.96                [status(thm)],
% 3.35/0.96                [c_568,c_570]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_6,plain,
% 3.35/0.96      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.35/0.96      | ~ r2_hidden(k4_tarski(X3,X0),X4)
% 3.35/0.96      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
% 3.35/0.96      | ~ v1_relat_1(X4)
% 3.35/0.96      | ~ v1_relat_1(X2)
% 3.35/0.96      | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
% 3.35/0.96      inference(cnf_transformation,[],[f41]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_262,plain,
% 3.35/0.96      ( ~ r2_hidden(k4_tarski(X0_44,X1_44),X0_42)
% 3.35/0.96      | ~ r2_hidden(k4_tarski(X2_44,X0_44),X1_42)
% 3.35/0.96      | r2_hidden(k4_tarski(X2_44,X1_44),k5_relat_1(X1_42,X0_42))
% 3.35/0.96      | ~ v1_relat_1(X0_42)
% 3.35/0.96      | ~ v1_relat_1(X1_42)
% 3.35/0.96      | ~ v1_relat_1(k5_relat_1(X1_42,X0_42)) ),
% 3.35/0.96      inference(subtyping,[status(esa)],[c_6]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_567,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),X0_42) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X2_44,X0_44),X1_42) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X2_44,X1_44),k5_relat_1(X1_42,X0_42)) = iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(k5_relat_1(X1_42,X0_42)) != iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_638,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),X0_42) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X2_44,X0_44),X1_42) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X2_44,X1_44),k5_relat_1(X1_42,X0_42)) = iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top ),
% 3.35/0.96      inference(forward_subsumption_resolution,
% 3.35/0.96                [status(thm)],
% 3.35/0.96                [c_567,c_570]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_1425,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X2_44,X1_44),k5_relat_1(X2_42,X1_42)) = iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X2_44,sK5(X0_42,X1_42,X0_44,X1_44)),X2_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X2_42) != iProver_top ),
% 3.35/0.96      inference(superposition,[status(thm)],[c_617,c_638]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_5549,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) = iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(sK6,X1_42)) != iProver_top
% 3.35/0.96      | r1_tarski(sK7,X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(sK6) != iProver_top ),
% 3.35/0.96      inference(superposition,[status(thm)],[c_5538,c_1425]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_6267,plain,
% 3.35/0.96      ( v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top
% 3.35/0.96      | r1_tarski(sK7,X0_42) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(sK6,X1_42)) != iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) = iProver_top ),
% 3.35/0.96      inference(global_propositional_subsumption,
% 3.35/0.96                [status(thm)],
% 3.35/0.96                [c_5549,c_15]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_6268,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(X0_42,X1_42)) = iProver_top
% 3.35/0.96      | r2_hidden(k4_tarski(X0_44,X1_44),k5_relat_1(sK6,X1_42)) != iProver_top
% 3.35/0.96      | r1_tarski(sK7,X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top ),
% 3.35/0.96      inference(renaming,[status(thm)],[c_6267]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_6284,plain,
% 3.35/0.96      ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK6,X0_42),X1_42),sK1(k5_relat_1(sK6,X0_42),X1_42)),k5_relat_1(X2_42,X0_42)) = iProver_top
% 3.35/0.96      | r1_tarski(k5_relat_1(sK6,X0_42),X1_42) = iProver_top
% 3.35/0.96      | r1_tarski(sK7,X2_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X2_42) != iProver_top
% 3.35/0.96      | v1_relat_1(k5_relat_1(sK6,X0_42)) != iProver_top ),
% 3.35/0.96      inference(superposition,[status(thm)],[c_562,c_6268]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_10779,plain,
% 3.35/0.96      ( r1_tarski(k5_relat_1(sK6,X0_42),k5_relat_1(X1_42,X0_42)) = iProver_top
% 3.35/0.96      | r1_tarski(sK7,X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X0_42) != iProver_top
% 3.35/0.96      | v1_relat_1(X1_42) != iProver_top
% 3.35/0.96      | v1_relat_1(k5_relat_1(sK6,X0_42)) != iProver_top ),
% 3.35/0.96      inference(superposition,[status(thm)],[c_6284,c_561]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_10,negated_conjecture,
% 3.35/0.96      ( ~ r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK8)) ),
% 3.35/0.96      inference(cnf_transformation,[],[f40]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_258,negated_conjecture,
% 3.35/0.96      ( ~ r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK8)) ),
% 3.35/0.96      inference(subtyping,[status(esa)],[c_10]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_571,plain,
% 3.35/0.96      ( r1_tarski(k5_relat_1(sK6,sK8),k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_10856,plain,
% 3.35/0.96      ( r1_tarski(sK7,sK7) != iProver_top
% 3.35/0.96      | v1_relat_1(k5_relat_1(sK6,sK8)) != iProver_top
% 3.35/0.96      | v1_relat_1(sK7) != iProver_top
% 3.35/0.96      | v1_relat_1(sK8) != iProver_top ),
% 3.35/0.96      inference(superposition,[status(thm)],[c_10779,c_571]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_12,negated_conjecture,
% 3.35/0.96      ( v1_relat_1(sK8) ),
% 3.35/0.96      inference(cnf_transformation,[],[f38]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_17,plain,
% 3.35/0.96      ( v1_relat_1(sK8) = iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_779,plain,
% 3.35/0.96      ( v1_relat_1(k5_relat_1(sK6,sK8))
% 3.35/0.96      | ~ v1_relat_1(sK8)
% 3.35/0.96      | ~ v1_relat_1(sK6) ),
% 3.35/0.96      inference(instantiation,[status(thm)],[c_259]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_780,plain,
% 3.35/0.96      ( v1_relat_1(k5_relat_1(sK6,sK8)) = iProver_top
% 3.35/0.96      | v1_relat_1(sK8) != iProver_top
% 3.35/0.96      | v1_relat_1(sK6) != iProver_top ),
% 3.35/0.96      inference(predicate_to_equality,[status(thm)],[c_779]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_11047,plain,
% 3.35/0.96      ( r1_tarski(sK7,sK7) != iProver_top ),
% 3.35/0.96      inference(global_propositional_subsumption,
% 3.35/0.96                [status(thm)],
% 3.35/0.96                [c_10856,c_15,c_16,c_17,c_780]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(c_11052,plain,
% 3.35/0.96      ( v1_relat_1(sK7) != iProver_top ),
% 3.35/0.96      inference(superposition,[status(thm)],[c_991,c_11047]) ).
% 3.35/0.96  
% 3.35/0.96  cnf(contradiction,plain,
% 3.35/0.96      ( $false ),
% 3.35/0.96      inference(minisat,[status(thm)],[c_11052,c_16]) ).
% 3.35/0.96  
% 3.35/0.96  
% 3.35/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.35/0.96  
% 3.35/0.96  ------                               Statistics
% 3.35/0.96  
% 3.35/0.96  ------ General
% 3.35/0.96  
% 3.35/0.96  abstr_ref_over_cycles:                  0
% 3.35/0.96  abstr_ref_under_cycles:                 0
% 3.35/0.96  gc_basic_clause_elim:                   0
% 3.35/0.96  forced_gc_time:                         0
% 3.35/0.96  parsing_time:                           0.009
% 3.35/0.96  unif_index_cands_time:                  0.
% 3.35/0.96  unif_index_add_time:                    0.
% 3.35/0.96  orderings_time:                         0.
% 3.35/0.96  out_proof_time:                         0.007
% 3.35/0.96  total_time:                             0.333
% 3.35/0.96  num_of_symbols:                         48
% 3.35/0.96  num_of_terms:                           7015
% 3.35/0.96  
% 3.35/0.96  ------ Preprocessing
% 3.35/0.96  
% 3.35/0.96  num_of_splits:                          0
% 3.35/0.96  num_of_split_atoms:                     0
% 3.35/0.96  num_of_reused_defs:                     0
% 3.35/0.96  num_eq_ax_congr_red:                    34
% 3.35/0.96  num_of_sem_filtered_clauses:            1
% 3.35/0.96  num_of_subtypes:                        3
% 3.35/0.96  monotx_restored_types:                  0
% 3.35/0.96  sat_num_of_epr_types:                   0
% 3.35/0.96  sat_num_of_non_cyclic_types:            0
% 3.35/0.96  sat_guarded_non_collapsed_types:        1
% 3.35/0.96  num_pure_diseq_elim:                    0
% 3.35/0.96  simp_replaced_by:                       0
% 3.35/0.96  res_preprocessed:                       64
% 3.35/0.96  prep_upred:                             0
% 3.35/0.96  prep_unflattend:                        10
% 3.35/0.96  smt_new_axioms:                         0
% 3.35/0.96  pred_elim_cands:                        3
% 3.35/0.96  pred_elim:                              0
% 3.35/0.96  pred_elim_cl:                           0
% 3.35/0.96  pred_elim_cycles:                       1
% 3.35/0.96  merged_defs:                            0
% 3.35/0.96  merged_defs_ncl:                        0
% 3.35/0.96  bin_hyper_res:                          0
% 3.35/0.96  prep_cycles:                            3
% 3.35/0.96  pred_elim_time:                         0.002
% 3.35/0.96  splitting_time:                         0.
% 3.35/0.96  sem_filter_time:                        0.
% 3.35/0.96  monotx_time:                            0.
% 3.35/0.96  subtype_inf_time:                       0.
% 3.35/0.96  
% 3.35/0.96  ------ Problem properties
% 3.35/0.96  
% 3.35/0.96  clauses:                                15
% 3.35/0.96  conjectures:                            5
% 3.35/0.96  epr:                                    4
% 3.35/0.96  horn:                                   12
% 3.35/0.96  ground:                                 5
% 3.35/0.96  unary:                                  5
% 3.35/0.96  binary:                                 0
% 3.35/0.96  lits:                                   53
% 3.35/0.96  lits_eq:                                3
% 3.35/0.96  fd_pure:                                0
% 3.35/0.96  fd_pseudo:                              0
% 3.35/0.96  fd_cond:                                0
% 3.35/0.96  fd_pseudo_cond:                         3
% 3.35/0.96  ac_symbols:                             0
% 3.35/0.96  
% 3.35/0.96  ------ Propositional Solver
% 3.35/0.96  
% 3.35/0.96  prop_solver_calls:                      26
% 3.35/0.96  prop_fast_solver_calls:                 947
% 3.35/0.96  smt_solver_calls:                       0
% 3.35/0.96  smt_fast_solver_calls:                  0
% 3.35/0.96  prop_num_of_clauses:                    2420
% 3.35/0.96  prop_preprocess_simplified:             4588
% 3.35/0.96  prop_fo_subsumed:                       61
% 3.35/0.96  prop_solver_time:                       0.
% 3.35/0.96  smt_solver_time:                        0.
% 3.35/0.96  smt_fast_solver_time:                   0.
% 3.35/0.96  prop_fast_solver_time:                  0.
% 3.35/0.96  prop_unsat_core_time:                   0.
% 3.35/0.96  
% 3.35/0.96  ------ QBF
% 3.35/0.96  
% 3.35/0.96  qbf_q_res:                              0
% 3.35/0.96  qbf_num_tautologies:                    0
% 3.35/0.96  qbf_prep_cycles:                        0
% 3.35/0.96  
% 3.35/0.96  ------ BMC1
% 3.35/0.96  
% 3.35/0.96  bmc1_current_bound:                     -1
% 3.35/0.96  bmc1_last_solved_bound:                 -1
% 3.35/0.96  bmc1_unsat_core_size:                   -1
% 3.35/0.96  bmc1_unsat_core_parents_size:           -1
% 3.35/0.96  bmc1_merge_next_fun:                    0
% 3.35/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.35/0.96  
% 3.35/0.96  ------ Instantiation
% 3.35/0.96  
% 3.35/0.96  inst_num_of_clauses:                    450
% 3.35/0.96  inst_num_in_passive:                    144
% 3.35/0.96  inst_num_in_active:                     295
% 3.35/0.96  inst_num_in_unprocessed:                11
% 3.35/0.96  inst_num_of_loops:                      370
% 3.35/0.96  inst_num_of_learning_restarts:          0
% 3.35/0.96  inst_num_moves_active_passive:          71
% 3.35/0.96  inst_lit_activity:                      0
% 3.35/0.96  inst_lit_activity_moves:                0
% 3.35/0.96  inst_num_tautologies:                   0
% 3.35/0.96  inst_num_prop_implied:                  0
% 3.35/0.96  inst_num_existing_simplified:           0
% 3.35/0.96  inst_num_eq_res_simplified:             0
% 3.35/0.96  inst_num_child_elim:                    0
% 3.35/0.96  inst_num_of_dismatching_blockings:      325
% 3.35/0.96  inst_num_of_non_proper_insts:           716
% 3.35/0.96  inst_num_of_duplicates:                 0
% 3.35/0.96  inst_inst_num_from_inst_to_res:         0
% 3.35/0.96  inst_dismatching_checking_time:         0.
% 3.35/0.96  
% 3.35/0.96  ------ Resolution
% 3.35/0.96  
% 3.35/0.96  res_num_of_clauses:                     0
% 3.35/0.96  res_num_in_passive:                     0
% 3.35/0.96  res_num_in_active:                      0
% 3.35/0.96  res_num_of_loops:                       67
% 3.35/0.96  res_forward_subset_subsumed:            82
% 3.35/0.96  res_backward_subset_subsumed:           0
% 3.35/0.96  res_forward_subsumed:                   0
% 3.35/0.96  res_backward_subsumed:                  0
% 3.35/0.96  res_forward_subsumption_resolution:     0
% 3.35/0.96  res_backward_subsumption_resolution:    0
% 3.35/0.96  res_clause_to_clause_subsumption:       5034
% 3.35/0.96  res_orphan_elimination:                 0
% 3.35/0.96  res_tautology_del:                      99
% 3.35/0.96  res_num_eq_res_simplified:              0
% 3.35/0.96  res_num_sel_changes:                    0
% 3.35/0.96  res_moves_from_active_to_pass:          0
% 3.35/0.96  
% 3.35/0.96  ------ Superposition
% 3.35/0.96  
% 3.35/0.96  sup_time_total:                         0.
% 3.35/0.96  sup_time_generating:                    0.
% 3.35/0.96  sup_time_sim_full:                      0.
% 3.35/0.96  sup_time_sim_immed:                     0.
% 3.35/0.96  
% 3.35/0.96  sup_num_of_clauses:                     344
% 3.35/0.96  sup_num_in_active:                      73
% 3.35/0.96  sup_num_in_passive:                     271
% 3.35/0.96  sup_num_of_loops:                       72
% 3.35/0.96  sup_fw_superposition:                   188
% 3.35/0.96  sup_bw_superposition:                   223
% 3.35/0.96  sup_immediate_simplified:               59
% 3.35/0.96  sup_given_eliminated:                   0
% 3.35/0.96  comparisons_done:                       0
% 3.35/0.96  comparisons_avoided:                    0
% 3.35/0.96  
% 3.35/0.96  ------ Simplifications
% 3.35/0.96  
% 3.35/0.96  
% 3.35/0.96  sim_fw_subset_subsumed:                 46
% 3.35/0.96  sim_bw_subset_subsumed:                 0
% 3.35/0.96  sim_fw_subsumed:                        12
% 3.35/0.96  sim_bw_subsumed:                        1
% 3.35/0.96  sim_fw_subsumption_res:                 3
% 3.35/0.96  sim_bw_subsumption_res:                 0
% 3.35/0.96  sim_tautology_del:                      2
% 3.35/0.96  sim_eq_tautology_del:                   0
% 3.35/0.96  sim_eq_res_simp:                        0
% 3.35/0.96  sim_fw_demodulated:                     0
% 3.35/0.96  sim_bw_demodulated:                     0
% 3.35/0.96  sim_light_normalised:                   0
% 3.35/0.96  sim_joinable_taut:                      0
% 3.35/0.96  sim_joinable_simp:                      0
% 3.35/0.96  sim_ac_normalised:                      0
% 3.35/0.96  sim_smt_subsumption:                    0
% 3.35/0.96  
%------------------------------------------------------------------------------
