%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:40 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 192 expanded)
%              Number of clauses        :   54 (  66 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   18
%              Number of atoms          :  364 ( 763 expanded)
%              Number of equality atoms :  131 ( 142 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK7))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X3))
          & r1_tarski(sK4,sK5)
          & r1_tarski(sK6,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK6,sK7)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f17,f30,f29])).

fof(f49,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(sK3(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK1(X0,X1) != sK2(X0,X1)
          | ~ r2_hidden(sK1(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & ( ( sK1(X0,X1) = sK2(X0,X1)
            & r2_hidden(sK1(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK1(X0,X1) != sK2(X0,X1)
              | ~ r2_hidden(sK1(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & ( ( sK1(X0,X1) = sK2(X0,X1)
                & r2_hidden(sK1(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).

fof(f37,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f52,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
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

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f31])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_540,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(k6_relat_1(X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_542,plain,
    ( r2_hidden(sK3(X0,X1),X0) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_553,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1045,plain,
    ( r2_hidden(sK3(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_542,c_553])).

cnf(c_2489,plain,
    ( r2_hidden(sK3(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_553])).

cnf(c_4636,plain,
    ( r2_hidden(sK3(X0,X1),sK5) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_540,c_2489])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_549,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_546,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_607,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_549,c_546])).

cnf(c_12,plain,
    ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
    | r1_tarski(k6_relat_1(X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_543,plain,
    ( r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1400,plain,
    ( r2_hidden(sK3(X0,k6_relat_1(X1)),X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_543])).

cnf(c_1520,plain,
    ( r2_hidden(sK3(X0,k6_relat_1(X1)),X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1400,c_546])).

cnf(c_5008,plain,
    ( r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(k6_relat_1(X0),k6_relat_1(sK5)) = iProver_top
    | v1_relat_1(k6_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4636,c_1520])).

cnf(c_3032,plain,
    ( v1_relat_1(k6_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3033,plain,
    ( v1_relat_1(k6_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3032])).

cnf(c_5111,plain,
    ( r1_tarski(k6_relat_1(X0),k6_relat_1(sK5)) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5008,c_3033])).

cnf(c_5112,plain,
    ( r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(k6_relat_1(X0),k6_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5111])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_538,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_545,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_821,plain,
    ( k5_relat_1(sK7,k6_relat_1(X0)) = k8_relat_1(X0,sK7) ),
    inference(superposition,[status(thm)],[c_538,c_545])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_537,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_822,plain,
    ( k5_relat_1(sK6,k6_relat_1(X0)) = k8_relat_1(X0,sK6) ),
    inference(superposition,[status(thm)],[c_537,c_545])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_544,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1535,plain,
    ( r1_tarski(k8_relat_1(X0,sK6),k5_relat_1(X1,X2)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X2) != iProver_top
    | r1_tarski(sK6,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_822,c_544])).

cnf(c_19,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_36,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2015,plain,
    ( r1_tarski(k8_relat_1(X0,sK6),k5_relat_1(X1,X2)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X2) != iProver_top
    | r1_tarski(sK6,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1535,c_19,c_36])).

cnf(c_2027,plain,
    ( r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X1,sK7)) = iProver_top
    | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) != iProver_top
    | r1_tarski(sK6,sK7) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_2015])).

cnf(c_20,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,plain,
    ( r1_tarski(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2207,plain,
    ( v1_relat_1(k6_relat_1(X1)) != iProver_top
    | r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X1,sK7)) = iProver_top
    | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2027,c_20,c_21])).

cnf(c_2208,plain,
    ( r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X1,sK7)) = iProver_top
    | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2207])).

cnf(c_2216,plain,
    ( r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X1,sK7)) = iProver_top
    | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2208,c_546])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_541,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2220,plain,
    ( r1_tarski(k6_relat_1(sK4),k6_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2216,c_541])).

cnf(c_5123,plain,
    ( r1_tarski(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5112,c_2220])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_554,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_555,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1036,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_555])).

cnf(c_5171,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5123,c_1036])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:17:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.40/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/0.98  
% 2.40/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/0.98  
% 2.40/0.98  ------  iProver source info
% 2.40/0.98  
% 2.40/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.40/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/0.98  git: non_committed_changes: false
% 2.40/0.98  git: last_make_outside_of_git: false
% 2.40/0.98  
% 2.40/0.98  ------ 
% 2.40/0.98  
% 2.40/0.98  ------ Input Options
% 2.40/0.98  
% 2.40/0.98  --out_options                           all
% 2.40/0.98  --tptp_safe_out                         true
% 2.40/0.98  --problem_path                          ""
% 2.40/0.98  --include_path                          ""
% 2.40/0.98  --clausifier                            res/vclausify_rel
% 2.40/0.98  --clausifier_options                    --mode clausify
% 2.40/0.98  --stdin                                 false
% 2.40/0.98  --stats_out                             all
% 2.40/0.98  
% 2.40/0.98  ------ General Options
% 2.40/0.98  
% 2.40/0.98  --fof                                   false
% 2.40/0.98  --time_out_real                         305.
% 2.40/0.98  --time_out_virtual                      -1.
% 2.40/0.98  --symbol_type_check                     false
% 2.40/0.98  --clausify_out                          false
% 2.40/0.98  --sig_cnt_out                           false
% 2.40/0.98  --trig_cnt_out                          false
% 2.40/0.98  --trig_cnt_out_tolerance                1.
% 2.40/0.98  --trig_cnt_out_sk_spl                   false
% 2.40/0.98  --abstr_cl_out                          false
% 2.40/0.98  
% 2.40/0.98  ------ Global Options
% 2.40/0.98  
% 2.40/0.98  --schedule                              default
% 2.40/0.98  --add_important_lit                     false
% 2.40/0.98  --prop_solver_per_cl                    1000
% 2.40/0.98  --min_unsat_core                        false
% 2.40/0.98  --soft_assumptions                      false
% 2.40/0.98  --soft_lemma_size                       3
% 2.40/0.98  --prop_impl_unit_size                   0
% 2.40/0.98  --prop_impl_unit                        []
% 2.40/0.98  --share_sel_clauses                     true
% 2.40/0.98  --reset_solvers                         false
% 2.40/0.98  --bc_imp_inh                            [conj_cone]
% 2.40/0.98  --conj_cone_tolerance                   3.
% 2.40/0.98  --extra_neg_conj                        none
% 2.40/0.98  --large_theory_mode                     true
% 2.40/0.98  --prolific_symb_bound                   200
% 2.40/0.98  --lt_threshold                          2000
% 2.40/0.98  --clause_weak_htbl                      true
% 2.40/0.98  --gc_record_bc_elim                     false
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing Options
% 2.40/0.98  
% 2.40/0.98  --preprocessing_flag                    true
% 2.40/0.98  --time_out_prep_mult                    0.1
% 2.40/0.98  --splitting_mode                        input
% 2.40/0.98  --splitting_grd                         true
% 2.40/0.98  --splitting_cvd                         false
% 2.40/0.98  --splitting_cvd_svl                     false
% 2.40/0.98  --splitting_nvd                         32
% 2.40/0.98  --sub_typing                            true
% 2.40/0.98  --prep_gs_sim                           true
% 2.40/0.98  --prep_unflatten                        true
% 2.40/0.98  --prep_res_sim                          true
% 2.40/0.98  --prep_upred                            true
% 2.40/0.98  --prep_sem_filter                       exhaustive
% 2.40/0.98  --prep_sem_filter_out                   false
% 2.40/0.98  --pred_elim                             true
% 2.40/0.98  --res_sim_input                         true
% 2.40/0.98  --eq_ax_congr_red                       true
% 2.40/0.98  --pure_diseq_elim                       true
% 2.40/0.98  --brand_transform                       false
% 2.40/0.98  --non_eq_to_eq                          false
% 2.40/0.98  --prep_def_merge                        true
% 2.40/0.98  --prep_def_merge_prop_impl              false
% 2.40/0.98  --prep_def_merge_mbd                    true
% 2.40/0.98  --prep_def_merge_tr_red                 false
% 2.40/0.98  --prep_def_merge_tr_cl                  false
% 2.40/0.98  --smt_preprocessing                     true
% 2.40/0.98  --smt_ac_axioms                         fast
% 2.40/0.98  --preprocessed_out                      false
% 2.40/0.98  --preprocessed_stats                    false
% 2.40/0.98  
% 2.40/0.98  ------ Abstraction refinement Options
% 2.40/0.98  
% 2.40/0.98  --abstr_ref                             []
% 2.40/0.98  --abstr_ref_prep                        false
% 2.40/0.98  --abstr_ref_until_sat                   false
% 2.40/0.98  --abstr_ref_sig_restrict                funpre
% 2.40/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.98  --abstr_ref_under                       []
% 2.40/0.98  
% 2.40/0.98  ------ SAT Options
% 2.40/0.98  
% 2.40/0.98  --sat_mode                              false
% 2.40/0.98  --sat_fm_restart_options                ""
% 2.40/0.98  --sat_gr_def                            false
% 2.40/0.98  --sat_epr_types                         true
% 2.40/0.98  --sat_non_cyclic_types                  false
% 2.40/0.98  --sat_finite_models                     false
% 2.40/0.98  --sat_fm_lemmas                         false
% 2.40/0.98  --sat_fm_prep                           false
% 2.40/0.98  --sat_fm_uc_incr                        true
% 2.40/0.98  --sat_out_model                         small
% 2.40/0.98  --sat_out_clauses                       false
% 2.40/0.98  
% 2.40/0.98  ------ QBF Options
% 2.40/0.98  
% 2.40/0.98  --qbf_mode                              false
% 2.40/0.98  --qbf_elim_univ                         false
% 2.40/0.98  --qbf_dom_inst                          none
% 2.40/0.98  --qbf_dom_pre_inst                      false
% 2.40/0.98  --qbf_sk_in                             false
% 2.40/0.98  --qbf_pred_elim                         true
% 2.40/0.98  --qbf_split                             512
% 2.40/0.98  
% 2.40/0.98  ------ BMC1 Options
% 2.40/0.98  
% 2.40/0.98  --bmc1_incremental                      false
% 2.40/0.98  --bmc1_axioms                           reachable_all
% 2.40/0.98  --bmc1_min_bound                        0
% 2.40/0.98  --bmc1_max_bound                        -1
% 2.40/0.98  --bmc1_max_bound_default                -1
% 2.40/0.98  --bmc1_symbol_reachability              true
% 2.40/0.98  --bmc1_property_lemmas                  false
% 2.40/0.98  --bmc1_k_induction                      false
% 2.40/0.98  --bmc1_non_equiv_states                 false
% 2.40/0.98  --bmc1_deadlock                         false
% 2.40/0.98  --bmc1_ucm                              false
% 2.40/0.98  --bmc1_add_unsat_core                   none
% 2.40/0.98  --bmc1_unsat_core_children              false
% 2.40/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.98  --bmc1_out_stat                         full
% 2.40/0.98  --bmc1_ground_init                      false
% 2.40/0.98  --bmc1_pre_inst_next_state              false
% 2.40/0.98  --bmc1_pre_inst_state                   false
% 2.40/0.98  --bmc1_pre_inst_reach_state             false
% 2.40/0.98  --bmc1_out_unsat_core                   false
% 2.40/0.98  --bmc1_aig_witness_out                  false
% 2.40/0.98  --bmc1_verbose                          false
% 2.40/0.98  --bmc1_dump_clauses_tptp                false
% 2.40/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.98  --bmc1_dump_file                        -
% 2.40/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.98  --bmc1_ucm_extend_mode                  1
% 2.40/0.98  --bmc1_ucm_init_mode                    2
% 2.40/0.98  --bmc1_ucm_cone_mode                    none
% 2.40/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.98  --bmc1_ucm_relax_model                  4
% 2.40/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.98  --bmc1_ucm_layered_model                none
% 2.40/0.98  --bmc1_ucm_max_lemma_size               10
% 2.40/0.98  
% 2.40/0.98  ------ AIG Options
% 2.40/0.98  
% 2.40/0.98  --aig_mode                              false
% 2.40/0.98  
% 2.40/0.98  ------ Instantiation Options
% 2.40/0.98  
% 2.40/0.98  --instantiation_flag                    true
% 2.40/0.98  --inst_sos_flag                         false
% 2.40/0.98  --inst_sos_phase                        true
% 2.40/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel_side                     num_symb
% 2.40/0.98  --inst_solver_per_active                1400
% 2.40/0.98  --inst_solver_calls_frac                1.
% 2.40/0.98  --inst_passive_queue_type               priority_queues
% 2.40/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.98  --inst_passive_queues_freq              [25;2]
% 2.40/0.98  --inst_dismatching                      true
% 2.40/0.98  --inst_eager_unprocessed_to_passive     true
% 2.40/0.98  --inst_prop_sim_given                   true
% 2.40/0.98  --inst_prop_sim_new                     false
% 2.40/0.98  --inst_subs_new                         false
% 2.40/0.98  --inst_eq_res_simp                      false
% 2.40/0.98  --inst_subs_given                       false
% 2.40/0.98  --inst_orphan_elimination               true
% 2.40/0.98  --inst_learning_loop_flag               true
% 2.40/0.98  --inst_learning_start                   3000
% 2.40/0.98  --inst_learning_factor                  2
% 2.40/0.98  --inst_start_prop_sim_after_learn       3
% 2.40/0.98  --inst_sel_renew                        solver
% 2.40/0.98  --inst_lit_activity_flag                true
% 2.40/0.98  --inst_restr_to_given                   false
% 2.40/0.98  --inst_activity_threshold               500
% 2.40/0.98  --inst_out_proof                        true
% 2.40/0.98  
% 2.40/0.98  ------ Resolution Options
% 2.40/0.98  
% 2.40/0.98  --resolution_flag                       true
% 2.40/0.98  --res_lit_sel                           adaptive
% 2.40/0.98  --res_lit_sel_side                      none
% 2.40/0.98  --res_ordering                          kbo
% 2.40/0.98  --res_to_prop_solver                    active
% 2.40/0.98  --res_prop_simpl_new                    false
% 2.40/0.98  --res_prop_simpl_given                  true
% 2.40/0.98  --res_passive_queue_type                priority_queues
% 2.40/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.98  --res_passive_queues_freq               [15;5]
% 2.40/0.98  --res_forward_subs                      full
% 2.40/0.98  --res_backward_subs                     full
% 2.40/0.98  --res_forward_subs_resolution           true
% 2.40/0.98  --res_backward_subs_resolution          true
% 2.40/0.98  --res_orphan_elimination                true
% 2.40/0.98  --res_time_limit                        2.
% 2.40/0.98  --res_out_proof                         true
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Options
% 2.40/0.98  
% 2.40/0.98  --superposition_flag                    true
% 2.40/0.98  --sup_passive_queue_type                priority_queues
% 2.40/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.98  --demod_completeness_check              fast
% 2.40/0.98  --demod_use_ground                      true
% 2.40/0.98  --sup_to_prop_solver                    passive
% 2.40/0.98  --sup_prop_simpl_new                    true
% 2.40/0.98  --sup_prop_simpl_given                  true
% 2.40/0.98  --sup_fun_splitting                     false
% 2.40/0.98  --sup_smt_interval                      50000
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Simplification Setup
% 2.40/0.98  
% 2.40/0.98  --sup_indices_passive                   []
% 2.40/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_full_bw                           [BwDemod]
% 2.40/0.98  --sup_immed_triv                        [TrivRules]
% 2.40/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_immed_bw_main                     []
% 2.40/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  
% 2.40/0.98  ------ Combination Options
% 2.40/0.98  
% 2.40/0.98  --comb_res_mult                         3
% 2.40/0.98  --comb_sup_mult                         2
% 2.40/0.98  --comb_inst_mult                        10
% 2.40/0.98  
% 2.40/0.98  ------ Debug Options
% 2.40/0.98  
% 2.40/0.98  --dbg_backtrace                         false
% 2.40/0.98  --dbg_dump_prop_clauses                 false
% 2.40/0.98  --dbg_dump_prop_clauses_file            -
% 2.40/0.98  --dbg_out_stat                          false
% 2.40/0.98  ------ Parsing...
% 2.40/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/0.98  ------ Proving...
% 2.40/0.98  ------ Problem Properties 
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  clauses                                 19
% 2.40/0.98  conjectures                             5
% 2.40/0.98  EPR                                     5
% 2.40/0.98  Horn                                    15
% 2.40/0.98  unary                                   6
% 2.40/0.98  binary                                  3
% 2.40/0.98  lits                                    50
% 2.40/0.98  lits eq                                 7
% 2.40/0.98  fd_pure                                 0
% 2.40/0.98  fd_pseudo                               0
% 2.40/0.98  fd_cond                                 0
% 2.40/0.98  fd_pseudo_cond                          4
% 2.40/0.98  AC symbols                              0
% 2.40/0.98  
% 2.40/0.98  ------ Schedule dynamic 5 is on 
% 2.40/0.98  
% 2.40/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  ------ 
% 2.40/0.98  Current options:
% 2.40/0.98  ------ 
% 2.40/0.98  
% 2.40/0.98  ------ Input Options
% 2.40/0.98  
% 2.40/0.98  --out_options                           all
% 2.40/0.98  --tptp_safe_out                         true
% 2.40/0.98  --problem_path                          ""
% 2.40/0.98  --include_path                          ""
% 2.40/0.98  --clausifier                            res/vclausify_rel
% 2.40/0.98  --clausifier_options                    --mode clausify
% 2.40/0.98  --stdin                                 false
% 2.40/0.98  --stats_out                             all
% 2.40/0.98  
% 2.40/0.98  ------ General Options
% 2.40/0.98  
% 2.40/0.98  --fof                                   false
% 2.40/0.98  --time_out_real                         305.
% 2.40/0.98  --time_out_virtual                      -1.
% 2.40/0.98  --symbol_type_check                     false
% 2.40/0.98  --clausify_out                          false
% 2.40/0.98  --sig_cnt_out                           false
% 2.40/0.98  --trig_cnt_out                          false
% 2.40/0.98  --trig_cnt_out_tolerance                1.
% 2.40/0.98  --trig_cnt_out_sk_spl                   false
% 2.40/0.98  --abstr_cl_out                          false
% 2.40/0.98  
% 2.40/0.98  ------ Global Options
% 2.40/0.98  
% 2.40/0.98  --schedule                              default
% 2.40/0.98  --add_important_lit                     false
% 2.40/0.98  --prop_solver_per_cl                    1000
% 2.40/0.98  --min_unsat_core                        false
% 2.40/0.98  --soft_assumptions                      false
% 2.40/0.98  --soft_lemma_size                       3
% 2.40/0.98  --prop_impl_unit_size                   0
% 2.40/0.98  --prop_impl_unit                        []
% 2.40/0.98  --share_sel_clauses                     true
% 2.40/0.98  --reset_solvers                         false
% 2.40/0.98  --bc_imp_inh                            [conj_cone]
% 2.40/0.98  --conj_cone_tolerance                   3.
% 2.40/0.98  --extra_neg_conj                        none
% 2.40/0.98  --large_theory_mode                     true
% 2.40/0.98  --prolific_symb_bound                   200
% 2.40/0.98  --lt_threshold                          2000
% 2.40/0.98  --clause_weak_htbl                      true
% 2.40/0.98  --gc_record_bc_elim                     false
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing Options
% 2.40/0.98  
% 2.40/0.98  --preprocessing_flag                    true
% 2.40/0.98  --time_out_prep_mult                    0.1
% 2.40/0.98  --splitting_mode                        input
% 2.40/0.98  --splitting_grd                         true
% 2.40/0.98  --splitting_cvd                         false
% 2.40/0.98  --splitting_cvd_svl                     false
% 2.40/0.98  --splitting_nvd                         32
% 2.40/0.98  --sub_typing                            true
% 2.40/0.98  --prep_gs_sim                           true
% 2.40/0.98  --prep_unflatten                        true
% 2.40/0.98  --prep_res_sim                          true
% 2.40/0.98  --prep_upred                            true
% 2.40/0.98  --prep_sem_filter                       exhaustive
% 2.40/0.98  --prep_sem_filter_out                   false
% 2.40/0.98  --pred_elim                             true
% 2.40/0.98  --res_sim_input                         true
% 2.40/0.98  --eq_ax_congr_red                       true
% 2.40/0.98  --pure_diseq_elim                       true
% 2.40/0.98  --brand_transform                       false
% 2.40/0.98  --non_eq_to_eq                          false
% 2.40/0.98  --prep_def_merge                        true
% 2.40/0.98  --prep_def_merge_prop_impl              false
% 2.40/0.98  --prep_def_merge_mbd                    true
% 2.40/0.98  --prep_def_merge_tr_red                 false
% 2.40/0.98  --prep_def_merge_tr_cl                  false
% 2.40/0.98  --smt_preprocessing                     true
% 2.40/0.98  --smt_ac_axioms                         fast
% 2.40/0.98  --preprocessed_out                      false
% 2.40/0.98  --preprocessed_stats                    false
% 2.40/0.98  
% 2.40/0.98  ------ Abstraction refinement Options
% 2.40/0.98  
% 2.40/0.98  --abstr_ref                             []
% 2.40/0.98  --abstr_ref_prep                        false
% 2.40/0.98  --abstr_ref_until_sat                   false
% 2.40/0.98  --abstr_ref_sig_restrict                funpre
% 2.40/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.98  --abstr_ref_under                       []
% 2.40/0.98  
% 2.40/0.98  ------ SAT Options
% 2.40/0.98  
% 2.40/0.98  --sat_mode                              false
% 2.40/0.98  --sat_fm_restart_options                ""
% 2.40/0.98  --sat_gr_def                            false
% 2.40/0.98  --sat_epr_types                         true
% 2.40/0.98  --sat_non_cyclic_types                  false
% 2.40/0.98  --sat_finite_models                     false
% 2.40/0.98  --sat_fm_lemmas                         false
% 2.40/0.98  --sat_fm_prep                           false
% 2.40/0.98  --sat_fm_uc_incr                        true
% 2.40/0.98  --sat_out_model                         small
% 2.40/0.98  --sat_out_clauses                       false
% 2.40/0.98  
% 2.40/0.98  ------ QBF Options
% 2.40/0.98  
% 2.40/0.98  --qbf_mode                              false
% 2.40/0.98  --qbf_elim_univ                         false
% 2.40/0.98  --qbf_dom_inst                          none
% 2.40/0.98  --qbf_dom_pre_inst                      false
% 2.40/0.98  --qbf_sk_in                             false
% 2.40/0.98  --qbf_pred_elim                         true
% 2.40/0.98  --qbf_split                             512
% 2.40/0.98  
% 2.40/0.98  ------ BMC1 Options
% 2.40/0.98  
% 2.40/0.98  --bmc1_incremental                      false
% 2.40/0.98  --bmc1_axioms                           reachable_all
% 2.40/0.98  --bmc1_min_bound                        0
% 2.40/0.98  --bmc1_max_bound                        -1
% 2.40/0.98  --bmc1_max_bound_default                -1
% 2.40/0.98  --bmc1_symbol_reachability              true
% 2.40/0.98  --bmc1_property_lemmas                  false
% 2.40/0.98  --bmc1_k_induction                      false
% 2.40/0.98  --bmc1_non_equiv_states                 false
% 2.40/0.98  --bmc1_deadlock                         false
% 2.40/0.98  --bmc1_ucm                              false
% 2.40/0.98  --bmc1_add_unsat_core                   none
% 2.40/0.98  --bmc1_unsat_core_children              false
% 2.40/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.98  --bmc1_out_stat                         full
% 2.40/0.98  --bmc1_ground_init                      false
% 2.40/0.98  --bmc1_pre_inst_next_state              false
% 2.40/0.98  --bmc1_pre_inst_state                   false
% 2.40/0.98  --bmc1_pre_inst_reach_state             false
% 2.40/0.98  --bmc1_out_unsat_core                   false
% 2.40/0.98  --bmc1_aig_witness_out                  false
% 2.40/0.98  --bmc1_verbose                          false
% 2.40/0.98  --bmc1_dump_clauses_tptp                false
% 2.40/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.98  --bmc1_dump_file                        -
% 2.40/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.98  --bmc1_ucm_extend_mode                  1
% 2.40/0.98  --bmc1_ucm_init_mode                    2
% 2.40/0.98  --bmc1_ucm_cone_mode                    none
% 2.40/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.98  --bmc1_ucm_relax_model                  4
% 2.40/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.98  --bmc1_ucm_layered_model                none
% 2.40/0.98  --bmc1_ucm_max_lemma_size               10
% 2.40/0.98  
% 2.40/0.98  ------ AIG Options
% 2.40/0.98  
% 2.40/0.98  --aig_mode                              false
% 2.40/0.98  
% 2.40/0.98  ------ Instantiation Options
% 2.40/0.98  
% 2.40/0.98  --instantiation_flag                    true
% 2.40/0.98  --inst_sos_flag                         false
% 2.40/0.98  --inst_sos_phase                        true
% 2.40/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel_side                     none
% 2.40/0.98  --inst_solver_per_active                1400
% 2.40/0.98  --inst_solver_calls_frac                1.
% 2.40/0.98  --inst_passive_queue_type               priority_queues
% 2.40/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.98  --inst_passive_queues_freq              [25;2]
% 2.40/0.98  --inst_dismatching                      true
% 2.40/0.98  --inst_eager_unprocessed_to_passive     true
% 2.40/0.98  --inst_prop_sim_given                   true
% 2.40/0.98  --inst_prop_sim_new                     false
% 2.40/0.98  --inst_subs_new                         false
% 2.40/0.98  --inst_eq_res_simp                      false
% 2.40/0.98  --inst_subs_given                       false
% 2.40/0.98  --inst_orphan_elimination               true
% 2.40/0.98  --inst_learning_loop_flag               true
% 2.40/0.98  --inst_learning_start                   3000
% 2.40/0.98  --inst_learning_factor                  2
% 2.40/0.98  --inst_start_prop_sim_after_learn       3
% 2.40/0.98  --inst_sel_renew                        solver
% 2.40/0.98  --inst_lit_activity_flag                true
% 2.40/0.98  --inst_restr_to_given                   false
% 2.40/0.98  --inst_activity_threshold               500
% 2.40/0.98  --inst_out_proof                        true
% 2.40/0.98  
% 2.40/0.98  ------ Resolution Options
% 2.40/0.98  
% 2.40/0.98  --resolution_flag                       false
% 2.40/0.98  --res_lit_sel                           adaptive
% 2.40/0.98  --res_lit_sel_side                      none
% 2.40/0.98  --res_ordering                          kbo
% 2.40/0.98  --res_to_prop_solver                    active
% 2.40/0.98  --res_prop_simpl_new                    false
% 2.40/0.98  --res_prop_simpl_given                  true
% 2.40/0.98  --res_passive_queue_type                priority_queues
% 2.40/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.98  --res_passive_queues_freq               [15;5]
% 2.40/0.98  --res_forward_subs                      full
% 2.40/0.98  --res_backward_subs                     full
% 2.40/0.98  --res_forward_subs_resolution           true
% 2.40/0.98  --res_backward_subs_resolution          true
% 2.40/0.98  --res_orphan_elimination                true
% 2.40/0.98  --res_time_limit                        2.
% 2.40/0.98  --res_out_proof                         true
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Options
% 2.40/0.98  
% 2.40/0.98  --superposition_flag                    true
% 2.40/0.98  --sup_passive_queue_type                priority_queues
% 2.40/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.98  --demod_completeness_check              fast
% 2.40/0.98  --demod_use_ground                      true
% 2.40/0.98  --sup_to_prop_solver                    passive
% 2.40/0.98  --sup_prop_simpl_new                    true
% 2.40/0.98  --sup_prop_simpl_given                  true
% 2.40/0.98  --sup_fun_splitting                     false
% 2.40/0.98  --sup_smt_interval                      50000
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Simplification Setup
% 2.40/0.98  
% 2.40/0.98  --sup_indices_passive                   []
% 2.40/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_full_bw                           [BwDemod]
% 2.40/0.98  --sup_immed_triv                        [TrivRules]
% 2.40/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_immed_bw_main                     []
% 2.40/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  
% 2.40/0.98  ------ Combination Options
% 2.40/0.98  
% 2.40/0.98  --comb_res_mult                         3
% 2.40/0.98  --comb_sup_mult                         2
% 2.40/0.98  --comb_inst_mult                        10
% 2.40/0.98  
% 2.40/0.98  ------ Debug Options
% 2.40/0.98  
% 2.40/0.98  --dbg_backtrace                         false
% 2.40/0.98  --dbg_dump_prop_clauses                 false
% 2.40/0.98  --dbg_dump_prop_clauses_file            -
% 2.40/0.98  --dbg_out_stat                          false
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  ------ Proving...
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  % SZS status Theorem for theBenchmark.p
% 2.40/0.98  
% 2.40/0.98   Resolution empty clause
% 2.40/0.98  
% 2.40/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/0.98  
% 2.40/0.98  fof(f7,conjecture,(
% 2.40/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f8,negated_conjecture,(
% 2.40/0.98    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 2.40/0.98    inference(negated_conjecture,[],[f7])).
% 2.40/0.98  
% 2.40/0.98  fof(f16,plain,(
% 2.40/0.98    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 2.40/0.98    inference(ennf_transformation,[],[f8])).
% 2.40/0.98  
% 2.40/0.98  fof(f17,plain,(
% 2.40/0.98    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 2.40/0.98    inference(flattening,[],[f16])).
% 2.40/0.98  
% 2.40/0.98  fof(f30,plain,(
% 2.40/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK7)) & r1_tarski(X0,X1) & r1_tarski(X2,sK7) & v1_relat_1(sK7))) )),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f29,plain,(
% 2.40/0.98    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X3)) & r1_tarski(sK4,sK5) & r1_tarski(sK6,X3) & v1_relat_1(X3)) & v1_relat_1(sK6))),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f31,plain,(
% 2.40/0.98    (~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) & r1_tarski(sK4,sK5) & r1_tarski(sK6,sK7) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 2.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f17,f30,f29])).
% 2.40/0.98  
% 2.40/0.98  fof(f49,plain,(
% 2.40/0.98    r1_tarski(sK4,sK5)),
% 2.40/0.98    inference(cnf_transformation,[],[f31])).
% 2.40/0.98  
% 2.40/0.98  fof(f6,axiom,(
% 2.40/0.98    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f14,plain,(
% 2.40/0.98    ! [X0,X1] : ((r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 2.40/0.98    inference(ennf_transformation,[],[f6])).
% 2.40/0.98  
% 2.40/0.98  fof(f15,plain,(
% 2.40/0.98    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 2.40/0.98    inference(flattening,[],[f14])).
% 2.40/0.98  
% 2.40/0.98  fof(f27,plain,(
% 2.40/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f28,plain,(
% 2.40/0.98    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) & r2_hidden(sK3(X0,X1),X0)) | ~v1_relat_1(X1))),
% 2.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f27])).
% 2.40/0.98  
% 2.40/0.98  fof(f44,plain,(
% 2.40/0.98    ( ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | r2_hidden(sK3(X0,X1),X0) | ~v1_relat_1(X1)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f28])).
% 2.40/0.98  
% 2.40/0.98  fof(f1,axiom,(
% 2.40/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f9,plain,(
% 2.40/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.98    inference(ennf_transformation,[],[f1])).
% 2.40/0.98  
% 2.40/0.98  fof(f18,plain,(
% 2.40/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.98    inference(nnf_transformation,[],[f9])).
% 2.40/0.98  
% 2.40/0.98  fof(f19,plain,(
% 2.40/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.98    inference(rectify,[],[f18])).
% 2.40/0.98  
% 2.40/0.98  fof(f20,plain,(
% 2.40/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f21,plain,(
% 2.40/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 2.40/0.98  
% 2.40/0.98  fof(f32,plain,(
% 2.40/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f21])).
% 2.40/0.98  
% 2.40/0.98  fof(f2,axiom,(
% 2.40/0.98    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f10,plain,(
% 2.40/0.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 2.40/0.98    inference(ennf_transformation,[],[f2])).
% 2.40/0.98  
% 2.40/0.98  fof(f22,plain,(
% 2.40/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 2.40/0.98    inference(nnf_transformation,[],[f10])).
% 2.40/0.98  
% 2.40/0.98  fof(f23,plain,(
% 2.40/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 2.40/0.98    inference(flattening,[],[f22])).
% 2.40/0.98  
% 2.40/0.98  fof(f24,plain,(
% 2.40/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 2.40/0.98    inference(rectify,[],[f23])).
% 2.40/0.98  
% 2.40/0.98  fof(f25,plain,(
% 2.40/0.98    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK1(X0,X1) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),X0) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & ((sK1(X0,X1) = sK2(X0,X1) & r2_hidden(sK1(X0,X1),X0)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1))))),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f26,plain,(
% 2.40/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK1(X0,X1) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),X0) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & ((sK1(X0,X1) = sK2(X0,X1) & r2_hidden(sK1(X0,X1),X0)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 2.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).
% 2.40/0.98  
% 2.40/0.98  fof(f37,plain,(
% 2.40/0.98    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f26])).
% 2.40/0.98  
% 2.40/0.98  fof(f51,plain,(
% 2.40/0.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,X5),X1) | ~r2_hidden(X5,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 2.40/0.98    inference(equality_resolution,[],[f37])).
% 2.40/0.98  
% 2.40/0.98  fof(f52,plain,(
% 2.40/0.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) | ~r2_hidden(X5,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.40/0.98    inference(equality_resolution,[],[f51])).
% 2.40/0.98  
% 2.40/0.98  fof(f3,axiom,(
% 2.40/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f41,plain,(
% 2.40/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.40/0.98    inference(cnf_transformation,[],[f3])).
% 2.40/0.98  
% 2.40/0.98  fof(f45,plain,(
% 2.40/0.98    ( ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) | ~v1_relat_1(X1)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f28])).
% 2.40/0.98  
% 2.40/0.98  fof(f47,plain,(
% 2.40/0.98    v1_relat_1(sK7)),
% 2.40/0.98    inference(cnf_transformation,[],[f31])).
% 2.40/0.98  
% 2.40/0.98  fof(f4,axiom,(
% 2.40/0.98    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f11,plain,(
% 2.40/0.98    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 2.40/0.98    inference(ennf_transformation,[],[f4])).
% 2.40/0.98  
% 2.40/0.98  fof(f42,plain,(
% 2.40/0.98    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f11])).
% 2.40/0.98  
% 2.40/0.98  fof(f46,plain,(
% 2.40/0.98    v1_relat_1(sK6)),
% 2.40/0.98    inference(cnf_transformation,[],[f31])).
% 2.40/0.98  
% 2.40/0.98  fof(f5,axiom,(
% 2.40/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f12,plain,(
% 2.40/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.40/0.98    inference(ennf_transformation,[],[f5])).
% 2.40/0.98  
% 2.40/0.98  fof(f13,plain,(
% 2.40/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.40/0.98    inference(flattening,[],[f12])).
% 2.40/0.98  
% 2.40/0.98  fof(f43,plain,(
% 2.40/0.98    ( ! [X2,X0,X3,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f13])).
% 2.40/0.98  
% 2.40/0.98  fof(f48,plain,(
% 2.40/0.98    r1_tarski(sK6,sK7)),
% 2.40/0.98    inference(cnf_transformation,[],[f31])).
% 2.40/0.98  
% 2.40/0.98  fof(f50,plain,(
% 2.40/0.98    ~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),
% 2.40/0.98    inference(cnf_transformation,[],[f31])).
% 2.40/0.98  
% 2.40/0.98  fof(f33,plain,(
% 2.40/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f21])).
% 2.40/0.98  
% 2.40/0.98  fof(f34,plain,(
% 2.40/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f21])).
% 2.40/0.98  
% 2.40/0.98  cnf(c_15,negated_conjecture,
% 2.40/0.98      ( r1_tarski(sK4,sK5) ),
% 2.40/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_540,plain,
% 2.40/0.98      ( r1_tarski(sK4,sK5) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_13,plain,
% 2.40/0.98      ( r2_hidden(sK3(X0,X1),X0)
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),X1)
% 2.40/0.98      | ~ v1_relat_1(X1) ),
% 2.40/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_542,plain,
% 2.40/0.98      ( r2_hidden(sK3(X0,X1),X0) = iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),X1) = iProver_top
% 2.40/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2,plain,
% 2.40/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.40/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_553,plain,
% 2.40/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.40/0.98      | r2_hidden(X0,X2) = iProver_top
% 2.40/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1045,plain,
% 2.40/0.98      ( r2_hidden(sK3(X0,X1),X2) = iProver_top
% 2.40/0.98      | r1_tarski(X0,X2) != iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),X1) = iProver_top
% 2.40/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_542,c_553]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2489,plain,
% 2.40/0.98      ( r2_hidden(sK3(X0,X1),X2) = iProver_top
% 2.40/0.98      | r1_tarski(X0,X3) != iProver_top
% 2.40/0.98      | r1_tarski(X3,X2) != iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),X1) = iProver_top
% 2.40/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_1045,c_553]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_4636,plain,
% 2.40/0.98      ( r2_hidden(sK3(X0,X1),sK5) = iProver_top
% 2.40/0.98      | r1_tarski(X0,sK4) != iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),X1) = iProver_top
% 2.40/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_540,c_2489]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_6,plain,
% 2.40/0.98      ( ~ r2_hidden(X0,X1)
% 2.40/0.98      | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
% 2.40/0.98      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 2.40/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_549,plain,
% 2.40/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.40/0.98      | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top
% 2.40/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_9,plain,
% 2.40/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.40/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_546,plain,
% 2.40/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_607,plain,
% 2.40/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.40/0.98      | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top ),
% 2.40/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_549,c_546]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_12,plain,
% 2.40/0.98      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),X1)
% 2.40/0.98      | ~ v1_relat_1(X1) ),
% 2.40/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_543,plain,
% 2.40/0.98      ( r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) != iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),X1) = iProver_top
% 2.40/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1400,plain,
% 2.40/0.98      ( r2_hidden(sK3(X0,k6_relat_1(X1)),X1) != iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) = iProver_top
% 2.40/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_607,c_543]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1520,plain,
% 2.40/0.98      ( r2_hidden(sK3(X0,k6_relat_1(X1)),X1) != iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) = iProver_top ),
% 2.40/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1400,c_546]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5008,plain,
% 2.40/0.98      ( r1_tarski(X0,sK4) != iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),k6_relat_1(sK5)) = iProver_top
% 2.40/0.98      | v1_relat_1(k6_relat_1(sK5)) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_4636,c_1520]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3032,plain,
% 2.40/0.98      ( v1_relat_1(k6_relat_1(sK5)) ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3033,plain,
% 2.40/0.98      ( v1_relat_1(k6_relat_1(sK5)) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_3032]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5111,plain,
% 2.40/0.98      ( r1_tarski(k6_relat_1(X0),k6_relat_1(sK5)) = iProver_top
% 2.40/0.98      | r1_tarski(X0,sK4) != iProver_top ),
% 2.40/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5008,c_3033]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5112,plain,
% 2.40/0.98      ( r1_tarski(X0,sK4) != iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),k6_relat_1(sK5)) = iProver_top ),
% 2.40/0.98      inference(renaming,[status(thm)],[c_5111]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_17,negated_conjecture,
% 2.40/0.98      ( v1_relat_1(sK7) ),
% 2.40/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_538,plain,
% 2.40/0.98      ( v1_relat_1(sK7) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_10,plain,
% 2.40/0.98      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 2.40/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_545,plain,
% 2.40/0.98      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 2.40/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_821,plain,
% 2.40/0.98      ( k5_relat_1(sK7,k6_relat_1(X0)) = k8_relat_1(X0,sK7) ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_538,c_545]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_18,negated_conjecture,
% 2.40/0.98      ( v1_relat_1(sK6) ),
% 2.40/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_537,plain,
% 2.40/0.98      ( v1_relat_1(sK6) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_822,plain,
% 2.40/0.98      ( k5_relat_1(sK6,k6_relat_1(X0)) = k8_relat_1(X0,sK6) ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_537,c_545]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_11,plain,
% 2.40/0.98      ( ~ r1_tarski(X0,X1)
% 2.40/0.98      | ~ r1_tarski(X2,X3)
% 2.40/0.98      | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
% 2.40/0.98      | ~ v1_relat_1(X1)
% 2.40/0.98      | ~ v1_relat_1(X0)
% 2.40/0.98      | ~ v1_relat_1(X3)
% 2.40/0.98      | ~ v1_relat_1(X2) ),
% 2.40/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_544,plain,
% 2.40/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.40/0.98      | r1_tarski(X2,X3) != iProver_top
% 2.40/0.98      | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) = iProver_top
% 2.40/0.98      | v1_relat_1(X1) != iProver_top
% 2.40/0.98      | v1_relat_1(X0) != iProver_top
% 2.40/0.98      | v1_relat_1(X3) != iProver_top
% 2.40/0.98      | v1_relat_1(X2) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1535,plain,
% 2.40/0.98      ( r1_tarski(k8_relat_1(X0,sK6),k5_relat_1(X1,X2)) = iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),X2) != iProver_top
% 2.40/0.98      | r1_tarski(sK6,X1) != iProver_top
% 2.40/0.98      | v1_relat_1(X1) != iProver_top
% 2.40/0.98      | v1_relat_1(X2) != iProver_top
% 2.40/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 2.40/0.98      | v1_relat_1(sK6) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_822,c_544]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_19,plain,
% 2.40/0.98      ( v1_relat_1(sK6) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_36,plain,
% 2.40/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2015,plain,
% 2.40/0.98      ( r1_tarski(k8_relat_1(X0,sK6),k5_relat_1(X1,X2)) = iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),X2) != iProver_top
% 2.40/0.98      | r1_tarski(sK6,X1) != iProver_top
% 2.40/0.98      | v1_relat_1(X1) != iProver_top
% 2.40/0.98      | v1_relat_1(X2) != iProver_top ),
% 2.40/0.98      inference(global_propositional_subsumption,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_1535,c_19,c_36]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2027,plain,
% 2.40/0.98      ( r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X1,sK7)) = iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) != iProver_top
% 2.40/0.98      | r1_tarski(sK6,sK7) != iProver_top
% 2.40/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top
% 2.40/0.98      | v1_relat_1(sK7) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_821,c_2015]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_20,plain,
% 2.40/0.98      ( v1_relat_1(sK7) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_16,negated_conjecture,
% 2.40/0.98      ( r1_tarski(sK6,sK7) ),
% 2.40/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_21,plain,
% 2.40/0.98      ( r1_tarski(sK6,sK7) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2207,plain,
% 2.40/0.98      ( v1_relat_1(k6_relat_1(X1)) != iProver_top
% 2.40/0.98      | r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X1,sK7)) = iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) != iProver_top ),
% 2.40/0.98      inference(global_propositional_subsumption,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_2027,c_20,c_21]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2208,plain,
% 2.40/0.98      ( r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X1,sK7)) = iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) != iProver_top
% 2.40/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 2.40/0.98      inference(renaming,[status(thm)],[c_2207]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2216,plain,
% 2.40/0.98      ( r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X1,sK7)) = iProver_top
% 2.40/0.98      | r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) != iProver_top ),
% 2.40/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_2208,c_546]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_14,negated_conjecture,
% 2.40/0.98      ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
% 2.40/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_541,plain,
% 2.40/0.98      ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2220,plain,
% 2.40/0.98      ( r1_tarski(k6_relat_1(sK4),k6_relat_1(sK5)) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_2216,c_541]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5123,plain,
% 2.40/0.98      ( r1_tarski(sK4,sK4) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_5112,c_2220]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1,plain,
% 2.40/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.40/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_554,plain,
% 2.40/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.40/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_0,plain,
% 2.40/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.40/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_555,plain,
% 2.40/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.40/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1036,plain,
% 2.40/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_554,c_555]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5171,plain,
% 2.40/0.98      ( $false ),
% 2.40/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_5123,c_1036]) ).
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/0.98  
% 2.40/0.98  ------                               Statistics
% 2.40/0.98  
% 2.40/0.98  ------ General
% 2.40/0.98  
% 2.40/0.98  abstr_ref_over_cycles:                  0
% 2.40/0.98  abstr_ref_under_cycles:                 0
% 2.40/0.98  gc_basic_clause_elim:                   0
% 2.40/0.98  forced_gc_time:                         0
% 2.40/0.98  parsing_time:                           0.009
% 2.40/0.98  unif_index_cands_time:                  0.
% 2.40/0.98  unif_index_add_time:                    0.
% 2.40/0.98  orderings_time:                         0.
% 2.40/0.98  out_proof_time:                         0.007
% 2.40/0.98  total_time:                             0.178
% 2.40/0.98  num_of_symbols:                         46
% 2.40/0.98  num_of_terms:                           4261
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing
% 2.40/0.98  
% 2.40/0.98  num_of_splits:                          0
% 2.40/0.98  num_of_split_atoms:                     0
% 2.40/0.98  num_of_reused_defs:                     0
% 2.40/0.98  num_eq_ax_congr_red:                    20
% 2.40/0.98  num_of_sem_filtered_clauses:            1
% 2.40/0.98  num_of_subtypes:                        0
% 2.40/0.98  monotx_restored_types:                  0
% 2.40/0.98  sat_num_of_epr_types:                   0
% 2.40/0.98  sat_num_of_non_cyclic_types:            0
% 2.40/0.98  sat_guarded_non_collapsed_types:        0
% 2.40/0.98  num_pure_diseq_elim:                    0
% 2.40/0.98  simp_replaced_by:                       0
% 2.40/0.98  res_preprocessed:                       74
% 2.40/0.98  prep_upred:                             0
% 2.40/0.98  prep_unflattend:                        0
% 2.40/0.98  smt_new_axioms:                         0
% 2.40/0.98  pred_elim_cands:                        3
% 2.40/0.98  pred_elim:                              0
% 2.40/0.98  pred_elim_cl:                           0
% 2.40/0.98  pred_elim_cycles:                       1
% 2.40/0.98  merged_defs:                            0
% 2.40/0.98  merged_defs_ncl:                        0
% 2.40/0.98  bin_hyper_res:                          0
% 2.40/0.98  prep_cycles:                            3
% 2.40/0.98  pred_elim_time:                         0.
% 2.40/0.98  splitting_time:                         0.
% 2.40/0.98  sem_filter_time:                        0.
% 2.40/0.98  monotx_time:                            0.001
% 2.40/0.98  subtype_inf_time:                       0.
% 2.40/0.98  
% 2.40/0.98  ------ Problem properties
% 2.40/0.98  
% 2.40/0.98  clauses:                                19
% 2.40/0.98  conjectures:                            5
% 2.40/0.98  epr:                                    5
% 2.40/0.98  horn:                                   15
% 2.40/0.98  ground:                                 5
% 2.40/0.98  unary:                                  6
% 2.40/0.98  binary:                                 3
% 2.40/0.98  lits:                                   50
% 2.40/0.98  lits_eq:                                7
% 2.40/0.98  fd_pure:                                0
% 2.40/0.98  fd_pseudo:                              0
% 2.40/0.98  fd_cond:                                0
% 2.40/0.98  fd_pseudo_cond:                         4
% 2.40/0.98  ac_symbols:                             0
% 2.40/0.98  
% 2.40/0.98  ------ Propositional Solver
% 2.40/0.98  
% 2.40/0.98  prop_solver_calls:                      25
% 2.40/0.98  prop_fast_solver_calls:                 724
% 2.40/0.98  smt_solver_calls:                       0
% 2.40/0.98  smt_fast_solver_calls:                  0
% 2.40/0.98  prop_num_of_clauses:                    1820
% 2.40/0.98  prop_preprocess_simplified:             4318
% 2.40/0.98  prop_fo_subsumed:                       17
% 2.40/0.98  prop_solver_time:                       0.
% 2.40/0.98  smt_solver_time:                        0.
% 2.40/0.98  smt_fast_solver_time:                   0.
% 2.40/0.98  prop_fast_solver_time:                  0.
% 2.40/0.98  prop_unsat_core_time:                   0.
% 2.40/0.98  
% 2.40/0.98  ------ QBF
% 2.40/0.98  
% 2.40/0.98  qbf_q_res:                              0
% 2.40/0.98  qbf_num_tautologies:                    0
% 2.40/0.98  qbf_prep_cycles:                        0
% 2.40/0.98  
% 2.40/0.98  ------ BMC1
% 2.40/0.98  
% 2.40/0.98  bmc1_current_bound:                     -1
% 2.40/0.98  bmc1_last_solved_bound:                 -1
% 2.40/0.98  bmc1_unsat_core_size:                   -1
% 2.40/0.98  bmc1_unsat_core_parents_size:           -1
% 2.40/0.98  bmc1_merge_next_fun:                    0
% 2.40/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.40/0.98  
% 2.40/0.98  ------ Instantiation
% 2.40/0.98  
% 2.40/0.98  inst_num_of_clauses:                    467
% 2.40/0.98  inst_num_in_passive:                    3
% 2.40/0.98  inst_num_in_active:                     271
% 2.40/0.98  inst_num_in_unprocessed:                193
% 2.40/0.98  inst_num_of_loops:                      330
% 2.40/0.98  inst_num_of_learning_restarts:          0
% 2.40/0.98  inst_num_moves_active_passive:          55
% 2.40/0.98  inst_lit_activity:                      0
% 2.40/0.98  inst_lit_activity_moves:                0
% 2.40/0.98  inst_num_tautologies:                   0
% 2.40/0.98  inst_num_prop_implied:                  0
% 2.40/0.98  inst_num_existing_simplified:           0
% 2.40/0.98  inst_num_eq_res_simplified:             0
% 2.40/0.98  inst_num_child_elim:                    0
% 2.40/0.98  inst_num_of_dismatching_blockings:      97
% 2.40/0.98  inst_num_of_non_proper_insts:           481
% 2.40/0.98  inst_num_of_duplicates:                 0
% 2.40/0.98  inst_inst_num_from_inst_to_res:         0
% 2.40/0.98  inst_dismatching_checking_time:         0.
% 2.40/0.98  
% 2.40/0.98  ------ Resolution
% 2.40/0.98  
% 2.40/0.98  res_num_of_clauses:                     0
% 2.40/0.98  res_num_in_passive:                     0
% 2.40/0.98  res_num_in_active:                      0
% 2.40/0.98  res_num_of_loops:                       77
% 2.40/0.98  res_forward_subset_subsumed:            79
% 2.40/0.98  res_backward_subset_subsumed:           0
% 2.40/0.98  res_forward_subsumed:                   0
% 2.40/0.98  res_backward_subsumed:                  0
% 2.40/0.98  res_forward_subsumption_resolution:     0
% 2.40/0.98  res_backward_subsumption_resolution:    0
% 2.40/0.98  res_clause_to_clause_subsumption:       1130
% 2.40/0.98  res_orphan_elimination:                 0
% 2.40/0.98  res_tautology_del:                      50
% 2.40/0.98  res_num_eq_res_simplified:              0
% 2.40/0.98  res_num_sel_changes:                    0
% 2.40/0.98  res_moves_from_active_to_pass:          0
% 2.40/0.98  
% 2.40/0.98  ------ Superposition
% 2.40/0.98  
% 2.40/0.98  sup_time_total:                         0.
% 2.40/0.98  sup_time_generating:                    0.
% 2.40/0.98  sup_time_sim_full:                      0.
% 2.40/0.98  sup_time_sim_immed:                     0.
% 2.40/0.98  
% 2.40/0.98  sup_num_of_clauses:                     134
% 2.40/0.98  sup_num_in_active:                      65
% 2.40/0.98  sup_num_in_passive:                     69
% 2.40/0.98  sup_num_of_loops:                       65
% 2.40/0.98  sup_fw_superposition:                   84
% 2.40/0.98  sup_bw_superposition:                   53
% 2.40/0.98  sup_immediate_simplified:               10
% 2.40/0.98  sup_given_eliminated:                   0
% 2.40/0.98  comparisons_done:                       0
% 2.40/0.98  comparisons_avoided:                    4
% 2.40/0.98  
% 2.40/0.98  ------ Simplifications
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  sim_fw_subset_subsumed:                 8
% 2.40/0.98  sim_bw_subset_subsumed:                 3
% 2.40/0.98  sim_fw_subsumed:                        2
% 2.40/0.98  sim_bw_subsumed:                        0
% 2.40/0.98  sim_fw_subsumption_res:                 22
% 2.40/0.98  sim_bw_subsumption_res:                 0
% 2.40/0.98  sim_tautology_del:                      2
% 2.40/0.98  sim_eq_tautology_del:                   2
% 2.40/0.98  sim_eq_res_simp:                        2
% 2.40/0.98  sim_fw_demodulated:                     0
% 2.40/0.98  sim_bw_demodulated:                     0
% 2.40/0.98  sim_light_normalised:                   0
% 2.40/0.98  sim_joinable_taut:                      0
% 2.40/0.98  sim_joinable_simp:                      0
% 2.40/0.98  sim_ac_normalised:                      0
% 2.40/0.98  sim_smt_subsumption:                    0
% 2.40/0.98  
%------------------------------------------------------------------------------
