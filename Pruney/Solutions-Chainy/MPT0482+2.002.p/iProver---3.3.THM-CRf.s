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
% DateTime   : Thu Dec  3 11:44:35 EST 2020

% Result     : Theorem 1.32s
% Output     : CNFRefutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 142 expanded)
%              Number of clauses        :   37 (  44 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  278 ( 489 expanded)
%              Number of equality atoms :   64 ( 107 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k1_relat_1(X1),X0)
         => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k5_relat_1(k6_relat_1(X0),X1) != X1
        & r1_tarski(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k5_relat_1(k6_relat_1(sK6),sK7) != sK7
      & r1_tarski(k1_relat_1(sK7),sK6)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k5_relat_1(k6_relat_1(sK6),sK7) != sK7
    & r1_tarski(k1_relat_1(sK7),sK6)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f14,f33])).

fof(f54,plain,(
    r1_tarski(k1_relat_1(sK7),sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f26,f29,f28,f27])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f45])).

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
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    k5_relat_1(k6_relat_1(sK6),sK7) != sK7 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k1_relat_1(sK7),sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_748,plain,
    ( r1_tarski(k1_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_228,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_229,plain,
    ( r2_hidden(k4_tarski(sK1(sK7,X0),sK2(sK7,X0)),sK7)
    | r1_tarski(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_746,plain,
    ( r2_hidden(k4_tarski(sK1(sK7,X0),sK2(sK7,X0)),sK7) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_750,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1235,plain,
    ( r2_hidden(sK1(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_746,c_750])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_755,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1906,plain,
    ( r2_hidden(sK1(sK7,X0),X1) = iProver_top
    | r1_tarski(k1_relat_1(sK7),X1) != iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_755])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_275,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_276,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),sK7))
    | ~ r2_hidden(k4_tarski(X0,X2),sK7) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_742,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_238,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_239,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK7,X0),sK2(sK7,X0)),X0)
    | r1_tarski(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_745,plain,
    ( r2_hidden(k4_tarski(sK1(sK7,X0),sK2(sK7,X0)),X0) != iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_958,plain,
    ( r2_hidden(k4_tarski(sK1(sK7,k5_relat_1(k6_relat_1(X0),sK7)),sK2(sK7,k5_relat_1(k6_relat_1(X0),sK7))),sK7) != iProver_top
    | r2_hidden(sK1(sK7,k5_relat_1(k6_relat_1(X0),sK7)),X0) != iProver_top
    | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_742,c_745])).

cnf(c_1299,plain,
    ( r2_hidden(k4_tarski(sK1(sK7,k5_relat_1(k6_relat_1(X0),sK7)),sK2(sK7,k5_relat_1(k6_relat_1(X0),sK7))),sK7)
    | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_1300,plain,
    ( r2_hidden(k4_tarski(sK1(sK7,k5_relat_1(k6_relat_1(X0),sK7)),sK2(sK7,k5_relat_1(k6_relat_1(X0),sK7))),sK7) = iProver_top
    | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1299])).

cnf(c_1378,plain,
    ( r2_hidden(sK1(sK7,k5_relat_1(k6_relat_1(X0),sK7)),X0) != iProver_top
    | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_958,c_1300])).

cnf(c_2882,plain,
    ( r1_tarski(k1_relat_1(sK7),X0) != iProver_top
    | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_1378])).

cnf(c_16,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_290,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_291,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),sK7),sK7) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_741,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_754,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1719,plain,
    ( k5_relat_1(k6_relat_1(X0),sK7) = sK7
    | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_754])).

cnf(c_3325,plain,
    ( k5_relat_1(k6_relat_1(X0),sK7) = sK7
    | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2882,c_1719])).

cnf(c_3461,plain,
    ( k5_relat_1(k6_relat_1(sK6),sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_748,c_3325])).

cnf(c_18,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK6),sK7) != sK7 ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3461,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.32/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.32/1.02  
% 1.32/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.32/1.02  
% 1.32/1.02  ------  iProver source info
% 1.32/1.02  
% 1.32/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.32/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.32/1.02  git: non_committed_changes: false
% 1.32/1.02  git: last_make_outside_of_git: false
% 1.32/1.02  
% 1.32/1.02  ------ 
% 1.32/1.02  
% 1.32/1.02  ------ Input Options
% 1.32/1.02  
% 1.32/1.02  --out_options                           all
% 1.32/1.02  --tptp_safe_out                         true
% 1.32/1.02  --problem_path                          ""
% 1.32/1.02  --include_path                          ""
% 1.32/1.02  --clausifier                            res/vclausify_rel
% 1.32/1.02  --clausifier_options                    --mode clausify
% 1.32/1.02  --stdin                                 false
% 1.32/1.02  --stats_out                             all
% 1.32/1.02  
% 1.32/1.02  ------ General Options
% 1.32/1.02  
% 1.32/1.02  --fof                                   false
% 1.32/1.02  --time_out_real                         305.
% 1.32/1.02  --time_out_virtual                      -1.
% 1.32/1.02  --symbol_type_check                     false
% 1.32/1.02  --clausify_out                          false
% 1.32/1.02  --sig_cnt_out                           false
% 1.32/1.02  --trig_cnt_out                          false
% 1.32/1.02  --trig_cnt_out_tolerance                1.
% 1.32/1.02  --trig_cnt_out_sk_spl                   false
% 1.32/1.02  --abstr_cl_out                          false
% 1.32/1.02  
% 1.32/1.02  ------ Global Options
% 1.32/1.02  
% 1.32/1.02  --schedule                              default
% 1.32/1.02  --add_important_lit                     false
% 1.32/1.02  --prop_solver_per_cl                    1000
% 1.32/1.02  --min_unsat_core                        false
% 1.32/1.02  --soft_assumptions                      false
% 1.32/1.02  --soft_lemma_size                       3
% 1.32/1.02  --prop_impl_unit_size                   0
% 1.32/1.02  --prop_impl_unit                        []
% 1.32/1.02  --share_sel_clauses                     true
% 1.32/1.02  --reset_solvers                         false
% 1.32/1.02  --bc_imp_inh                            [conj_cone]
% 1.32/1.02  --conj_cone_tolerance                   3.
% 1.32/1.02  --extra_neg_conj                        none
% 1.32/1.02  --large_theory_mode                     true
% 1.32/1.02  --prolific_symb_bound                   200
% 1.32/1.02  --lt_threshold                          2000
% 1.32/1.02  --clause_weak_htbl                      true
% 1.32/1.02  --gc_record_bc_elim                     false
% 1.32/1.02  
% 1.32/1.02  ------ Preprocessing Options
% 1.32/1.02  
% 1.32/1.02  --preprocessing_flag                    true
% 1.32/1.02  --time_out_prep_mult                    0.1
% 1.32/1.02  --splitting_mode                        input
% 1.32/1.02  --splitting_grd                         true
% 1.32/1.02  --splitting_cvd                         false
% 1.32/1.02  --splitting_cvd_svl                     false
% 1.32/1.02  --splitting_nvd                         32
% 1.32/1.02  --sub_typing                            true
% 1.32/1.02  --prep_gs_sim                           true
% 1.32/1.02  --prep_unflatten                        true
% 1.32/1.02  --prep_res_sim                          true
% 1.32/1.02  --prep_upred                            true
% 1.32/1.02  --prep_sem_filter                       exhaustive
% 1.32/1.02  --prep_sem_filter_out                   false
% 1.32/1.02  --pred_elim                             true
% 1.32/1.02  --res_sim_input                         true
% 1.32/1.02  --eq_ax_congr_red                       true
% 1.32/1.02  --pure_diseq_elim                       true
% 1.32/1.02  --brand_transform                       false
% 1.32/1.02  --non_eq_to_eq                          false
% 1.32/1.02  --prep_def_merge                        true
% 1.32/1.02  --prep_def_merge_prop_impl              false
% 1.32/1.02  --prep_def_merge_mbd                    true
% 1.32/1.02  --prep_def_merge_tr_red                 false
% 1.32/1.02  --prep_def_merge_tr_cl                  false
% 1.32/1.02  --smt_preprocessing                     true
% 1.32/1.02  --smt_ac_axioms                         fast
% 1.32/1.02  --preprocessed_out                      false
% 1.32/1.02  --preprocessed_stats                    false
% 1.32/1.02  
% 1.32/1.02  ------ Abstraction refinement Options
% 1.32/1.02  
% 1.32/1.02  --abstr_ref                             []
% 1.32/1.02  --abstr_ref_prep                        false
% 1.32/1.02  --abstr_ref_until_sat                   false
% 1.32/1.02  --abstr_ref_sig_restrict                funpre
% 1.32/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.32/1.02  --abstr_ref_under                       []
% 1.32/1.02  
% 1.32/1.02  ------ SAT Options
% 1.32/1.02  
% 1.32/1.02  --sat_mode                              false
% 1.32/1.02  --sat_fm_restart_options                ""
% 1.32/1.02  --sat_gr_def                            false
% 1.32/1.02  --sat_epr_types                         true
% 1.32/1.02  --sat_non_cyclic_types                  false
% 1.32/1.02  --sat_finite_models                     false
% 1.32/1.02  --sat_fm_lemmas                         false
% 1.32/1.02  --sat_fm_prep                           false
% 1.32/1.02  --sat_fm_uc_incr                        true
% 1.32/1.02  --sat_out_model                         small
% 1.32/1.02  --sat_out_clauses                       false
% 1.32/1.02  
% 1.32/1.02  ------ QBF Options
% 1.32/1.02  
% 1.32/1.02  --qbf_mode                              false
% 1.32/1.02  --qbf_elim_univ                         false
% 1.32/1.02  --qbf_dom_inst                          none
% 1.32/1.02  --qbf_dom_pre_inst                      false
% 1.32/1.02  --qbf_sk_in                             false
% 1.32/1.02  --qbf_pred_elim                         true
% 1.32/1.02  --qbf_split                             512
% 1.32/1.02  
% 1.32/1.02  ------ BMC1 Options
% 1.32/1.02  
% 1.32/1.02  --bmc1_incremental                      false
% 1.32/1.02  --bmc1_axioms                           reachable_all
% 1.32/1.02  --bmc1_min_bound                        0
% 1.32/1.02  --bmc1_max_bound                        -1
% 1.32/1.02  --bmc1_max_bound_default                -1
% 1.32/1.02  --bmc1_symbol_reachability              true
% 1.32/1.02  --bmc1_property_lemmas                  false
% 1.32/1.02  --bmc1_k_induction                      false
% 1.32/1.02  --bmc1_non_equiv_states                 false
% 1.32/1.02  --bmc1_deadlock                         false
% 1.32/1.02  --bmc1_ucm                              false
% 1.32/1.02  --bmc1_add_unsat_core                   none
% 1.32/1.02  --bmc1_unsat_core_children              false
% 1.32/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.32/1.02  --bmc1_out_stat                         full
% 1.32/1.02  --bmc1_ground_init                      false
% 1.32/1.02  --bmc1_pre_inst_next_state              false
% 1.32/1.02  --bmc1_pre_inst_state                   false
% 1.32/1.02  --bmc1_pre_inst_reach_state             false
% 1.32/1.02  --bmc1_out_unsat_core                   false
% 1.32/1.02  --bmc1_aig_witness_out                  false
% 1.32/1.02  --bmc1_verbose                          false
% 1.32/1.02  --bmc1_dump_clauses_tptp                false
% 1.32/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.32/1.02  --bmc1_dump_file                        -
% 1.32/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.32/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.32/1.02  --bmc1_ucm_extend_mode                  1
% 1.32/1.02  --bmc1_ucm_init_mode                    2
% 1.32/1.02  --bmc1_ucm_cone_mode                    none
% 1.32/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.32/1.02  --bmc1_ucm_relax_model                  4
% 1.32/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.32/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.32/1.02  --bmc1_ucm_layered_model                none
% 1.32/1.02  --bmc1_ucm_max_lemma_size               10
% 1.32/1.02  
% 1.32/1.02  ------ AIG Options
% 1.32/1.02  
% 1.32/1.02  --aig_mode                              false
% 1.32/1.02  
% 1.32/1.02  ------ Instantiation Options
% 1.32/1.02  
% 1.32/1.02  --instantiation_flag                    true
% 1.32/1.02  --inst_sos_flag                         false
% 1.32/1.02  --inst_sos_phase                        true
% 1.32/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.32/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.32/1.02  --inst_lit_sel_side                     num_symb
% 1.32/1.02  --inst_solver_per_active                1400
% 1.32/1.02  --inst_solver_calls_frac                1.
% 1.32/1.02  --inst_passive_queue_type               priority_queues
% 1.32/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.32/1.02  --inst_passive_queues_freq              [25;2]
% 1.32/1.02  --inst_dismatching                      true
% 1.32/1.02  --inst_eager_unprocessed_to_passive     true
% 1.32/1.02  --inst_prop_sim_given                   true
% 1.32/1.02  --inst_prop_sim_new                     false
% 1.32/1.02  --inst_subs_new                         false
% 1.32/1.02  --inst_eq_res_simp                      false
% 1.32/1.02  --inst_subs_given                       false
% 1.32/1.02  --inst_orphan_elimination               true
% 1.32/1.02  --inst_learning_loop_flag               true
% 1.32/1.02  --inst_learning_start                   3000
% 1.32/1.02  --inst_learning_factor                  2
% 1.32/1.02  --inst_start_prop_sim_after_learn       3
% 1.32/1.02  --inst_sel_renew                        solver
% 1.32/1.02  --inst_lit_activity_flag                true
% 1.32/1.02  --inst_restr_to_given                   false
% 1.32/1.02  --inst_activity_threshold               500
% 1.32/1.02  --inst_out_proof                        true
% 1.32/1.02  
% 1.32/1.02  ------ Resolution Options
% 1.32/1.02  
% 1.32/1.02  --resolution_flag                       true
% 1.32/1.02  --res_lit_sel                           adaptive
% 1.32/1.02  --res_lit_sel_side                      none
% 1.32/1.02  --res_ordering                          kbo
% 1.32/1.02  --res_to_prop_solver                    active
% 1.32/1.02  --res_prop_simpl_new                    false
% 1.32/1.02  --res_prop_simpl_given                  true
% 1.32/1.02  --res_passive_queue_type                priority_queues
% 1.32/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.32/1.02  --res_passive_queues_freq               [15;5]
% 1.32/1.02  --res_forward_subs                      full
% 1.32/1.02  --res_backward_subs                     full
% 1.32/1.02  --res_forward_subs_resolution           true
% 1.32/1.02  --res_backward_subs_resolution          true
% 1.32/1.02  --res_orphan_elimination                true
% 1.32/1.02  --res_time_limit                        2.
% 1.32/1.02  --res_out_proof                         true
% 1.32/1.02  
% 1.32/1.02  ------ Superposition Options
% 1.32/1.02  
% 1.32/1.02  --superposition_flag                    true
% 1.32/1.02  --sup_passive_queue_type                priority_queues
% 1.32/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.32/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.32/1.02  --demod_completeness_check              fast
% 1.32/1.02  --demod_use_ground                      true
% 1.32/1.02  --sup_to_prop_solver                    passive
% 1.32/1.02  --sup_prop_simpl_new                    true
% 1.32/1.02  --sup_prop_simpl_given                  true
% 1.32/1.02  --sup_fun_splitting                     false
% 1.32/1.02  --sup_smt_interval                      50000
% 1.32/1.02  
% 1.32/1.02  ------ Superposition Simplification Setup
% 1.32/1.02  
% 1.32/1.02  --sup_indices_passive                   []
% 1.32/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.32/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.02  --sup_full_bw                           [BwDemod]
% 1.32/1.02  --sup_immed_triv                        [TrivRules]
% 1.32/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.32/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.02  --sup_immed_bw_main                     []
% 1.32/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.32/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.02  
% 1.32/1.02  ------ Combination Options
% 1.32/1.02  
% 1.32/1.02  --comb_res_mult                         3
% 1.32/1.02  --comb_sup_mult                         2
% 1.32/1.02  --comb_inst_mult                        10
% 1.32/1.02  
% 1.32/1.02  ------ Debug Options
% 1.32/1.02  
% 1.32/1.02  --dbg_backtrace                         false
% 1.32/1.02  --dbg_dump_prop_clauses                 false
% 1.32/1.02  --dbg_dump_prop_clauses_file            -
% 1.32/1.02  --dbg_out_stat                          false
% 1.32/1.02  ------ Parsing...
% 1.32/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.32/1.02  
% 1.32/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.32/1.02  
% 1.32/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.32/1.02  
% 1.32/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.32/1.02  ------ Proving...
% 1.32/1.02  ------ Problem Properties 
% 1.32/1.02  
% 1.32/1.02  
% 1.32/1.02  clauses                                 18
% 1.32/1.02  conjectures                             2
% 1.32/1.02  EPR                                     3
% 1.32/1.02  Horn                                    15
% 1.32/1.02  unary                                   5
% 1.32/1.02  binary                                  8
% 1.32/1.02  lits                                    36
% 1.32/1.02  lits eq                                 4
% 1.32/1.02  fd_pure                                 0
% 1.32/1.02  fd_pseudo                               0
% 1.32/1.02  fd_cond                                 0
% 1.32/1.02  fd_pseudo_cond                          3
% 1.32/1.02  AC symbols                              0
% 1.32/1.02  
% 1.32/1.02  ------ Schedule dynamic 5 is on 
% 1.32/1.02  
% 1.32/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.32/1.02  
% 1.32/1.02  
% 1.32/1.02  ------ 
% 1.32/1.02  Current options:
% 1.32/1.02  ------ 
% 1.32/1.02  
% 1.32/1.02  ------ Input Options
% 1.32/1.02  
% 1.32/1.02  --out_options                           all
% 1.32/1.02  --tptp_safe_out                         true
% 1.32/1.02  --problem_path                          ""
% 1.32/1.02  --include_path                          ""
% 1.32/1.02  --clausifier                            res/vclausify_rel
% 1.32/1.02  --clausifier_options                    --mode clausify
% 1.32/1.02  --stdin                                 false
% 1.32/1.02  --stats_out                             all
% 1.32/1.02  
% 1.32/1.02  ------ General Options
% 1.32/1.02  
% 1.32/1.02  --fof                                   false
% 1.32/1.02  --time_out_real                         305.
% 1.32/1.02  --time_out_virtual                      -1.
% 1.32/1.02  --symbol_type_check                     false
% 1.32/1.02  --clausify_out                          false
% 1.32/1.02  --sig_cnt_out                           false
% 1.32/1.02  --trig_cnt_out                          false
% 1.32/1.02  --trig_cnt_out_tolerance                1.
% 1.32/1.02  --trig_cnt_out_sk_spl                   false
% 1.32/1.02  --abstr_cl_out                          false
% 1.32/1.02  
% 1.32/1.02  ------ Global Options
% 1.32/1.02  
% 1.32/1.02  --schedule                              default
% 1.32/1.02  --add_important_lit                     false
% 1.32/1.02  --prop_solver_per_cl                    1000
% 1.32/1.02  --min_unsat_core                        false
% 1.32/1.02  --soft_assumptions                      false
% 1.32/1.02  --soft_lemma_size                       3
% 1.32/1.02  --prop_impl_unit_size                   0
% 1.32/1.02  --prop_impl_unit                        []
% 1.32/1.02  --share_sel_clauses                     true
% 1.32/1.02  --reset_solvers                         false
% 1.32/1.02  --bc_imp_inh                            [conj_cone]
% 1.32/1.02  --conj_cone_tolerance                   3.
% 1.32/1.02  --extra_neg_conj                        none
% 1.32/1.02  --large_theory_mode                     true
% 1.32/1.02  --prolific_symb_bound                   200
% 1.32/1.02  --lt_threshold                          2000
% 1.32/1.02  --clause_weak_htbl                      true
% 1.32/1.02  --gc_record_bc_elim                     false
% 1.32/1.02  
% 1.32/1.02  ------ Preprocessing Options
% 1.32/1.02  
% 1.32/1.02  --preprocessing_flag                    true
% 1.32/1.02  --time_out_prep_mult                    0.1
% 1.32/1.02  --splitting_mode                        input
% 1.32/1.02  --splitting_grd                         true
% 1.32/1.02  --splitting_cvd                         false
% 1.32/1.02  --splitting_cvd_svl                     false
% 1.32/1.02  --splitting_nvd                         32
% 1.32/1.02  --sub_typing                            true
% 1.32/1.02  --prep_gs_sim                           true
% 1.32/1.02  --prep_unflatten                        true
% 1.32/1.02  --prep_res_sim                          true
% 1.32/1.02  --prep_upred                            true
% 1.32/1.02  --prep_sem_filter                       exhaustive
% 1.32/1.02  --prep_sem_filter_out                   false
% 1.32/1.02  --pred_elim                             true
% 1.32/1.02  --res_sim_input                         true
% 1.32/1.02  --eq_ax_congr_red                       true
% 1.32/1.02  --pure_diseq_elim                       true
% 1.32/1.02  --brand_transform                       false
% 1.32/1.02  --non_eq_to_eq                          false
% 1.32/1.02  --prep_def_merge                        true
% 1.32/1.02  --prep_def_merge_prop_impl              false
% 1.32/1.02  --prep_def_merge_mbd                    true
% 1.32/1.02  --prep_def_merge_tr_red                 false
% 1.32/1.02  --prep_def_merge_tr_cl                  false
% 1.32/1.02  --smt_preprocessing                     true
% 1.32/1.02  --smt_ac_axioms                         fast
% 1.32/1.02  --preprocessed_out                      false
% 1.32/1.02  --preprocessed_stats                    false
% 1.32/1.02  
% 1.32/1.02  ------ Abstraction refinement Options
% 1.32/1.02  
% 1.32/1.02  --abstr_ref                             []
% 1.32/1.02  --abstr_ref_prep                        false
% 1.32/1.02  --abstr_ref_until_sat                   false
% 1.32/1.02  --abstr_ref_sig_restrict                funpre
% 1.32/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.32/1.02  --abstr_ref_under                       []
% 1.32/1.02  
% 1.32/1.02  ------ SAT Options
% 1.32/1.02  
% 1.32/1.02  --sat_mode                              false
% 1.32/1.02  --sat_fm_restart_options                ""
% 1.32/1.02  --sat_gr_def                            false
% 1.32/1.02  --sat_epr_types                         true
% 1.32/1.02  --sat_non_cyclic_types                  false
% 1.32/1.02  --sat_finite_models                     false
% 1.32/1.02  --sat_fm_lemmas                         false
% 1.32/1.02  --sat_fm_prep                           false
% 1.32/1.02  --sat_fm_uc_incr                        true
% 1.32/1.02  --sat_out_model                         small
% 1.32/1.02  --sat_out_clauses                       false
% 1.32/1.02  
% 1.32/1.02  ------ QBF Options
% 1.32/1.02  
% 1.32/1.02  --qbf_mode                              false
% 1.32/1.02  --qbf_elim_univ                         false
% 1.32/1.02  --qbf_dom_inst                          none
% 1.32/1.02  --qbf_dom_pre_inst                      false
% 1.32/1.02  --qbf_sk_in                             false
% 1.32/1.02  --qbf_pred_elim                         true
% 1.32/1.02  --qbf_split                             512
% 1.32/1.02  
% 1.32/1.02  ------ BMC1 Options
% 1.32/1.02  
% 1.32/1.02  --bmc1_incremental                      false
% 1.32/1.02  --bmc1_axioms                           reachable_all
% 1.32/1.02  --bmc1_min_bound                        0
% 1.32/1.02  --bmc1_max_bound                        -1
% 1.32/1.02  --bmc1_max_bound_default                -1
% 1.32/1.02  --bmc1_symbol_reachability              true
% 1.32/1.02  --bmc1_property_lemmas                  false
% 1.32/1.02  --bmc1_k_induction                      false
% 1.32/1.02  --bmc1_non_equiv_states                 false
% 1.32/1.02  --bmc1_deadlock                         false
% 1.32/1.02  --bmc1_ucm                              false
% 1.32/1.02  --bmc1_add_unsat_core                   none
% 1.32/1.02  --bmc1_unsat_core_children              false
% 1.32/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.32/1.02  --bmc1_out_stat                         full
% 1.32/1.02  --bmc1_ground_init                      false
% 1.32/1.02  --bmc1_pre_inst_next_state              false
% 1.32/1.02  --bmc1_pre_inst_state                   false
% 1.32/1.02  --bmc1_pre_inst_reach_state             false
% 1.32/1.02  --bmc1_out_unsat_core                   false
% 1.32/1.02  --bmc1_aig_witness_out                  false
% 1.32/1.02  --bmc1_verbose                          false
% 1.32/1.02  --bmc1_dump_clauses_tptp                false
% 1.32/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.32/1.02  --bmc1_dump_file                        -
% 1.32/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.32/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.32/1.02  --bmc1_ucm_extend_mode                  1
% 1.32/1.02  --bmc1_ucm_init_mode                    2
% 1.32/1.02  --bmc1_ucm_cone_mode                    none
% 1.32/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.32/1.02  --bmc1_ucm_relax_model                  4
% 1.32/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.32/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.32/1.02  --bmc1_ucm_layered_model                none
% 1.32/1.02  --bmc1_ucm_max_lemma_size               10
% 1.32/1.02  
% 1.32/1.02  ------ AIG Options
% 1.32/1.02  
% 1.32/1.02  --aig_mode                              false
% 1.32/1.02  
% 1.32/1.02  ------ Instantiation Options
% 1.32/1.02  
% 1.32/1.02  --instantiation_flag                    true
% 1.32/1.02  --inst_sos_flag                         false
% 1.32/1.02  --inst_sos_phase                        true
% 1.32/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.32/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.32/1.02  --inst_lit_sel_side                     none
% 1.32/1.02  --inst_solver_per_active                1400
% 1.32/1.02  --inst_solver_calls_frac                1.
% 1.32/1.02  --inst_passive_queue_type               priority_queues
% 1.32/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.32/1.02  --inst_passive_queues_freq              [25;2]
% 1.32/1.02  --inst_dismatching                      true
% 1.32/1.02  --inst_eager_unprocessed_to_passive     true
% 1.32/1.02  --inst_prop_sim_given                   true
% 1.32/1.02  --inst_prop_sim_new                     false
% 1.32/1.02  --inst_subs_new                         false
% 1.32/1.02  --inst_eq_res_simp                      false
% 1.32/1.02  --inst_subs_given                       false
% 1.32/1.02  --inst_orphan_elimination               true
% 1.32/1.02  --inst_learning_loop_flag               true
% 1.32/1.02  --inst_learning_start                   3000
% 1.32/1.02  --inst_learning_factor                  2
% 1.32/1.02  --inst_start_prop_sim_after_learn       3
% 1.32/1.02  --inst_sel_renew                        solver
% 1.32/1.02  --inst_lit_activity_flag                true
% 1.32/1.02  --inst_restr_to_given                   false
% 1.32/1.02  --inst_activity_threshold               500
% 1.32/1.02  --inst_out_proof                        true
% 1.32/1.02  
% 1.32/1.02  ------ Resolution Options
% 1.32/1.02  
% 1.32/1.02  --resolution_flag                       false
% 1.32/1.02  --res_lit_sel                           adaptive
% 1.32/1.02  --res_lit_sel_side                      none
% 1.32/1.02  --res_ordering                          kbo
% 1.32/1.02  --res_to_prop_solver                    active
% 1.32/1.02  --res_prop_simpl_new                    false
% 1.32/1.02  --res_prop_simpl_given                  true
% 1.32/1.02  --res_passive_queue_type                priority_queues
% 1.32/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.32/1.02  --res_passive_queues_freq               [15;5]
% 1.32/1.02  --res_forward_subs                      full
% 1.32/1.02  --res_backward_subs                     full
% 1.32/1.02  --res_forward_subs_resolution           true
% 1.32/1.02  --res_backward_subs_resolution          true
% 1.32/1.02  --res_orphan_elimination                true
% 1.32/1.02  --res_time_limit                        2.
% 1.32/1.02  --res_out_proof                         true
% 1.32/1.02  
% 1.32/1.02  ------ Superposition Options
% 1.32/1.02  
% 1.32/1.02  --superposition_flag                    true
% 1.32/1.02  --sup_passive_queue_type                priority_queues
% 1.32/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.32/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.32/1.02  --demod_completeness_check              fast
% 1.32/1.02  --demod_use_ground                      true
% 1.32/1.02  --sup_to_prop_solver                    passive
% 1.32/1.02  --sup_prop_simpl_new                    true
% 1.32/1.02  --sup_prop_simpl_given                  true
% 1.32/1.02  --sup_fun_splitting                     false
% 1.32/1.02  --sup_smt_interval                      50000
% 1.32/1.02  
% 1.32/1.02  ------ Superposition Simplification Setup
% 1.32/1.02  
% 1.32/1.02  --sup_indices_passive                   []
% 1.32/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.32/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.02  --sup_full_bw                           [BwDemod]
% 1.32/1.02  --sup_immed_triv                        [TrivRules]
% 1.32/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.32/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.02  --sup_immed_bw_main                     []
% 1.32/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.32/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.02  
% 1.32/1.02  ------ Combination Options
% 1.32/1.02  
% 1.32/1.02  --comb_res_mult                         3
% 1.32/1.02  --comb_sup_mult                         2
% 1.32/1.02  --comb_inst_mult                        10
% 1.32/1.02  
% 1.32/1.02  ------ Debug Options
% 1.32/1.02  
% 1.32/1.02  --dbg_backtrace                         false
% 1.32/1.02  --dbg_dump_prop_clauses                 false
% 1.32/1.02  --dbg_dump_prop_clauses_file            -
% 1.32/1.02  --dbg_out_stat                          false
% 1.32/1.02  
% 1.32/1.02  
% 1.32/1.02  
% 1.32/1.02  
% 1.32/1.02  ------ Proving...
% 1.32/1.02  
% 1.32/1.02  
% 1.32/1.02  % SZS status Theorem for theBenchmark.p
% 1.32/1.02  
% 1.32/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.32/1.02  
% 1.32/1.02  fof(f7,conjecture,(
% 1.32/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.32/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.02  
% 1.32/1.02  fof(f8,negated_conjecture,(
% 1.32/1.02    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.32/1.02    inference(negated_conjecture,[],[f7])).
% 1.32/1.02  
% 1.32/1.02  fof(f13,plain,(
% 1.32/1.02    ? [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.32/1.02    inference(ennf_transformation,[],[f8])).
% 1.32/1.02  
% 1.32/1.02  fof(f14,plain,(
% 1.32/1.02    ? [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0) & v1_relat_1(X1))),
% 1.32/1.02    inference(flattening,[],[f13])).
% 1.32/1.02  
% 1.32/1.02  fof(f33,plain,(
% 1.32/1.02    ? [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0) & v1_relat_1(X1)) => (k5_relat_1(k6_relat_1(sK6),sK7) != sK7 & r1_tarski(k1_relat_1(sK7),sK6) & v1_relat_1(sK7))),
% 1.32/1.02    introduced(choice_axiom,[])).
% 1.32/1.02  
% 1.32/1.02  fof(f34,plain,(
% 1.32/1.02    k5_relat_1(k6_relat_1(sK6),sK7) != sK7 & r1_tarski(k1_relat_1(sK7),sK6) & v1_relat_1(sK7)),
% 1.32/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f14,f33])).
% 1.32/1.02  
% 1.32/1.02  fof(f54,plain,(
% 1.32/1.02    r1_tarski(k1_relat_1(sK7),sK6)),
% 1.32/1.02    inference(cnf_transformation,[],[f34])).
% 1.32/1.02  
% 1.32/1.02  fof(f3,axiom,(
% 1.32/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.32/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.02  
% 1.32/1.02  fof(f10,plain,(
% 1.32/1.02    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.32/1.02    inference(ennf_transformation,[],[f3])).
% 1.32/1.02  
% 1.32/1.02  fof(f21,plain,(
% 1.32/1.02    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.32/1.02    inference(nnf_transformation,[],[f10])).
% 1.32/1.02  
% 1.32/1.02  fof(f22,plain,(
% 1.32/1.02    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.32/1.02    inference(rectify,[],[f21])).
% 1.32/1.02  
% 1.32/1.02  fof(f23,plain,(
% 1.32/1.02    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)))),
% 1.32/1.02    introduced(choice_axiom,[])).
% 1.32/1.02  
% 1.32/1.02  fof(f24,plain,(
% 1.32/1.02    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.32/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).
% 1.32/1.02  
% 1.32/1.02  fof(f42,plain,(
% 1.32/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 1.32/1.02    inference(cnf_transformation,[],[f24])).
% 1.32/1.02  
% 1.32/1.02  fof(f53,plain,(
% 1.32/1.02    v1_relat_1(sK7)),
% 1.32/1.02    inference(cnf_transformation,[],[f34])).
% 1.32/1.02  
% 1.32/1.02  fof(f4,axiom,(
% 1.32/1.02    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.32/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.02  
% 1.32/1.02  fof(f25,plain,(
% 1.32/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.32/1.02    inference(nnf_transformation,[],[f4])).
% 1.32/1.02  
% 1.32/1.02  fof(f26,plain,(
% 1.32/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.32/1.02    inference(rectify,[],[f25])).
% 1.32/1.02  
% 1.32/1.02  fof(f29,plain,(
% 1.32/1.02    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 1.32/1.02    introduced(choice_axiom,[])).
% 1.32/1.02  
% 1.32/1.02  fof(f28,plain,(
% 1.32/1.02    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0))) )),
% 1.32/1.02    introduced(choice_axiom,[])).
% 1.32/1.02  
% 1.32/1.02  fof(f27,plain,(
% 1.32/1.02    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.32/1.02    introduced(choice_axiom,[])).
% 1.32/1.02  
% 1.32/1.02  fof(f30,plain,(
% 1.32/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.32/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f26,f29,f28,f27])).
% 1.32/1.02  
% 1.32/1.02  fof(f45,plain,(
% 1.32/1.02    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.32/1.02    inference(cnf_transformation,[],[f30])).
% 1.32/1.02  
% 1.32/1.02  fof(f58,plain,(
% 1.32/1.02    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 1.32/1.02    inference(equality_resolution,[],[f45])).
% 1.32/1.02  
% 1.32/1.02  fof(f1,axiom,(
% 1.32/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.32/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.02  
% 1.32/1.02  fof(f9,plain,(
% 1.32/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.32/1.02    inference(ennf_transformation,[],[f1])).
% 1.32/1.02  
% 1.32/1.02  fof(f15,plain,(
% 1.32/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/1.02    inference(nnf_transformation,[],[f9])).
% 1.32/1.02  
% 1.32/1.02  fof(f16,plain,(
% 1.32/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/1.02    inference(rectify,[],[f15])).
% 1.32/1.02  
% 1.32/1.02  fof(f17,plain,(
% 1.32/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.32/1.02    introduced(choice_axiom,[])).
% 1.32/1.02  
% 1.32/1.02  fof(f18,plain,(
% 1.32/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 1.32/1.02  
% 1.32/1.02  fof(f35,plain,(
% 1.32/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.32/1.02    inference(cnf_transformation,[],[f18])).
% 1.32/1.02  
% 1.32/1.02  fof(f5,axiom,(
% 1.32/1.02    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 1.32/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.02  
% 1.32/1.02  fof(f11,plain,(
% 1.32/1.02    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 1.32/1.02    inference(ennf_transformation,[],[f5])).
% 1.32/1.02  
% 1.32/1.02  fof(f31,plain,(
% 1.32/1.02    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 1.32/1.02    inference(nnf_transformation,[],[f11])).
% 1.32/1.02  
% 1.32/1.02  fof(f32,plain,(
% 1.32/1.02    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 1.32/1.02    inference(flattening,[],[f31])).
% 1.32/1.02  
% 1.32/1.02  fof(f50,plain,(
% 1.32/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2) | ~v1_relat_1(X3)) )),
% 1.32/1.02    inference(cnf_transformation,[],[f32])).
% 1.32/1.02  
% 1.32/1.02  fof(f43,plain,(
% 1.32/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 1.32/1.02    inference(cnf_transformation,[],[f24])).
% 1.32/1.02  
% 1.32/1.02  fof(f6,axiom,(
% 1.32/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.32/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.02  
% 1.32/1.02  fof(f12,plain,(
% 1.32/1.02    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.32/1.02    inference(ennf_transformation,[],[f6])).
% 1.32/1.02  
% 1.32/1.02  fof(f52,plain,(
% 1.32/1.02    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 1.32/1.02    inference(cnf_transformation,[],[f12])).
% 1.32/1.02  
% 1.32/1.02  fof(f2,axiom,(
% 1.32/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.02  
% 1.32/1.02  fof(f19,plain,(
% 1.32/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/1.02    inference(nnf_transformation,[],[f2])).
% 1.32/1.02  
% 1.32/1.02  fof(f20,plain,(
% 1.32/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/1.02    inference(flattening,[],[f19])).
% 1.32/1.02  
% 1.32/1.02  fof(f40,plain,(
% 1.32/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.32/1.02    inference(cnf_transformation,[],[f20])).
% 1.32/1.02  
% 1.32/1.02  fof(f55,plain,(
% 1.32/1.02    k5_relat_1(k6_relat_1(sK6),sK7) != sK7),
% 1.32/1.02    inference(cnf_transformation,[],[f34])).
% 1.32/1.02  
% 1.32/1.02  cnf(c_19,negated_conjecture,
% 1.32/1.02      ( r1_tarski(k1_relat_1(sK7),sK6) ),
% 1.32/1.02      inference(cnf_transformation,[],[f54]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_748,plain,
% 1.32/1.02      ( r1_tarski(k1_relat_1(sK7),sK6) = iProver_top ),
% 1.32/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_7,plain,
% 1.32/1.02      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 1.32/1.02      | r1_tarski(X0,X1)
% 1.32/1.02      | ~ v1_relat_1(X0) ),
% 1.32/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_20,negated_conjecture,
% 1.32/1.02      ( v1_relat_1(sK7) ),
% 1.32/1.02      inference(cnf_transformation,[],[f53]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_228,plain,
% 1.32/1.02      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 1.32/1.02      | r1_tarski(X0,X1)
% 1.32/1.02      | sK7 != X0 ),
% 1.32/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_229,plain,
% 1.32/1.02      ( r2_hidden(k4_tarski(sK1(sK7,X0),sK2(sK7,X0)),sK7)
% 1.32/1.02      | r1_tarski(sK7,X0) ),
% 1.32/1.02      inference(unflattening,[status(thm)],[c_228]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_746,plain,
% 1.32/1.02      ( r2_hidden(k4_tarski(sK1(sK7,X0),sK2(sK7,X0)),sK7) = iProver_top
% 1.32/1.02      | r1_tarski(sK7,X0) = iProver_top ),
% 1.32/1.02      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_11,plain,
% 1.32/1.02      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 1.32/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_750,plain,
% 1.32/1.02      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 1.32/1.02      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 1.32/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_1235,plain,
% 1.32/1.02      ( r2_hidden(sK1(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 1.32/1.02      | r1_tarski(sK7,X0) = iProver_top ),
% 1.32/1.02      inference(superposition,[status(thm)],[c_746,c_750]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_2,plain,
% 1.32/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.32/1.02      inference(cnf_transformation,[],[f35]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_755,plain,
% 1.32/1.02      ( r2_hidden(X0,X1) != iProver_top
% 1.32/1.02      | r2_hidden(X0,X2) = iProver_top
% 1.32/1.02      | r1_tarski(X1,X2) != iProver_top ),
% 1.32/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_1906,plain,
% 1.32/1.02      ( r2_hidden(sK1(sK7,X0),X1) = iProver_top
% 1.32/1.02      | r1_tarski(k1_relat_1(sK7),X1) != iProver_top
% 1.32/1.02      | r1_tarski(sK7,X0) = iProver_top ),
% 1.32/1.02      inference(superposition,[status(thm)],[c_1235,c_755]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_13,plain,
% 1.32/1.02      ( ~ r2_hidden(X0,X1)
% 1.32/1.02      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 1.32/1.02      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
% 1.32/1.02      | ~ v1_relat_1(X3) ),
% 1.32/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_275,plain,
% 1.32/1.02      ( ~ r2_hidden(X0,X1)
% 1.32/1.02      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 1.32/1.02      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
% 1.32/1.02      | sK7 != X3 ),
% 1.32/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_276,plain,
% 1.32/1.02      ( ~ r2_hidden(X0,X1)
% 1.32/1.02      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),sK7))
% 1.32/1.02      | ~ r2_hidden(k4_tarski(X0,X2),sK7) ),
% 1.32/1.02      inference(unflattening,[status(thm)],[c_275]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_742,plain,
% 1.32/1.02      ( r2_hidden(X0,X1) != iProver_top
% 1.32/1.02      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),sK7)) = iProver_top
% 1.32/1.02      | r2_hidden(k4_tarski(X0,X2),sK7) != iProver_top ),
% 1.32/1.02      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_6,plain,
% 1.32/1.02      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
% 1.32/1.02      | r1_tarski(X0,X1)
% 1.32/1.02      | ~ v1_relat_1(X0) ),
% 1.32/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_238,plain,
% 1.32/1.02      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
% 1.32/1.02      | r1_tarski(X0,X1)
% 1.32/1.02      | sK7 != X0 ),
% 1.32/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_239,plain,
% 1.32/1.02      ( ~ r2_hidden(k4_tarski(sK1(sK7,X0),sK2(sK7,X0)),X0)
% 1.32/1.02      | r1_tarski(sK7,X0) ),
% 1.32/1.02      inference(unflattening,[status(thm)],[c_238]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_745,plain,
% 1.32/1.02      ( r2_hidden(k4_tarski(sK1(sK7,X0),sK2(sK7,X0)),X0) != iProver_top
% 1.32/1.02      | r1_tarski(sK7,X0) = iProver_top ),
% 1.32/1.02      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_958,plain,
% 1.32/1.02      ( r2_hidden(k4_tarski(sK1(sK7,k5_relat_1(k6_relat_1(X0),sK7)),sK2(sK7,k5_relat_1(k6_relat_1(X0),sK7))),sK7) != iProver_top
% 1.32/1.02      | r2_hidden(sK1(sK7,k5_relat_1(k6_relat_1(X0),sK7)),X0) != iProver_top
% 1.32/1.02      | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) = iProver_top ),
% 1.32/1.02      inference(superposition,[status(thm)],[c_742,c_745]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_1299,plain,
% 1.32/1.02      ( r2_hidden(k4_tarski(sK1(sK7,k5_relat_1(k6_relat_1(X0),sK7)),sK2(sK7,k5_relat_1(k6_relat_1(X0),sK7))),sK7)
% 1.32/1.02      | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) ),
% 1.32/1.02      inference(instantiation,[status(thm)],[c_229]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_1300,plain,
% 1.32/1.02      ( r2_hidden(k4_tarski(sK1(sK7,k5_relat_1(k6_relat_1(X0),sK7)),sK2(sK7,k5_relat_1(k6_relat_1(X0),sK7))),sK7) = iProver_top
% 1.32/1.02      | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) = iProver_top ),
% 1.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1299]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_1378,plain,
% 1.32/1.02      ( r2_hidden(sK1(sK7,k5_relat_1(k6_relat_1(X0),sK7)),X0) != iProver_top
% 1.32/1.02      | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) = iProver_top ),
% 1.32/1.02      inference(global_propositional_subsumption,
% 1.32/1.02                [status(thm)],
% 1.32/1.02                [c_958,c_1300]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_2882,plain,
% 1.32/1.02      ( r1_tarski(k1_relat_1(sK7),X0) != iProver_top
% 1.32/1.02      | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) = iProver_top ),
% 1.32/1.02      inference(superposition,[status(thm)],[c_1906,c_1378]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_16,plain,
% 1.32/1.02      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~ v1_relat_1(X1) ),
% 1.32/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_290,plain,
% 1.32/1.02      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | sK7 != X1 ),
% 1.32/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_291,plain,
% 1.32/1.02      ( r1_tarski(k5_relat_1(k6_relat_1(X0),sK7),sK7) ),
% 1.32/1.02      inference(unflattening,[status(thm)],[c_290]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_741,plain,
% 1.32/1.02      ( r1_tarski(k5_relat_1(k6_relat_1(X0),sK7),sK7) = iProver_top ),
% 1.32/1.02      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_3,plain,
% 1.32/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.32/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_754,plain,
% 1.32/1.02      ( X0 = X1
% 1.32/1.02      | r1_tarski(X1,X0) != iProver_top
% 1.32/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 1.32/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_1719,plain,
% 1.32/1.02      ( k5_relat_1(k6_relat_1(X0),sK7) = sK7
% 1.32/1.02      | r1_tarski(sK7,k5_relat_1(k6_relat_1(X0),sK7)) != iProver_top ),
% 1.32/1.02      inference(superposition,[status(thm)],[c_741,c_754]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_3325,plain,
% 1.32/1.02      ( k5_relat_1(k6_relat_1(X0),sK7) = sK7
% 1.32/1.02      | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
% 1.32/1.02      inference(superposition,[status(thm)],[c_2882,c_1719]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_3461,plain,
% 1.32/1.02      ( k5_relat_1(k6_relat_1(sK6),sK7) = sK7 ),
% 1.32/1.02      inference(superposition,[status(thm)],[c_748,c_3325]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(c_18,negated_conjecture,
% 1.32/1.02      ( k5_relat_1(k6_relat_1(sK6),sK7) != sK7 ),
% 1.32/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.32/1.02  
% 1.32/1.02  cnf(contradiction,plain,
% 1.32/1.02      ( $false ),
% 1.32/1.02      inference(minisat,[status(thm)],[c_3461,c_18]) ).
% 1.32/1.02  
% 1.32/1.02  
% 1.32/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.32/1.02  
% 1.32/1.02  ------                               Statistics
% 1.32/1.02  
% 1.32/1.02  ------ General
% 1.32/1.02  
% 1.32/1.02  abstr_ref_over_cycles:                  0
% 1.32/1.02  abstr_ref_under_cycles:                 0
% 1.32/1.02  gc_basic_clause_elim:                   0
% 1.32/1.02  forced_gc_time:                         0
% 1.32/1.02  parsing_time:                           0.015
% 1.32/1.02  unif_index_cands_time:                  0.
% 1.32/1.02  unif_index_add_time:                    0.
% 1.32/1.02  orderings_time:                         0.
% 1.32/1.02  out_proof_time:                         0.006
% 1.32/1.02  total_time:                             0.151
% 1.32/1.02  num_of_symbols:                         46
% 1.32/1.02  num_of_terms:                           3441
% 1.32/1.02  
% 1.32/1.02  ------ Preprocessing
% 1.32/1.02  
% 1.32/1.02  num_of_splits:                          0
% 1.32/1.02  num_of_split_atoms:                     0
% 1.32/1.02  num_of_reused_defs:                     0
% 1.32/1.02  num_eq_ax_congr_red:                    32
% 1.32/1.02  num_of_sem_filtered_clauses:            1
% 1.32/1.02  num_of_subtypes:                        0
% 1.32/1.02  monotx_restored_types:                  0
% 1.32/1.02  sat_num_of_epr_types:                   0
% 1.32/1.02  sat_num_of_non_cyclic_types:            0
% 1.32/1.02  sat_guarded_non_collapsed_types:        0
% 1.32/1.02  num_pure_diseq_elim:                    0
% 1.32/1.02  simp_replaced_by:                       0
% 1.32/1.02  res_preprocessed:                       95
% 1.32/1.02  prep_upred:                             0
% 1.32/1.02  prep_unflattend:                        8
% 1.32/1.02  smt_new_axioms:                         0
% 1.32/1.02  pred_elim_cands:                        2
% 1.32/1.02  pred_elim:                              1
% 1.32/1.02  pred_elim_cl:                           2
% 1.32/1.02  pred_elim_cycles:                       3
% 1.32/1.02  merged_defs:                            0
% 1.32/1.02  merged_defs_ncl:                        0
% 1.32/1.02  bin_hyper_res:                          0
% 1.32/1.02  prep_cycles:                            4
% 1.32/1.02  pred_elim_time:                         0.003
% 1.32/1.02  splitting_time:                         0.
% 1.32/1.02  sem_filter_time:                        0.
% 1.32/1.02  monotx_time:                            0.
% 1.32/1.02  subtype_inf_time:                       0.
% 1.32/1.02  
% 1.32/1.02  ------ Problem properties
% 1.32/1.02  
% 1.32/1.02  clauses:                                18
% 1.32/1.02  conjectures:                            2
% 1.32/1.02  epr:                                    3
% 1.32/1.02  horn:                                   15
% 1.32/1.02  ground:                                 2
% 1.32/1.02  unary:                                  5
% 1.32/1.02  binary:                                 8
% 1.32/1.02  lits:                                   36
% 1.32/1.02  lits_eq:                                4
% 1.32/1.02  fd_pure:                                0
% 1.32/1.02  fd_pseudo:                              0
% 1.32/1.02  fd_cond:                                0
% 1.32/1.02  fd_pseudo_cond:                         3
% 1.32/1.02  ac_symbols:                             0
% 1.32/1.02  
% 1.32/1.02  ------ Propositional Solver
% 1.32/1.02  
% 1.32/1.02  prop_solver_calls:                      28
% 1.32/1.02  prop_fast_solver_calls:                 534
% 1.32/1.02  smt_solver_calls:                       0
% 1.32/1.02  smt_fast_solver_calls:                  0
% 1.32/1.02  prop_num_of_clauses:                    1227
% 1.32/1.02  prop_preprocess_simplified:             4635
% 1.32/1.02  prop_fo_subsumed:                       1
% 1.32/1.02  prop_solver_time:                       0.
% 1.32/1.02  smt_solver_time:                        0.
% 1.32/1.02  smt_fast_solver_time:                   0.
% 1.32/1.02  prop_fast_solver_time:                  0.
% 1.32/1.02  prop_unsat_core_time:                   0.
% 1.32/1.02  
% 1.32/1.02  ------ QBF
% 1.32/1.02  
% 1.32/1.02  qbf_q_res:                              0
% 1.32/1.02  qbf_num_tautologies:                    0
% 1.32/1.02  qbf_prep_cycles:                        0
% 1.32/1.02  
% 1.32/1.02  ------ BMC1
% 1.32/1.02  
% 1.32/1.02  bmc1_current_bound:                     -1
% 1.32/1.02  bmc1_last_solved_bound:                 -1
% 1.32/1.02  bmc1_unsat_core_size:                   -1
% 1.32/1.02  bmc1_unsat_core_parents_size:           -1
% 1.32/1.02  bmc1_merge_next_fun:                    0
% 1.32/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.32/1.02  
% 1.32/1.02  ------ Instantiation
% 1.32/1.02  
% 1.32/1.02  inst_num_of_clauses:                    369
% 1.32/1.02  inst_num_in_passive:                    80
% 1.32/1.02  inst_num_in_active:                     184
% 1.32/1.02  inst_num_in_unprocessed:                105
% 1.32/1.02  inst_num_of_loops:                      220
% 1.32/1.02  inst_num_of_learning_restarts:          0
% 1.32/1.02  inst_num_moves_active_passive:          33
% 1.32/1.02  inst_lit_activity:                      0
% 1.32/1.02  inst_lit_activity_moves:                0
% 1.32/1.02  inst_num_tautologies:                   0
% 1.32/1.02  inst_num_prop_implied:                  0
% 1.32/1.02  inst_num_existing_simplified:           0
% 1.32/1.02  inst_num_eq_res_simplified:             0
% 1.32/1.02  inst_num_child_elim:                    0
% 1.32/1.02  inst_num_of_dismatching_blockings:      78
% 1.32/1.02  inst_num_of_non_proper_insts:           317
% 1.32/1.02  inst_num_of_duplicates:                 0
% 1.32/1.02  inst_inst_num_from_inst_to_res:         0
% 1.32/1.02  inst_dismatching_checking_time:         0.
% 1.32/1.02  
% 1.32/1.02  ------ Resolution
% 1.32/1.02  
% 1.32/1.02  res_num_of_clauses:                     0
% 1.32/1.02  res_num_in_passive:                     0
% 1.32/1.02  res_num_in_active:                      0
% 1.32/1.02  res_num_of_loops:                       99
% 1.32/1.02  res_forward_subset_subsumed:            38
% 1.32/1.02  res_backward_subset_subsumed:           0
% 1.32/1.02  res_forward_subsumed:                   1
% 1.32/1.02  res_backward_subsumed:                  0
% 1.32/1.02  res_forward_subsumption_resolution:     0
% 1.32/1.02  res_backward_subsumption_resolution:    0
% 1.32/1.02  res_clause_to_clause_subsumption:       403
% 1.32/1.02  res_orphan_elimination:                 0
% 1.32/1.02  res_tautology_del:                      23
% 1.32/1.02  res_num_eq_res_simplified:              0
% 1.32/1.02  res_num_sel_changes:                    0
% 1.32/1.02  res_moves_from_active_to_pass:          0
% 1.32/1.02  
% 1.32/1.02  ------ Superposition
% 1.32/1.02  
% 1.32/1.02  sup_time_total:                         0.
% 1.32/1.02  sup_time_generating:                    0.
% 1.32/1.02  sup_time_sim_full:                      0.
% 1.32/1.02  sup_time_sim_immed:                     0.
% 1.32/1.02  
% 1.32/1.02  sup_num_of_clauses:                     87
% 1.32/1.02  sup_num_in_active:                      41
% 1.32/1.02  sup_num_in_passive:                     46
% 1.32/1.02  sup_num_of_loops:                       42
% 1.32/1.02  sup_fw_superposition:                   43
% 1.32/1.02  sup_bw_superposition:                   68
% 1.32/1.02  sup_immediate_simplified:               23
% 1.32/1.02  sup_given_eliminated:                   0
% 1.32/1.02  comparisons_done:                       0
% 1.32/1.02  comparisons_avoided:                    0
% 1.32/1.02  
% 1.32/1.02  ------ Simplifications
% 1.32/1.02  
% 1.32/1.02  
% 1.32/1.02  sim_fw_subset_subsumed:                 7
% 1.32/1.02  sim_bw_subset_subsumed:                 1
% 1.32/1.02  sim_fw_subsumed:                        9
% 1.32/1.02  sim_bw_subsumed:                        0
% 1.32/1.02  sim_fw_subsumption_res:                 0
% 1.32/1.02  sim_bw_subsumption_res:                 0
% 1.32/1.02  sim_tautology_del:                      14
% 1.32/1.02  sim_eq_tautology_del:                   1
% 1.32/1.02  sim_eq_res_simp:                        1
% 1.32/1.02  sim_fw_demodulated:                     0
% 1.32/1.02  sim_bw_demodulated:                     3
% 1.32/1.02  sim_light_normalised:                   7
% 1.32/1.02  sim_joinable_taut:                      0
% 1.32/1.02  sim_joinable_simp:                      0
% 1.32/1.02  sim_ac_normalised:                      0
% 1.32/1.02  sim_smt_subsumption:                    0
% 1.32/1.02  
%------------------------------------------------------------------------------
