%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0746+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:02 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 130 expanded)
%              Number of clauses        :   36 (  42 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  289 ( 490 expanded)
%              Number of equality atoms :   56 (  60 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f11])).

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

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f39])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f30])).

fof(f48,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ( v3_ordinal1(X1)
             => ~ r1_tarski(X0,X1) )
          & ! [X1] :
              ( r2_hidden(X1,X0)
             => v3_ordinal1(X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ( v3_ordinal1(X1)
             => ~ r1_tarski(X0,X1) )
          & ! [X2] :
              ( r2_hidden(X2,X0)
             => v3_ordinal1(X2) ) ) ),
    inference(rectify,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_tarski(X0,X1)
          | ~ v3_ordinal1(X1) )
      & ! [X2] :
          ( v3_ordinal1(X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_tarski(X0,X1)
            | ~ v3_ordinal1(X1) )
        & ! [X2] :
            ( v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) ) )
   => ( ! [X1] :
          ( ~ r1_tarski(sK5,X1)
          | ~ v3_ordinal1(X1) )
      & ! [X2] :
          ( v3_ordinal1(X2)
          | ~ r2_hidden(X2,sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK5,X1)
        | ~ v3_ordinal1(X1) )
    & ! [X2] :
        ( v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK5) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f32])).

fof(f50,plain,(
    ! [X2] :
      ( v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK5,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_938,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_933,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1626,plain,
    ( r2_hidden(X0,sK0(X1,X2)) != iProver_top
    | r2_hidden(X0,k3_tarski(X1)) = iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_933])).

cnf(c_4833,plain,
    ( r2_hidden(sK0(sK0(X0,X1),X2),k3_tarski(X0)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(sK0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_1626])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_939,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8673,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(sK0(X0,X1),k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4833,c_939])).

cnf(c_10,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r2_hidden(X0,k1_ordinal1(X1))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_227,plain,
    ( r2_hidden(X0,k1_ordinal1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_10,c_12])).

cnf(c_924,plain,
    ( r2_hidden(X0,k1_ordinal1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_1348,plain,
    ( r1_tarski(X0,k1_ordinal1(X1)) = iProver_top
    | r1_tarski(sK0(X0,k1_ordinal1(X1)),X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK0(X0,k1_ordinal1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_924,c_939])).

cnf(c_9605,plain,
    ( r1_tarski(X0,k1_ordinal1(k3_tarski(X0))) = iProver_top
    | v3_ordinal1(sK0(X0,k1_ordinal1(k3_tarski(X0)))) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8673,c_1348])).

cnf(c_9607,plain,
    ( r1_tarski(sK5,k1_ordinal1(k3_tarski(sK5))) = iProver_top
    | v3_ordinal1(sK0(sK5,k1_ordinal1(k3_tarski(sK5)))) != iProver_top
    | v3_ordinal1(k3_tarski(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9605])).

cnf(c_15,plain,
    ( r2_hidden(sK4(X0),X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_928,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_926,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1353,plain,
    ( v3_ordinal1(sK4(sK5)) = iProver_top
    | v3_ordinal1(k3_tarski(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_926])).

cnf(c_14,plain,
    ( ~ v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,plain,
    ( v3_ordinal1(sK4(X0)) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_29,plain,
    ( v3_ordinal1(sK4(sK5)) != iProver_top
    | v3_ordinal1(k3_tarski(sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1675,plain,
    ( v3_ordinal1(k3_tarski(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1353,c_29])).

cnf(c_1583,plain,
    ( ~ r2_hidden(sK0(sK5,k1_ordinal1(k3_tarski(sK5))),sK5)
    | v3_ordinal1(sK0(sK5,k1_ordinal1(k3_tarski(sK5)))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1584,plain,
    ( r2_hidden(sK0(sK5,k1_ordinal1(k3_tarski(sK5))),sK5) != iProver_top
    | v3_ordinal1(sK0(sK5,k1_ordinal1(k3_tarski(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_1366,plain,
    ( r2_hidden(sK0(sK5,k1_ordinal1(k3_tarski(sK5))),sK5)
    | r1_tarski(sK5,k1_ordinal1(k3_tarski(sK5))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1370,plain,
    ( r2_hidden(sK0(sK5,k1_ordinal1(k3_tarski(sK5))),sK5) = iProver_top
    | r1_tarski(sK5,k1_ordinal1(k3_tarski(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1366])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(sK5,X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1231,plain,
    ( ~ r1_tarski(sK5,k1_ordinal1(k3_tarski(sK5)))
    | ~ v3_ordinal1(k1_ordinal1(k3_tarski(sK5))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1232,plain,
    ( r1_tarski(sK5,k1_ordinal1(k3_tarski(sK5))) != iProver_top
    | v3_ordinal1(k1_ordinal1(k3_tarski(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1231])).

cnf(c_9,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1108,plain,
    ( v3_ordinal1(k1_ordinal1(k3_tarski(sK5)))
    | ~ v3_ordinal1(k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1112,plain,
    ( v3_ordinal1(k1_ordinal1(k3_tarski(sK5))) = iProver_top
    | v3_ordinal1(k3_tarski(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9607,c_1675,c_1584,c_1370,c_1232,c_1112])).


%------------------------------------------------------------------------------
