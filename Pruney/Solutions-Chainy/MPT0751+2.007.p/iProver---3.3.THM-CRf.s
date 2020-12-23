%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:03 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  232 (1229 expanded)
%              Number of clauses        :  177 ( 482 expanded)
%              Number of leaves         :   16 ( 217 expanded)
%              Depth                    :   27
%              Number of atoms          :  777 (5121 expanded)
%              Number of equality atoms :  374 (1235 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_ordinal1(X1) = X0
          & v3_ordinal1(X1) )
     => ( k1_ordinal1(sK2) = X0
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK1)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK1
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK1
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK1) ) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ( v4_ordinal1(sK1)
        & k1_ordinal1(sK2) = sK1
        & v3_ordinal1(sK2) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK1
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK1) ) )
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f33,f32])).

fof(f53,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
        & r2_hidden(sK0(X0),X0)
        & v3_ordinal1(sK0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
            & r2_hidden(sK0(X0),X0)
            & v3_ordinal1(sK0(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f52,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK0(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK0(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,
    ( v3_ordinal1(sK2)
    | ~ v4_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,
    ( k1_ordinal1(sK2) = sK1
    | ~ v4_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f59,plain,(
    ! [X2] :
      ( v4_ordinal1(sK1)
      | k1_ordinal1(X2) != sK1
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_24,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1458,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_ordinal1(k1_ordinal1(X0),X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1470,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_ordinal1(k1_ordinal1(X0),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_ordinal1(X1))
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1469,plain,
    ( r2_hidden(X0,k1_ordinal1(X1)) = iProver_top
    | r1_ordinal1(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_ordinal1(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1472,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k1_ordinal1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2570,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r1_ordinal1(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_1472])).

cnf(c_5026,plain,
    ( k1_ordinal1(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k1_ordinal1(X0),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_2570])).

cnf(c_3,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_78,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17335,plain,
    ( v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | r2_hidden(k1_ordinal1(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | k1_ordinal1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5026,c_78])).

cnf(c_17336,plain,
    ( k1_ordinal1(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k1_ordinal1(X0),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_17335])).

cnf(c_14,plain,
    ( ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1467,plain,
    ( r2_hidden(k1_ordinal1(sK0(X0)),X0) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17344,plain,
    ( k1_ordinal1(sK0(X0)) = X0
    | r2_hidden(sK0(X0),X0) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17336,c_1467])).

cnf(c_16,plain,
    ( v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_41,plain,
    ( v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( r2_hidden(sK0(X0),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_44,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17449,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | k1_ordinal1(sK0(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17344,c_41,c_44])).

cnf(c_17450,plain,
    ( k1_ordinal1(sK0(X0)) = X0
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17449])).

cnf(c_17457,plain,
    ( k1_ordinal1(sK0(sK1)) = sK1
    | v4_ordinal1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1458,c_17450])).

cnf(c_25,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ v4_ordinal1(sK1)
    | v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,plain,
    ( v4_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( ~ v4_ordinal1(sK1)
    | k1_ordinal1(sK2) = sK1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_30,plain,
    ( k1_ordinal1(sK2) = sK1
    | v4_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_43,plain,
    ( v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(sK0(sK1)) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_46,plain,
    ( r2_hidden(sK0(sK1),sK1) = iProver_top
    | v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_47,plain,
    ( r2_hidden(k1_ordinal1(sK0(X0)),X0) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_49,plain,
    ( r2_hidden(k1_ordinal1(sK0(sK1)),sK1) != iProver_top
    | v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X1))
    | r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_51,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK1))
    | r1_ordinal1(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_62,plain,
    ( k1_ordinal1(sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_70,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_69,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_71,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_5,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_73,plain,
    ( ~ r1_ordinal1(sK1,sK1)
    | r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_80,plain,
    ( v3_ordinal1(k1_ordinal1(sK1)) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_86,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_568,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X2,X3)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 != X3
    | k1_ordinal1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_569,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_ordinal1(X0),X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_573,plain,
    ( ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | r1_tarski(k1_ordinal1(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_3])).

cnf(c_574,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_ordinal1(X0),X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_573])).

cnf(c_575,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_ordinal1(X0),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_577,plain,
    ( r2_hidden(sK1,sK1) != iProver_top
    | r1_tarski(k1_ordinal1(sK1),sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_1098,plain,
    ( X0 != X1
    | k1_ordinal1(X0) = k1_ordinal1(X1) ),
    theory(equality)).

cnf(c_1103,plain,
    ( k1_ordinal1(sK1) = k1_ordinal1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_1525,plain,
    ( ~ r1_ordinal1(X0,k1_ordinal1(X0))
    | r1_tarski(X0,k1_ordinal1(X0))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1526,plain,
    ( r1_ordinal1(X0,k1_ordinal1(X0)) != iProver_top
    | r1_tarski(X0,k1_ordinal1(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_1528,plain,
    ( r1_ordinal1(sK1,k1_ordinal1(sK1)) != iProver_top
    | r1_tarski(sK1,k1_ordinal1(sK1)) = iProver_top
    | v3_ordinal1(k1_ordinal1(sK1)) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1526])).

cnf(c_1097,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1516,plain,
    ( X0 != X1
    | k1_ordinal1(X0) != X1
    | k1_ordinal1(X0) = X0 ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_1537,plain,
    ( X0 != k1_ordinal1(X0)
    | k1_ordinal1(X0) = X0
    | k1_ordinal1(X0) != k1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_1538,plain,
    ( k1_ordinal1(sK1) != k1_ordinal1(sK1)
    | k1_ordinal1(sK1) = sK1
    | sK1 != k1_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_1551,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(k1_ordinal1(X0)))
    | r1_ordinal1(X0,k1_ordinal1(X0))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1557,plain,
    ( r2_hidden(X0,k1_ordinal1(k1_ordinal1(X0))) != iProver_top
    | r1_ordinal1(X0,k1_ordinal1(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1551])).

cnf(c_1559,plain,
    ( r2_hidden(sK1,k1_ordinal1(k1_ordinal1(sK1))) != iProver_top
    | r1_ordinal1(sK1,k1_ordinal1(sK1)) = iProver_top
    | v3_ordinal1(k1_ordinal1(sK1)) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_1577,plain,
    ( ~ r1_tarski(X0,k1_ordinal1(X0))
    | ~ r1_tarski(k1_ordinal1(X0),X0)
    | X0 = k1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1578,plain,
    ( X0 = k1_ordinal1(X0)
    | r1_tarski(X0,k1_ordinal1(X0)) != iProver_top
    | r1_tarski(k1_ordinal1(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1577])).

cnf(c_1580,plain,
    ( sK1 = k1_ordinal1(sK1)
    | r1_tarski(k1_ordinal1(sK1),sK1) != iProver_top
    | r1_tarski(sK1,k1_ordinal1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k1_ordinal1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1668,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X0))
    | r2_hidden(X0,k1_ordinal1(k1_ordinal1(X0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1669,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) != iProver_top
    | r2_hidden(X0,k1_ordinal1(k1_ordinal1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1668])).

cnf(c_1671,plain,
    ( r2_hidden(sK1,k1_ordinal1(k1_ordinal1(sK1))) = iProver_top
    | r2_hidden(sK1,k1_ordinal1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_1894,plain,
    ( v3_ordinal1(k1_ordinal1(sK2))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1895,plain,
    ( v3_ordinal1(k1_ordinal1(sK2)) = iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_1605,plain,
    ( X0 != X1
    | X0 = k1_ordinal1(X2)
    | k1_ordinal1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_2080,plain,
    ( X0 = k1_ordinal1(sK2)
    | X0 != sK1
    | k1_ordinal1(sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_2081,plain,
    ( k1_ordinal1(sK2) != sK1
    | sK1 = k1_ordinal1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2080])).

cnf(c_3388,plain,
    ( ~ r2_hidden(sK0(sK1),sK1)
    | r1_ordinal1(k1_ordinal1(sK0(sK1)),sK1)
    | ~ v3_ordinal1(sK0(sK1))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3398,plain,
    ( r2_hidden(sK0(sK1),sK1) != iProver_top
    | r1_ordinal1(k1_ordinal1(sK0(sK1)),sK1) = iProver_top
    | v3_ordinal1(sK0(sK1)) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3388])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_ordinal1(X0),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1760,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X0))
    | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0))
    | ~ v4_ordinal1(k1_ordinal1(X0))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4079,plain,
    ( r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2))
    | ~ r2_hidden(sK2,k1_ordinal1(sK2))
    | ~ v4_ordinal1(k1_ordinal1(sK2))
    | ~ v3_ordinal1(k1_ordinal1(sK2))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_4080,plain,
    ( r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2)) = iProver_top
    | r2_hidden(sK2,k1_ordinal1(sK2)) != iProver_top
    | v4_ordinal1(k1_ordinal1(sK2)) != iProver_top
    | v3_ordinal1(k1_ordinal1(sK2)) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4079])).

cnf(c_4295,plain,
    ( r2_hidden(sK2,k1_ordinal1(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4296,plain,
    ( r2_hidden(sK2,k1_ordinal1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4295])).

cnf(c_1793,plain,
    ( r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1))
    | ~ r1_ordinal1(k1_ordinal1(X0),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4512,plain,
    ( r2_hidden(k1_ordinal1(sK0(sK1)),k1_ordinal1(sK1))
    | ~ r1_ordinal1(k1_ordinal1(sK0(sK1)),sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0(sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_4513,plain,
    ( r2_hidden(k1_ordinal1(sK0(sK1)),k1_ordinal1(sK1)) = iProver_top
    | r1_ordinal1(k1_ordinal1(sK0(sK1)),sK1) != iProver_top
    | v3_ordinal1(k1_ordinal1(sK0(sK1))) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4512])).

cnf(c_1102,plain,
    ( ~ v4_ordinal1(X0)
    | v4_ordinal1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2303,plain,
    ( ~ v4_ordinal1(X0)
    | v4_ordinal1(k1_ordinal1(X1))
    | k1_ordinal1(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_5884,plain,
    ( v4_ordinal1(k1_ordinal1(sK2))
    | ~ v4_ordinal1(sK1)
    | k1_ordinal1(sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_5885,plain,
    ( k1_ordinal1(sK2) != sK1
    | v4_ordinal1(k1_ordinal1(sK2)) = iProver_top
    | v4_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5884])).

cnf(c_1101,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2687,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_ordinal1(X3))
    | X0 != X2
    | X1 != k1_ordinal1(X3) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_6728,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_ordinal1(sK2))
    | X0 != X2
    | X1 != k1_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_2687])).

cnf(c_7112,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2))
    | X0 != k1_ordinal1(sK2)
    | X1 != k1_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_6728])).

cnf(c_7113,plain,
    ( X0 != k1_ordinal1(sK2)
    | X1 != k1_ordinal1(sK2)
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7112])).

cnf(c_7115,plain,
    ( sK1 != k1_ordinal1(sK2)
    | r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2)) != iProver_top
    | r2_hidden(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7113])).

cnf(c_7125,plain,
    ( ~ v3_ordinal1(sK0(sK1))
    | v3_ordinal1(k1_ordinal1(sK0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7126,plain,
    ( v3_ordinal1(sK0(sK1)) != iProver_top
    | v3_ordinal1(k1_ordinal1(sK0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7125])).

cnf(c_4636,plain,
    ( ~ r1_tarski(X0,sK0(sK1))
    | ~ r1_tarski(sK0(sK1),X0)
    | X0 = sK0(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7345,plain,
    ( ~ r1_tarski(sK0(sK1),sK0(sK1))
    | sK0(sK1) = sK0(sK1) ),
    inference(instantiation,[status(thm)],[c_4636])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_9945,plain,
    ( r1_tarski(sK0(sK1),sK0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1601,plain,
    ( r2_hidden(k1_ordinal1(X0),X1)
    | ~ r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1))
    | X1 = k1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9962,plain,
    ( ~ r2_hidden(k1_ordinal1(sK0(sK1)),k1_ordinal1(sK1))
    | r2_hidden(k1_ordinal1(sK0(sK1)),sK1)
    | sK1 = k1_ordinal1(sK0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1601])).

cnf(c_9963,plain,
    ( sK1 = k1_ordinal1(sK0(sK1))
    | r2_hidden(k1_ordinal1(sK0(sK1)),k1_ordinal1(sK1)) != iProver_top
    | r2_hidden(k1_ordinal1(sK0(sK1)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9962])).

cnf(c_1539,plain,
    ( X0 != X1
    | k1_ordinal1(X2) != X1
    | k1_ordinal1(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_1593,plain,
    ( X0 != k1_ordinal1(X1)
    | k1_ordinal1(X1) = X0
    | k1_ordinal1(X1) != k1_ordinal1(X1) ),
    inference(instantiation,[status(thm)],[c_1539])).

cnf(c_15431,plain,
    ( k1_ordinal1(sK0(sK1)) != k1_ordinal1(sK0(sK1))
    | k1_ordinal1(sK0(sK1)) = sK1
    | sK1 != k1_ordinal1(sK0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_10152,plain,
    ( X0 != sK0(sK1)
    | k1_ordinal1(X0) = k1_ordinal1(sK0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_16310,plain,
    ( sK0(sK1) != sK0(sK1)
    | k1_ordinal1(sK0(sK1)) = k1_ordinal1(sK0(sK1)) ),
    inference(instantiation,[status(thm)],[c_10152])).

cnf(c_17545,plain,
    ( k1_ordinal1(sK0(sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17457,c_24,c_25,c_26,c_30,c_43,c_46,c_49,c_51,c_62,c_70,c_71,c_73,c_80,c_86,c_577,c_1103,c_1528,c_1538,c_1559,c_1580,c_1671,c_1895,c_2081,c_3398,c_4080,c_4296,c_4513,c_5885,c_7115,c_7126,c_7345,c_9945,c_9963,c_15431,c_16310])).

cnf(c_18,negated_conjecture,
    ( v4_ordinal1(sK1)
    | ~ v3_ordinal1(X0)
    | k1_ordinal1(X0) != sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1463,plain,
    ( k1_ordinal1(X0) != sK1
    | v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17699,plain,
    ( v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(sK0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17545,c_1463])).

cnf(c_17885,plain,
    ( v4_ordinal1(sK1)
    | ~ v3_ordinal1(sK0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17699])).

cnf(c_1474,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1464,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k1_ordinal1(X0),X1) = iProver_top
    | v4_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1468,plain,
    ( r2_hidden(X0,k1_ordinal1(X1)) != iProver_top
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2380,plain,
    ( r2_hidden(X0,k1_ordinal1(X1)) != iProver_top
    | r1_ordinal1(k1_ordinal1(X0),X1) = iProver_top
    | v4_ordinal1(k1_ordinal1(X1)) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_1468])).

cnf(c_1799,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X1))
    | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1))
    | ~ v4_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k1_ordinal1(X1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1800,plain,
    ( r2_hidden(X0,k1_ordinal1(X1)) != iProver_top
    | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1)) = iProver_top
    | v4_ordinal1(k1_ordinal1(X1)) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1799])).

cnf(c_2279,plain,
    ( ~ r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1))
    | r1_ordinal1(k1_ordinal1(X0),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2283,plain,
    ( r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1)) != iProver_top
    | r1_ordinal1(k1_ordinal1(X0),X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2279])).

cnf(c_4052,plain,
    ( v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(k1_ordinal1(X1)) != iProver_top
    | r1_ordinal1(k1_ordinal1(X0),X1) = iProver_top
    | r2_hidden(X0,k1_ordinal1(X1)) != iProver_top
    | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2380,c_78])).

cnf(c_4053,plain,
    ( r2_hidden(X0,k1_ordinal1(X1)) != iProver_top
    | r1_ordinal1(k1_ordinal1(X0),X1) = iProver_top
    | v4_ordinal1(k1_ordinal1(X1)) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4052])).

cnf(c_4056,plain,
    ( r1_ordinal1(k1_ordinal1(X0),X0) = iProver_top
    | v4_ordinal1(k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_4053])).

cnf(c_1473,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_ordinal1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2379,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_1468])).

cnf(c_2638,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_ordinal1(X0,k1_ordinal1(X1)) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_2379])).

cnf(c_1475,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2962,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k1_ordinal1(X1)) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2638,c_1475])).

cnf(c_2636,plain,
    ( r1_ordinal1(X0,k1_ordinal1(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_2379])).

cnf(c_2719,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r1_ordinal1(X0,k1_ordinal1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2636,c_69,c_78,c_1557,c_1669])).

cnf(c_2720,plain,
    ( r1_ordinal1(X0,k1_ordinal1(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2719])).

cnf(c_2725,plain,
    ( r1_tarski(X0,k1_ordinal1(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2720,c_1475])).

cnf(c_2734,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r1_tarski(X0,k1_ordinal1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2725,c_78])).

cnf(c_2735,plain,
    ( r1_tarski(X0,k1_ordinal1(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2734])).

cnf(c_1479,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2741,plain,
    ( k1_ordinal1(X0) = X0
    | r1_tarski(k1_ordinal1(X0),X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2735,c_1479])).

cnf(c_2822,plain,
    ( r1_tarski(k1_ordinal1(X0),X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2741,c_9])).

cnf(c_2971,plain,
    ( r2_hidden(k1_ordinal1(k1_ordinal1(X0)),X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(k1_ordinal1(k1_ordinal1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2962,c_2822])).

cnf(c_1707,plain,
    ( ~ v3_ordinal1(k1_ordinal1(X0))
    | v3_ordinal1(k1_ordinal1(k1_ordinal1(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1708,plain,
    ( v3_ordinal1(k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(k1_ordinal1(k1_ordinal1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1707])).

cnf(c_3052,plain,
    ( v3_ordinal1(k1_ordinal1(X0)) != iProver_top
    | r2_hidden(k1_ordinal1(k1_ordinal1(X0)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2971,c_1708])).

cnf(c_3053,plain,
    ( r2_hidden(k1_ordinal1(k1_ordinal1(X0)),X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3052])).

cnf(c_3060,plain,
    ( r2_hidden(k1_ordinal1(X0),X0) != iProver_top
    | v4_ordinal1(X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_3053])).

cnf(c_1751,plain,
    ( ~ r2_hidden(k1_ordinal1(X0),X0)
    | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1752,plain,
    ( r2_hidden(k1_ordinal1(X0),X0) != iProver_top
    | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1751])).

cnf(c_2034,plain,
    ( ~ r1_ordinal1(k1_ordinal1(X0),X0)
    | r1_tarski(k1_ordinal1(X0),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2035,plain,
    ( r1_ordinal1(k1_ordinal1(X0),X0) != iProver_top
    | r1_tarski(k1_ordinal1(X0),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_2183,plain,
    ( ~ r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0))
    | r1_ordinal1(k1_ordinal1(X0),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2189,plain,
    ( r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0)) != iProver_top
    | r1_ordinal1(k1_ordinal1(X0),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2183])).

cnf(c_3642,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(k1_ordinal1(X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3060,c_9,c_78,c_1752,c_2035,c_2189,c_2741])).

cnf(c_3643,plain,
    ( r2_hidden(k1_ordinal1(X0),X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3642])).

cnf(c_3650,plain,
    ( r2_hidden(X0,X0) != iProver_top
    | v4_ordinal1(X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_3643])).

cnf(c_3660,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) != iProver_top
    | v4_ordinal1(k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_3650])).

cnf(c_4316,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4056,c_69,c_78,c_3660])).

cnf(c_4317,plain,
    ( v4_ordinal1(k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4316])).

cnf(c_17674,plain,
    ( v4_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17545,c_4317])).

cnf(c_17867,plain,
    ( ~ v4_ordinal1(sK1)
    | ~ v3_ordinal1(sK0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17674])).

cnf(c_7114,plain,
    ( ~ r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2))
    | r2_hidden(sK1,sK1)
    | sK1 != k1_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_7112])).

cnf(c_1670,plain,
    ( r2_hidden(sK1,k1_ordinal1(k1_ordinal1(sK1)))
    | ~ r2_hidden(sK1,k1_ordinal1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1668])).

cnf(c_1579,plain,
    ( ~ r1_tarski(k1_ordinal1(sK1),sK1)
    | ~ r1_tarski(sK1,k1_ordinal1(sK1))
    | sK1 = k1_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_1558,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(k1_ordinal1(sK1)))
    | r1_ordinal1(sK1,k1_ordinal1(sK1))
    | ~ v3_ordinal1(k1_ordinal1(sK1))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_1527,plain,
    ( ~ r1_ordinal1(sK1,k1_ordinal1(sK1))
    | r1_tarski(sK1,k1_ordinal1(sK1))
    | ~ v3_ordinal1(k1_ordinal1(sK1))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_1525])).

cnf(c_576,plain,
    ( ~ r2_hidden(sK1,sK1)
    | r1_tarski(k1_ordinal1(sK1),sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_338,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0))
    | k1_ordinal1(sK2) = sK1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_339,plain,
    ( v3_ordinal1(sK0(sK1))
    | ~ v3_ordinal1(sK1)
    | k1_ordinal1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_341,plain,
    ( v3_ordinal1(sK0(sK1))
    | k1_ordinal1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_24])).

cnf(c_324,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0))
    | v3_ordinal1(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_325,plain,
    ( v3_ordinal1(sK0(sK1))
    | v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_327,plain,
    ( v3_ordinal1(sK2)
    | v3_ordinal1(sK0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_24])).

cnf(c_328,plain,
    ( v3_ordinal1(sK0(sK1))
    | v3_ordinal1(sK2) ),
    inference(renaming,[status(thm)],[c_327])).

cnf(c_79,plain,
    ( v3_ordinal1(k1_ordinal1(sK1))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_42,plain,
    ( v4_ordinal1(sK1)
    | v3_ordinal1(sK0(sK1))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17885,c_17867,c_7114,c_5884,c_4295,c_4079,c_2081,c_1894,c_1670,c_1579,c_1558,c_1538,c_1527,c_1103,c_576,c_341,c_328,c_86,c_79,c_73,c_70,c_62,c_51,c_42,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.01/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/0.99  
% 3.01/0.99  ------  iProver source info
% 3.01/0.99  
% 3.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/0.99  git: non_committed_changes: false
% 3.01/0.99  git: last_make_outside_of_git: false
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    ""
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.99  --bmc1_ucm_extend_mode                  1
% 3.01/0.99  --bmc1_ucm_init_mode                    2
% 3.01/0.99  --bmc1_ucm_cone_mode                    none
% 3.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.99  --bmc1_ucm_relax_model                  4
% 3.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.99  --bmc1_ucm_layered_model                none
% 3.01/0.99  --bmc1_ucm_max_lemma_size               10
% 3.01/0.99  
% 3.01/0.99  ------ AIG Options
% 3.01/0.99  
% 3.01/0.99  --aig_mode                              false
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation Options
% 3.01/0.99  
% 3.01/0.99  --instantiation_flag                    true
% 3.01/0.99  --inst_sos_flag                         true
% 3.01/0.99  --inst_sos_phase                        true
% 3.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel_side                     num_symb
% 3.01/0.99  --inst_solver_per_active                1400
% 3.01/0.99  --inst_solver_calls_frac                1.
% 3.01/0.99  --inst_passive_queue_type               priority_queues
% 3.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.99  --inst_passive_queues_freq              [25;2]
% 3.01/0.99  --inst_dismatching                      true
% 3.01/0.99  --inst_eager_unprocessed_to_passive     true
% 3.01/0.99  --inst_prop_sim_given                   true
% 3.01/0.99  --inst_prop_sim_new                     false
% 3.01/0.99  --inst_subs_new                         false
% 3.01/0.99  --inst_eq_res_simp                      false
% 3.01/0.99  --inst_subs_given                       false
% 3.01/0.99  --inst_orphan_elimination               true
% 3.01/0.99  --inst_learning_loop_flag               true
% 3.01/0.99  --inst_learning_start                   3000
% 3.01/0.99  --inst_learning_factor                  2
% 3.01/0.99  --inst_start_prop_sim_after_learn       3
% 3.01/0.99  --inst_sel_renew                        solver
% 3.01/0.99  --inst_lit_activity_flag                true
% 3.01/0.99  --inst_restr_to_given                   false
% 3.01/0.99  --inst_activity_threshold               500
% 3.01/0.99  --inst_out_proof                        true
% 3.01/0.99  
% 3.01/0.99  ------ Resolution Options
% 3.01/0.99  
% 3.01/0.99  --resolution_flag                       true
% 3.01/0.99  --res_lit_sel                           adaptive
% 3.01/0.99  --res_lit_sel_side                      none
% 3.01/0.99  --res_ordering                          kbo
% 3.01/0.99  --res_to_prop_solver                    active
% 3.01/0.99  --res_prop_simpl_new                    false
% 3.01/0.99  --res_prop_simpl_given                  true
% 3.01/0.99  --res_passive_queue_type                priority_queues
% 3.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.99  --res_passive_queues_freq               [15;5]
% 3.01/0.99  --res_forward_subs                      full
% 3.01/0.99  --res_backward_subs                     full
% 3.01/0.99  --res_forward_subs_resolution           true
% 3.01/0.99  --res_backward_subs_resolution          true
% 3.01/0.99  --res_orphan_elimination                true
% 3.01/0.99  --res_time_limit                        2.
% 3.01/0.99  --res_out_proof                         true
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Options
% 3.01/0.99  
% 3.01/0.99  --superposition_flag                    true
% 3.01/0.99  --sup_passive_queue_type                priority_queues
% 3.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.99  --demod_completeness_check              fast
% 3.01/0.99  --demod_use_ground                      true
% 3.01/0.99  --sup_to_prop_solver                    passive
% 3.01/0.99  --sup_prop_simpl_new                    true
% 3.01/0.99  --sup_prop_simpl_given                  true
% 3.01/0.99  --sup_fun_splitting                     true
% 3.01/0.99  --sup_smt_interval                      50000
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Simplification Setup
% 3.01/0.99  
% 3.01/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.01/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.01/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.01/0.99  --sup_immed_triv                        [TrivRules]
% 3.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_bw_main                     []
% 3.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_input_bw                          []
% 3.01/0.99  
% 3.01/0.99  ------ Combination Options
% 3.01/0.99  
% 3.01/0.99  --comb_res_mult                         3
% 3.01/0.99  --comb_sup_mult                         2
% 3.01/0.99  --comb_inst_mult                        10
% 3.01/0.99  
% 3.01/0.99  ------ Debug Options
% 3.01/0.99  
% 3.01/0.99  --dbg_backtrace                         false
% 3.01/0.99  --dbg_dump_prop_clauses                 false
% 3.01/0.99  --dbg_dump_prop_clauses_file            -
% 3.01/0.99  --dbg_out_stat                          false
% 3.01/0.99  ------ Parsing...
% 3.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/0.99  ------ Proving...
% 3.01/0.99  ------ Problem Properties 
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  clauses                                 23
% 3.01/0.99  conjectures                             6
% 3.01/0.99  EPR                                     6
% 3.01/0.99  Horn                                    20
% 3.01/0.99  unary                                   4
% 3.01/0.99  binary                                  4
% 3.01/0.99  lits                                    65
% 3.01/0.99  lits eq                                 8
% 3.01/0.99  fd_pure                                 0
% 3.01/0.99  fd_pseudo                               0
% 3.01/0.99  fd_cond                                 0
% 3.01/0.99  fd_pseudo_cond                          2
% 3.01/0.99  AC symbols                              0
% 3.01/0.99  
% 3.01/0.99  ------ Schedule dynamic 5 is on 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  Current options:
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    ""
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.99  --bmc1_ucm_extend_mode                  1
% 3.01/0.99  --bmc1_ucm_init_mode                    2
% 3.01/0.99  --bmc1_ucm_cone_mode                    none
% 3.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.99  --bmc1_ucm_relax_model                  4
% 3.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.99  --bmc1_ucm_layered_model                none
% 3.01/0.99  --bmc1_ucm_max_lemma_size               10
% 3.01/0.99  
% 3.01/0.99  ------ AIG Options
% 3.01/0.99  
% 3.01/0.99  --aig_mode                              false
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation Options
% 3.01/0.99  
% 3.01/0.99  --instantiation_flag                    true
% 3.01/0.99  --inst_sos_flag                         true
% 3.01/0.99  --inst_sos_phase                        true
% 3.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel_side                     none
% 3.01/0.99  --inst_solver_per_active                1400
% 3.01/0.99  --inst_solver_calls_frac                1.
% 3.01/0.99  --inst_passive_queue_type               priority_queues
% 3.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.99  --inst_passive_queues_freq              [25;2]
% 3.01/0.99  --inst_dismatching                      true
% 3.01/0.99  --inst_eager_unprocessed_to_passive     true
% 3.01/0.99  --inst_prop_sim_given                   true
% 3.01/0.99  --inst_prop_sim_new                     false
% 3.01/0.99  --inst_subs_new                         false
% 3.01/0.99  --inst_eq_res_simp                      false
% 3.01/0.99  --inst_subs_given                       false
% 3.01/0.99  --inst_orphan_elimination               true
% 3.01/0.99  --inst_learning_loop_flag               true
% 3.01/0.99  --inst_learning_start                   3000
% 3.01/0.99  --inst_learning_factor                  2
% 3.01/0.99  --inst_start_prop_sim_after_learn       3
% 3.01/0.99  --inst_sel_renew                        solver
% 3.01/0.99  --inst_lit_activity_flag                true
% 3.01/0.99  --inst_restr_to_given                   false
% 3.01/0.99  --inst_activity_threshold               500
% 3.01/0.99  --inst_out_proof                        true
% 3.01/0.99  
% 3.01/0.99  ------ Resolution Options
% 3.01/0.99  
% 3.01/0.99  --resolution_flag                       false
% 3.01/0.99  --res_lit_sel                           adaptive
% 3.01/0.99  --res_lit_sel_side                      none
% 3.01/0.99  --res_ordering                          kbo
% 3.01/0.99  --res_to_prop_solver                    active
% 3.01/0.99  --res_prop_simpl_new                    false
% 3.01/0.99  --res_prop_simpl_given                  true
% 3.01/0.99  --res_passive_queue_type                priority_queues
% 3.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.99  --res_passive_queues_freq               [15;5]
% 3.01/0.99  --res_forward_subs                      full
% 3.01/0.99  --res_backward_subs                     full
% 3.01/0.99  --res_forward_subs_resolution           true
% 3.01/0.99  --res_backward_subs_resolution          true
% 3.01/0.99  --res_orphan_elimination                true
% 3.01/0.99  --res_time_limit                        2.
% 3.01/0.99  --res_out_proof                         true
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Options
% 3.01/0.99  
% 3.01/0.99  --superposition_flag                    true
% 3.01/0.99  --sup_passive_queue_type                priority_queues
% 3.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.99  --demod_completeness_check              fast
% 3.01/0.99  --demod_use_ground                      true
% 3.01/0.99  --sup_to_prop_solver                    passive
% 3.01/0.99  --sup_prop_simpl_new                    true
% 3.01/0.99  --sup_prop_simpl_given                  true
% 3.01/0.99  --sup_fun_splitting                     true
% 3.01/0.99  --sup_smt_interval                      50000
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Simplification Setup
% 3.01/0.99  
% 3.01/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.01/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.01/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.01/0.99  --sup_immed_triv                        [TrivRules]
% 3.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_bw_main                     []
% 3.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_input_bw                          []
% 3.01/0.99  
% 3.01/0.99  ------ Combination Options
% 3.01/0.99  
% 3.01/0.99  --comb_res_mult                         3
% 3.01/0.99  --comb_sup_mult                         2
% 3.01/0.99  --comb_inst_mult                        10
% 3.01/0.99  
% 3.01/0.99  ------ Debug Options
% 3.01/0.99  
% 3.01/0.99  --dbg_backtrace                         false
% 3.01/0.99  --dbg_dump_prop_clauses                 false
% 3.01/0.99  --dbg_dump_prop_clauses_file            -
% 3.01/0.99  --dbg_out_stat                          false
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ Proving...
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  % SZS status Theorem for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  fof(f9,conjecture,(
% 3.01/0.99    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f10,negated_conjecture,(
% 3.01/0.99    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 3.01/0.99    inference(negated_conjecture,[],[f9])).
% 3.01/0.99  
% 3.01/0.99  fof(f11,plain,(
% 3.01/0.99    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 3.01/0.99    inference(rectify,[],[f10])).
% 3.01/0.99  
% 3.01/0.99  fof(f20,plain,(
% 3.01/0.99    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f11])).
% 3.01/0.99  
% 3.01/0.99  fof(f33,plain,(
% 3.01/0.99    ( ! [X0] : (? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1)) => (k1_ordinal1(sK2) = X0 & v3_ordinal1(sK2))) )),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f32,plain,(
% 3.01/0.99    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK1) & ? [X1] : (k1_ordinal1(X1) = sK1 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK1 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f34,plain,(
% 3.01/0.99    ((v4_ordinal1(sK1) & (k1_ordinal1(sK2) = sK1 & v3_ordinal1(sK2))) | (! [X2] : (k1_ordinal1(X2) != sK1 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK1))) & v3_ordinal1(sK1)),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f33,f32])).
% 3.01/0.99  
% 3.01/0.99  fof(f53,plain,(
% 3.01/0.99    v3_ordinal1(sK1)),
% 3.01/0.99    inference(cnf_transformation,[],[f34])).
% 3.01/0.99  
% 3.01/0.99  fof(f6,axiom,(
% 3.01/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f16,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f6])).
% 3.01/0.99  
% 3.01/0.99  fof(f26,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(nnf_transformation,[],[f16])).
% 3.01/0.99  
% 3.01/0.99  fof(f45,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f26])).
% 3.01/0.99  
% 3.01/0.99  fof(f7,axiom,(
% 3.01/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f17,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f7])).
% 3.01/0.99  
% 3.01/0.99  fof(f27,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(nnf_transformation,[],[f17])).
% 3.01/0.99  
% 3.01/0.99  fof(f48,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f27])).
% 3.01/0.99  
% 3.01/0.99  fof(f4,axiom,(
% 3.01/0.99    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f24,plain,(
% 3.01/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.01/0.99    inference(nnf_transformation,[],[f4])).
% 3.01/0.99  
% 3.01/0.99  fof(f25,plain,(
% 3.01/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.01/0.99    inference(flattening,[],[f24])).
% 3.01/0.99  
% 3.01/0.99  fof(f41,plain,(
% 3.01/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f25])).
% 3.01/0.99  
% 3.01/0.99  fof(f2,axiom,(
% 3.01/0.99    ! [X0] : (v3_ordinal1(X0) => (v3_ordinal1(k1_ordinal1(X0)) & ~v1_xboole_0(k1_ordinal1(X0))))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f12,plain,(
% 3.01/0.99    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.01/0.99    inference(pure_predicate_removal,[],[f2])).
% 3.01/0.99  
% 3.01/0.99  fof(f13,plain,(
% 3.01/0.99    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f12])).
% 3.01/0.99  
% 3.01/0.99  fof(f38,plain,(
% 3.01/0.99    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f13])).
% 3.01/0.99  
% 3.01/0.99  fof(f8,axiom,(
% 3.01/0.99    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f18,plain,(
% 3.01/0.99    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f8])).
% 3.01/0.99  
% 3.01/0.99  fof(f19,plain,(
% 3.01/0.99    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(flattening,[],[f18])).
% 3.01/0.99  
% 3.01/0.99  fof(f28,plain,(
% 3.01/0.99    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(nnf_transformation,[],[f19])).
% 3.01/0.99  
% 3.01/0.99  fof(f29,plain,(
% 3.01/0.99    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(rectify,[],[f28])).
% 3.01/0.99  
% 3.01/0.99  fof(f30,plain,(
% 3.01/0.99    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK0(X0)),X0) & r2_hidden(sK0(X0),X0) & v3_ordinal1(sK0(X0))))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f31,plain,(
% 3.01/0.99    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK0(X0)),X0) & r2_hidden(sK0(X0),X0) & v3_ordinal1(sK0(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.01/0.99  
% 3.01/0.99  fof(f52,plain,(
% 3.01/0.99    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK0(X0)),X0) | ~v3_ordinal1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f31])).
% 3.01/0.99  
% 3.01/0.99  fof(f50,plain,(
% 3.01/0.99    ( ! [X0] : (v4_ordinal1(X0) | v3_ordinal1(sK0(X0)) | ~v3_ordinal1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f31])).
% 3.01/0.99  
% 3.01/0.99  fof(f51,plain,(
% 3.01/0.99    ( ! [X0] : (v4_ordinal1(X0) | r2_hidden(sK0(X0),X0) | ~v3_ordinal1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f31])).
% 3.01/0.99  
% 3.01/0.99  fof(f54,plain,(
% 3.01/0.99    v3_ordinal1(sK2) | ~v4_ordinal1(sK1)),
% 3.01/0.99    inference(cnf_transformation,[],[f34])).
% 3.01/0.99  
% 3.01/0.99  fof(f56,plain,(
% 3.01/0.99    k1_ordinal1(sK2) = sK1 | ~v4_ordinal1(sK1)),
% 3.01/0.99    inference(cnf_transformation,[],[f34])).
% 3.01/0.99  
% 3.01/0.99  fof(f47,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f27])).
% 3.01/0.99  
% 3.01/0.99  fof(f5,axiom,(
% 3.01/0.99    ! [X0] : k1_ordinal1(X0) != X0),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f44,plain,(
% 3.01/0.99    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 3.01/0.99    inference(cnf_transformation,[],[f5])).
% 3.01/0.99  
% 3.01/0.99  fof(f43,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 3.01/0.99    inference(cnf_transformation,[],[f25])).
% 3.01/0.99  
% 3.01/0.99  fof(f62,plain,(
% 3.01/0.99    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 3.01/0.99    inference(equality_resolution,[],[f43])).
% 3.01/0.99  
% 3.01/0.99  fof(f3,axiom,(
% 3.01/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f14,plain,(
% 3.01/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f3])).
% 3.01/0.99  
% 3.01/0.99  fof(f15,plain,(
% 3.01/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(flattening,[],[f14])).
% 3.01/0.99  
% 3.01/0.99  fof(f23,plain,(
% 3.01/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.01/0.99    inference(nnf_transformation,[],[f15])).
% 3.01/0.99  
% 3.01/0.99  fof(f39,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f23])).
% 3.01/0.99  
% 3.01/0.99  fof(f1,axiom,(
% 3.01/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f21,plain,(
% 3.01/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.01/0.99    inference(nnf_transformation,[],[f1])).
% 3.01/0.99  
% 3.01/0.99  fof(f22,plain,(
% 3.01/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.01/0.99    inference(flattening,[],[f21])).
% 3.01/0.99  
% 3.01/0.99  fof(f37,plain,(
% 3.01/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f42,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f25])).
% 3.01/0.99  
% 3.01/0.99  fof(f49,plain,(
% 3.01/0.99    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f31])).
% 3.01/0.99  
% 3.01/0.99  fof(f35,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.01/0.99    inference(cnf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f61,plain,(
% 3.01/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.01/0.99    inference(equality_resolution,[],[f35])).
% 3.01/0.99  
% 3.01/0.99  fof(f59,plain,(
% 3.01/0.99    ( ! [X2] : (v4_ordinal1(sK1) | k1_ordinal1(X2) != sK1 | ~v3_ordinal1(X2)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f34])).
% 3.01/0.99  
% 3.01/0.99  cnf(c_24,negated_conjecture,
% 3.01/0.99      ( v3_ordinal1(sK1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1458,plain,
% 3.01/0.99      ( v3_ordinal1(sK1) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_11,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,X1)
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(X0),X1)
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1470,plain,
% 3.01/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(X0),X1) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_12,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X1))
% 3.01/0.99      | ~ r1_ordinal1(X0,X1)
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1469,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X1)) = iProver_top
% 3.01/0.99      | r1_ordinal1(X0,X1) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_8,plain,
% 3.01/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_ordinal1(X1)) | X1 = X0 ),
% 3.01/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1472,plain,
% 3.01/0.99      ( X0 = X1
% 3.01/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.01/0.99      | r2_hidden(X1,k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2570,plain,
% 3.01/0.99      ( X0 = X1
% 3.01/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.01/0.99      | r1_ordinal1(X1,X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1469,c_1472]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_5026,plain,
% 3.01/0.99      ( k1_ordinal1(X0) = X1
% 3.01/0.99      | r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),X1) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1470,c_2570]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3,plain,
% 3.01/0.99      ( ~ v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_78,plain,
% 3.01/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17335,plain,
% 3.01/0.99      ( v3_ordinal1(X1) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),X1) = iProver_top
% 3.01/0.99      | r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | k1_ordinal1(X0) = X1 ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_5026,c_78]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17336,plain,
% 3.01/0.99      ( k1_ordinal1(X0) = X1
% 3.01/0.99      | r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),X1) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_17335]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_14,plain,
% 3.01/0.99      ( ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
% 3.01/0.99      | v4_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1467,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(sK0(X0)),X0) != iProver_top
% 3.01/0.99      | v4_ordinal1(X0) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17344,plain,
% 3.01/0.99      ( k1_ordinal1(sK0(X0)) = X0
% 3.01/0.99      | r2_hidden(sK0(X0),X0) != iProver_top
% 3.01/0.99      | v4_ordinal1(X0) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(sK0(X0)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_17336,c_1467]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_16,plain,
% 3.01/0.99      ( v4_ordinal1(X0) | ~ v3_ordinal1(X0) | v3_ordinal1(sK0(X0)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_41,plain,
% 3.01/0.99      ( v4_ordinal1(X0) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(sK0(X0)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_15,plain,
% 3.01/0.99      ( r2_hidden(sK0(X0),X0) | v4_ordinal1(X0) | ~ v3_ordinal1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_44,plain,
% 3.01/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.01/0.99      | v4_ordinal1(X0) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17449,plain,
% 3.01/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v4_ordinal1(X0) = iProver_top
% 3.01/0.99      | k1_ordinal1(sK0(X0)) = X0 ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_17344,c_41,c_44]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17450,plain,
% 3.01/0.99      ( k1_ordinal1(sK0(X0)) = X0
% 3.01/0.99      | v4_ordinal1(X0) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_17449]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17457,plain,
% 3.01/0.99      ( k1_ordinal1(sK0(sK1)) = sK1 | v4_ordinal1(sK1) = iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1458,c_17450]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_25,plain,
% 3.01/0.99      ( v3_ordinal1(sK1) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_23,negated_conjecture,
% 3.01/0.99      ( ~ v4_ordinal1(sK1) | v3_ordinal1(sK2) ),
% 3.01/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_26,plain,
% 3.01/0.99      ( v4_ordinal1(sK1) != iProver_top
% 3.01/0.99      | v3_ordinal1(sK2) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_21,negated_conjecture,
% 3.01/0.99      ( ~ v4_ordinal1(sK1) | k1_ordinal1(sK2) = sK1 ),
% 3.01/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_30,plain,
% 3.01/0.99      ( k1_ordinal1(sK2) = sK1 | v4_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_43,plain,
% 3.01/0.99      ( v4_ordinal1(sK1) = iProver_top
% 3.01/0.99      | v3_ordinal1(sK0(sK1)) = iProver_top
% 3.01/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_41]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_46,plain,
% 3.01/0.99      ( r2_hidden(sK0(sK1),sK1) = iProver_top
% 3.01/0.99      | v4_ordinal1(sK1) = iProver_top
% 3.01/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_44]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_47,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(sK0(X0)),X0) != iProver_top
% 3.01/0.99      | v4_ordinal1(X0) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_49,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(sK0(sK1)),sK1) != iProver_top
% 3.01/0.99      | v4_ordinal1(sK1) = iProver_top
% 3.01/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_47]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_13,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k1_ordinal1(X1))
% 3.01/0.99      | r1_ordinal1(X0,X1)
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_51,plain,
% 3.01/0.99      ( ~ r2_hidden(sK1,k1_ordinal1(sK1))
% 3.01/0.99      | r1_ordinal1(sK1,sK1)
% 3.01/0.99      | ~ v3_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_9,plain,
% 3.01/0.99      ( k1_ordinal1(X0) != X0 ),
% 3.01/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_62,plain,
% 3.01/0.99      ( k1_ordinal1(sK1) != sK1 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_6,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X0)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_70,plain,
% 3.01/0.99      ( r2_hidden(sK1,k1_ordinal1(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_69,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X0)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_71,plain,
% 3.01/0.99      ( r2_hidden(sK1,k1_ordinal1(sK1)) = iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_69]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_5,plain,
% 3.01/0.99      ( ~ r1_ordinal1(X0,X1)
% 3.01/0.99      | r1_tarski(X0,X1)
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_73,plain,
% 3.01/0.99      ( ~ r1_ordinal1(sK1,sK1)
% 3.01/0.99      | r1_tarski(sK1,sK1)
% 3.01/0.99      | ~ v3_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_80,plain,
% 3.01/0.99      ( v3_ordinal1(k1_ordinal1(sK1)) = iProver_top
% 3.01/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_78]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_0,plain,
% 3.01/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.01/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_86,plain,
% 3.01/0.99      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_568,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,X1)
% 3.01/0.99      | r1_tarski(X2,X3)
% 3.01/0.99      | ~ v3_ordinal1(X2)
% 3.01/0.99      | ~ v3_ordinal1(X3)
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(X1)
% 3.01/0.99      | X1 != X3
% 3.01/0.99      | k1_ordinal1(X0) != X2 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_569,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,X1)
% 3.01/0.99      | r1_tarski(k1_ordinal1(X0),X1)
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(X1)
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(X0)) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_568]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_573,plain,
% 3.01/0.99      ( ~ v3_ordinal1(X1)
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | r1_tarski(k1_ordinal1(X0),X1)
% 3.01/0.99      | ~ r2_hidden(X0,X1) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_569,c_3]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_574,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,X1)
% 3.01/0.99      | r1_tarski(k1_ordinal1(X0),X1)
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(X1) ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_573]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_575,plain,
% 3.01/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | r1_tarski(k1_ordinal1(X0),X1) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_577,plain,
% 3.01/0.99      ( r2_hidden(sK1,sK1) != iProver_top
% 3.01/0.99      | r1_tarski(k1_ordinal1(sK1),sK1) = iProver_top
% 3.01/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_575]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1098,plain,
% 3.01/0.99      ( X0 != X1 | k1_ordinal1(X0) = k1_ordinal1(X1) ),
% 3.01/0.99      theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1103,plain,
% 3.01/0.99      ( k1_ordinal1(sK1) = k1_ordinal1(sK1) | sK1 != sK1 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1098]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1525,plain,
% 3.01/0.99      ( ~ r1_ordinal1(X0,k1_ordinal1(X0))
% 3.01/0.99      | r1_tarski(X0,k1_ordinal1(X0))
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(X0)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1526,plain,
% 3.01/0.99      ( r1_ordinal1(X0,k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | r1_tarski(X0,k1_ordinal1(X0)) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1525]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1528,plain,
% 3.01/0.99      ( r1_ordinal1(sK1,k1_ordinal1(sK1)) != iProver_top
% 3.01/0.99      | r1_tarski(sK1,k1_ordinal1(sK1)) = iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(sK1)) != iProver_top
% 3.01/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1526]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1097,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1516,plain,
% 3.01/0.99      ( X0 != X1 | k1_ordinal1(X0) != X1 | k1_ordinal1(X0) = X0 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1097]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1537,plain,
% 3.01/0.99      ( X0 != k1_ordinal1(X0)
% 3.01/0.99      | k1_ordinal1(X0) = X0
% 3.01/0.99      | k1_ordinal1(X0) != k1_ordinal1(X0) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1516]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1538,plain,
% 3.01/0.99      ( k1_ordinal1(sK1) != k1_ordinal1(sK1)
% 3.01/0.99      | k1_ordinal1(sK1) = sK1
% 3.01/0.99      | sK1 != k1_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1537]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1551,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k1_ordinal1(k1_ordinal1(X0)))
% 3.01/0.99      | r1_ordinal1(X0,k1_ordinal1(X0))
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(X0)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1557,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(k1_ordinal1(X0))) != iProver_top
% 3.01/0.99      | r1_ordinal1(X0,k1_ordinal1(X0)) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1551]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1559,plain,
% 3.01/0.99      ( r2_hidden(sK1,k1_ordinal1(k1_ordinal1(sK1))) != iProver_top
% 3.01/0.99      | r1_ordinal1(sK1,k1_ordinal1(sK1)) = iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(sK1)) != iProver_top
% 3.01/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1557]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1577,plain,
% 3.01/0.99      ( ~ r1_tarski(X0,k1_ordinal1(X0))
% 3.01/0.99      | ~ r1_tarski(k1_ordinal1(X0),X0)
% 3.01/0.99      | X0 = k1_ordinal1(X0) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1578,plain,
% 3.01/0.99      ( X0 = k1_ordinal1(X0)
% 3.01/0.99      | r1_tarski(X0,k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | r1_tarski(k1_ordinal1(X0),X0) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1577]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1580,plain,
% 3.01/0.99      ( sK1 = k1_ordinal1(sK1)
% 3.01/0.99      | r1_tarski(k1_ordinal1(sK1),sK1) != iProver_top
% 3.01/0.99      | r1_tarski(sK1,k1_ordinal1(sK1)) != iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1578]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1668,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k1_ordinal1(X0))
% 3.01/0.99      | r2_hidden(X0,k1_ordinal1(k1_ordinal1(X0))) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1669,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | r2_hidden(X0,k1_ordinal1(k1_ordinal1(X0))) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1668]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1671,plain,
% 3.01/0.99      ( r2_hidden(sK1,k1_ordinal1(k1_ordinal1(sK1))) = iProver_top
% 3.01/0.99      | r2_hidden(sK1,k1_ordinal1(sK1)) != iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1669]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1894,plain,
% 3.01/0.99      ( v3_ordinal1(k1_ordinal1(sK2)) | ~ v3_ordinal1(sK2) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1895,plain,
% 3.01/0.99      ( v3_ordinal1(k1_ordinal1(sK2)) = iProver_top
% 3.01/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1605,plain,
% 3.01/0.99      ( X0 != X1 | X0 = k1_ordinal1(X2) | k1_ordinal1(X2) != X1 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1097]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2080,plain,
% 3.01/0.99      ( X0 = k1_ordinal1(sK2) | X0 != sK1 | k1_ordinal1(sK2) != sK1 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1605]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2081,plain,
% 3.01/0.99      ( k1_ordinal1(sK2) != sK1 | sK1 = k1_ordinal1(sK2) | sK1 != sK1 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_2080]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3388,plain,
% 3.01/0.99      ( ~ r2_hidden(sK0(sK1),sK1)
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(sK0(sK1)),sK1)
% 3.01/0.99      | ~ v3_ordinal1(sK0(sK1))
% 3.01/0.99      | ~ v3_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3398,plain,
% 3.01/0.99      ( r2_hidden(sK0(sK1),sK1) != iProver_top
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(sK0(sK1)),sK1) = iProver_top
% 3.01/0.99      | v3_ordinal1(sK0(sK1)) != iProver_top
% 3.01/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_3388]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,X1)
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),X1)
% 3.01/0.99      | ~ v4_ordinal1(X1)
% 3.01/0.99      | ~ v3_ordinal1(X1)
% 3.01/0.99      | ~ v3_ordinal1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1760,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k1_ordinal1(X0))
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0))
% 3.01/0.99      | ~ v4_ordinal1(k1_ordinal1(X0))
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(X0)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4079,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2))
% 3.01/0.99      | ~ r2_hidden(sK2,k1_ordinal1(sK2))
% 3.01/0.99      | ~ v4_ordinal1(k1_ordinal1(sK2))
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(sK2))
% 3.01/0.99      | ~ v3_ordinal1(sK2) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1760]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4080,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2)) = iProver_top
% 3.01/0.99      | r2_hidden(sK2,k1_ordinal1(sK2)) != iProver_top
% 3.01/0.99      | v4_ordinal1(k1_ordinal1(sK2)) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(sK2)) != iProver_top
% 3.01/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_4079]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4295,plain,
% 3.01/0.99      ( r2_hidden(sK2,k1_ordinal1(sK2)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4296,plain,
% 3.01/0.99      ( r2_hidden(sK2,k1_ordinal1(sK2)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_4295]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1793,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1))
% 3.01/0.99      | ~ r1_ordinal1(k1_ordinal1(X0),X1)
% 3.01/0.99      | ~ v3_ordinal1(X1)
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(X0)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4512,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(sK0(sK1)),k1_ordinal1(sK1))
% 3.01/0.99      | ~ r1_ordinal1(k1_ordinal1(sK0(sK1)),sK1)
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(sK0(sK1)))
% 3.01/0.99      | ~ v3_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1793]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4513,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(sK0(sK1)),k1_ordinal1(sK1)) = iProver_top
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(sK0(sK1)),sK1) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(sK0(sK1))) != iProver_top
% 3.01/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_4512]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1102,plain,
% 3.01/0.99      ( ~ v4_ordinal1(X0) | v4_ordinal1(X1) | X1 != X0 ),
% 3.01/0.99      theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2303,plain,
% 3.01/0.99      ( ~ v4_ordinal1(X0)
% 3.01/0.99      | v4_ordinal1(k1_ordinal1(X1))
% 3.01/0.99      | k1_ordinal1(X1) != X0 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1102]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_5884,plain,
% 3.01/0.99      ( v4_ordinal1(k1_ordinal1(sK2))
% 3.01/0.99      | ~ v4_ordinal1(sK1)
% 3.01/0.99      | k1_ordinal1(sK2) != sK1 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_2303]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_5885,plain,
% 3.01/0.99      ( k1_ordinal1(sK2) != sK1
% 3.01/0.99      | v4_ordinal1(k1_ordinal1(sK2)) = iProver_top
% 3.01/0.99      | v4_ordinal1(sK1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_5884]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1101,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.01/0.99      theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2687,plain,
% 3.01/0.99      ( r2_hidden(X0,X1)
% 3.01/0.99      | ~ r2_hidden(X2,k1_ordinal1(X3))
% 3.01/0.99      | X0 != X2
% 3.01/0.99      | X1 != k1_ordinal1(X3) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1101]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_6728,plain,
% 3.01/0.99      ( r2_hidden(X0,X1)
% 3.01/0.99      | ~ r2_hidden(X2,k1_ordinal1(sK2))
% 3.01/0.99      | X0 != X2
% 3.01/0.99      | X1 != k1_ordinal1(sK2) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_2687]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7112,plain,
% 3.01/0.99      ( r2_hidden(X0,X1)
% 3.01/0.99      | ~ r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2))
% 3.01/0.99      | X0 != k1_ordinal1(sK2)
% 3.01/0.99      | X1 != k1_ordinal1(sK2) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_6728]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7113,plain,
% 3.01/0.99      ( X0 != k1_ordinal1(sK2)
% 3.01/0.99      | X1 != k1_ordinal1(sK2)
% 3.01/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.01/0.99      | r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_7112]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7115,plain,
% 3.01/0.99      ( sK1 != k1_ordinal1(sK2)
% 3.01/0.99      | r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2)) != iProver_top
% 3.01/0.99      | r2_hidden(sK1,sK1) = iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_7113]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7125,plain,
% 3.01/0.99      ( ~ v3_ordinal1(sK0(sK1)) | v3_ordinal1(k1_ordinal1(sK0(sK1))) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7126,plain,
% 3.01/0.99      ( v3_ordinal1(sK0(sK1)) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(sK0(sK1))) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_7125]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4636,plain,
% 3.01/0.99      ( ~ r1_tarski(X0,sK0(sK1))
% 3.01/0.99      | ~ r1_tarski(sK0(sK1),X0)
% 3.01/0.99      | X0 = sK0(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7345,plain,
% 3.01/0.99      ( ~ r1_tarski(sK0(sK1),sK0(sK1)) | sK0(sK1) = sK0(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_4636]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2,plain,
% 3.01/0.99      ( r1_tarski(X0,X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_9945,plain,
% 3.01/0.99      ( r1_tarski(sK0(sK1),sK0(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1601,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(X0),X1)
% 3.01/0.99      | ~ r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1))
% 3.01/0.99      | X1 = k1_ordinal1(X0) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_9962,plain,
% 3.01/0.99      ( ~ r2_hidden(k1_ordinal1(sK0(sK1)),k1_ordinal1(sK1))
% 3.01/0.99      | r2_hidden(k1_ordinal1(sK0(sK1)),sK1)
% 3.01/0.99      | sK1 = k1_ordinal1(sK0(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1601]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_9963,plain,
% 3.01/0.99      ( sK1 = k1_ordinal1(sK0(sK1))
% 3.01/0.99      | r2_hidden(k1_ordinal1(sK0(sK1)),k1_ordinal1(sK1)) != iProver_top
% 3.01/0.99      | r2_hidden(k1_ordinal1(sK0(sK1)),sK1) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_9962]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1539,plain,
% 3.01/0.99      ( X0 != X1 | k1_ordinal1(X2) != X1 | k1_ordinal1(X2) = X0 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1097]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1593,plain,
% 3.01/0.99      ( X0 != k1_ordinal1(X1)
% 3.01/0.99      | k1_ordinal1(X1) = X0
% 3.01/0.99      | k1_ordinal1(X1) != k1_ordinal1(X1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1539]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_15431,plain,
% 3.01/0.99      ( k1_ordinal1(sK0(sK1)) != k1_ordinal1(sK0(sK1))
% 3.01/0.99      | k1_ordinal1(sK0(sK1)) = sK1
% 3.01/0.99      | sK1 != k1_ordinal1(sK0(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1593]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_10152,plain,
% 3.01/0.99      ( X0 != sK0(sK1) | k1_ordinal1(X0) = k1_ordinal1(sK0(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1098]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_16310,plain,
% 3.01/0.99      ( sK0(sK1) != sK0(sK1)
% 3.01/0.99      | k1_ordinal1(sK0(sK1)) = k1_ordinal1(sK0(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_10152]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17545,plain,
% 3.01/0.99      ( k1_ordinal1(sK0(sK1)) = sK1 ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_17457,c_24,c_25,c_26,c_30,c_43,c_46,c_49,c_51,c_62,
% 3.01/0.99                 c_70,c_71,c_73,c_80,c_86,c_577,c_1103,c_1528,c_1538,
% 3.01/0.99                 c_1559,c_1580,c_1671,c_1895,c_2081,c_3398,c_4080,c_4296,
% 3.01/0.99                 c_4513,c_5885,c_7115,c_7126,c_7345,c_9945,c_9963,
% 3.01/0.99                 c_15431,c_16310]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_18,negated_conjecture,
% 3.01/0.99      ( v4_ordinal1(sK1) | ~ v3_ordinal1(X0) | k1_ordinal1(X0) != sK1 ),
% 3.01/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1463,plain,
% 3.01/0.99      ( k1_ordinal1(X0) != sK1
% 3.01/0.99      | v4_ordinal1(sK1) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17699,plain,
% 3.01/0.99      ( v4_ordinal1(sK1) = iProver_top
% 3.01/0.99      | v3_ordinal1(sK0(sK1)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_17545,c_1463]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17885,plain,
% 3.01/0.99      ( v4_ordinal1(sK1) | ~ v3_ordinal1(sK0(sK1)) ),
% 3.01/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_17699]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1474,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X0)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1464,plain,
% 3.01/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),X1) = iProver_top
% 3.01/0.99      | v4_ordinal1(X1) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1468,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X1)) != iProver_top
% 3.01/0.99      | r1_ordinal1(X0,X1) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2380,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X1)) != iProver_top
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(X0),X1) = iProver_top
% 3.01/0.99      | v4_ordinal1(k1_ordinal1(X1)) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1464,c_1468]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1799,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k1_ordinal1(X1))
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1))
% 3.01/0.99      | ~ v4_ordinal1(k1_ordinal1(X1))
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(X1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1800,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X1)) != iProver_top
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1)) = iProver_top
% 3.01/0.99      | v4_ordinal1(k1_ordinal1(X1)) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1799]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2279,plain,
% 3.01/0.99      ( ~ r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1))
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(X0),X1)
% 3.01/0.99      | ~ v3_ordinal1(X1)
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(X0)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2283,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(X0),k1_ordinal1(X1)) != iProver_top
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(X0),X1) = iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_2279]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4052,plain,
% 3.01/0.99      ( v3_ordinal1(X1) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v4_ordinal1(k1_ordinal1(X1)) != iProver_top
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(X0),X1) = iProver_top
% 3.01/0.99      | r2_hidden(X0,k1_ordinal1(X1)) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_2380,c_78]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4053,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X1)) != iProver_top
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(X0),X1) = iProver_top
% 3.01/0.99      | v4_ordinal1(k1_ordinal1(X1)) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_4052]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4056,plain,
% 3.01/0.99      ( r1_ordinal1(k1_ordinal1(X0),X0) = iProver_top
% 3.01/0.99      | v4_ordinal1(k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1474,c_4053]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1473,plain,
% 3.01/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | r2_hidden(X0,k1_ordinal1(X1)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2379,plain,
% 3.01/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | r1_ordinal1(X0,X1) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1473,c_1468]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2638,plain,
% 3.01/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | r1_ordinal1(X0,k1_ordinal1(X1)) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1473,c_2379]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1475,plain,
% 3.01/0.99      ( r1_ordinal1(X0,X1) != iProver_top
% 3.01/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2962,plain,
% 3.01/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | r1_tarski(X0,k1_ordinal1(X1)) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X1)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_2638,c_1475]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2636,plain,
% 3.01/0.99      ( r1_ordinal1(X0,k1_ordinal1(X0)) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1474,c_2379]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2719,plain,
% 3.01/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | r1_ordinal1(X0,k1_ordinal1(X0)) = iProver_top ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_2636,c_69,c_78,c_1557,c_1669]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2720,plain,
% 3.01/0.99      ( r1_ordinal1(X0,k1_ordinal1(X0)) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_2719]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2725,plain,
% 3.01/0.99      ( r1_tarski(X0,k1_ordinal1(X0)) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_2720,c_1475]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2734,plain,
% 3.01/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | r1_tarski(X0,k1_ordinal1(X0)) = iProver_top ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_2725,c_78]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2735,plain,
% 3.01/0.99      ( r1_tarski(X0,k1_ordinal1(X0)) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_2734]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1479,plain,
% 3.01/0.99      ( X0 = X1
% 3.01/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.01/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2741,plain,
% 3.01/0.99      ( k1_ordinal1(X0) = X0
% 3.01/0.99      | r1_tarski(k1_ordinal1(X0),X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_2735,c_1479]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2822,plain,
% 3.01/0.99      ( r1_tarski(k1_ordinal1(X0),X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_2741,c_9]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2971,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(k1_ordinal1(X0)),X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(k1_ordinal1(X0))) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_2962,c_2822]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1707,plain,
% 3.01/0.99      ( ~ v3_ordinal1(k1_ordinal1(X0))
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(k1_ordinal1(X0))) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1708,plain,
% 3.01/0.99      ( v3_ordinal1(k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(k1_ordinal1(X0))) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1707]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3052,plain,
% 3.01/0.99      ( v3_ordinal1(k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | r2_hidden(k1_ordinal1(k1_ordinal1(X0)),X0) != iProver_top ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_2971,c_1708]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3053,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(k1_ordinal1(X0)),X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_3052]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3060,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(X0),X0) != iProver_top
% 3.01/0.99      | v4_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1464,c_3053]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1751,plain,
% 3.01/0.99      ( ~ r2_hidden(k1_ordinal1(X0),X0)
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1752,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(X0),X0) != iProver_top
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1751]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2034,plain,
% 3.01/0.99      ( ~ r1_ordinal1(k1_ordinal1(X0),X0)
% 3.01/0.99      | r1_tarski(k1_ordinal1(X0),X0)
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(X0)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2035,plain,
% 3.01/0.99      ( r1_ordinal1(k1_ordinal1(X0),X0) != iProver_top
% 3.01/0.99      | r1_tarski(k1_ordinal1(X0),X0) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_2034]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2183,plain,
% 3.01/0.99      ( ~ r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0))
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(X0),X0)
% 3.01/0.99      | ~ v3_ordinal1(X0)
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(X0)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2189,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | r1_ordinal1(k1_ordinal1(X0),X0) = iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_2183]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3642,plain,
% 3.01/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | r2_hidden(k1_ordinal1(X0),X0) != iProver_top ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_3060,c_9,c_78,c_1752,c_2035,c_2189,c_2741]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3643,plain,
% 3.01/0.99      ( r2_hidden(k1_ordinal1(X0),X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_3642]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3650,plain,
% 3.01/0.99      ( r2_hidden(X0,X0) != iProver_top
% 3.01/0.99      | v4_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1464,c_3643]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3660,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | v4_ordinal1(k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1464,c_3650]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4316,plain,
% 3.01/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.01/0.99      | v4_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_4056,c_69,c_78,c_3660]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4317,plain,
% 3.01/0.99      ( v4_ordinal1(k1_ordinal1(X0)) != iProver_top
% 3.01/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_4316]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17674,plain,
% 3.01/0.99      ( v4_ordinal1(sK1) != iProver_top
% 3.01/0.99      | v3_ordinal1(sK0(sK1)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_17545,c_4317]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17867,plain,
% 3.01/0.99      ( ~ v4_ordinal1(sK1) | ~ v3_ordinal1(sK0(sK1)) ),
% 3.01/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_17674]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7114,plain,
% 3.01/0.99      ( ~ r2_hidden(k1_ordinal1(sK2),k1_ordinal1(sK2))
% 3.01/0.99      | r2_hidden(sK1,sK1)
% 3.01/0.99      | sK1 != k1_ordinal1(sK2) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_7112]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1670,plain,
% 3.01/0.99      ( r2_hidden(sK1,k1_ordinal1(k1_ordinal1(sK1)))
% 3.01/0.99      | ~ r2_hidden(sK1,k1_ordinal1(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1668]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1579,plain,
% 3.01/0.99      ( ~ r1_tarski(k1_ordinal1(sK1),sK1)
% 3.01/0.99      | ~ r1_tarski(sK1,k1_ordinal1(sK1))
% 3.01/0.99      | sK1 = k1_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1577]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1558,plain,
% 3.01/0.99      ( ~ r2_hidden(sK1,k1_ordinal1(k1_ordinal1(sK1)))
% 3.01/0.99      | r1_ordinal1(sK1,k1_ordinal1(sK1))
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(sK1))
% 3.01/0.99      | ~ v3_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1551]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1527,plain,
% 3.01/0.99      ( ~ r1_ordinal1(sK1,k1_ordinal1(sK1))
% 3.01/0.99      | r1_tarski(sK1,k1_ordinal1(sK1))
% 3.01/0.99      | ~ v3_ordinal1(k1_ordinal1(sK1))
% 3.01/0.99      | ~ v3_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1525]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_576,plain,
% 3.01/0.99      ( ~ r2_hidden(sK1,sK1)
% 3.01/0.99      | r1_tarski(k1_ordinal1(sK1),sK1)
% 3.01/0.99      | ~ v3_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_574]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_338,plain,
% 3.01/0.99      ( ~ v3_ordinal1(X0)
% 3.01/0.99      | v3_ordinal1(sK0(X0))
% 3.01/0.99      | k1_ordinal1(sK2) = sK1
% 3.01/0.99      | sK1 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_339,plain,
% 3.01/0.99      ( v3_ordinal1(sK0(sK1))
% 3.01/0.99      | ~ v3_ordinal1(sK1)
% 3.01/0.99      | k1_ordinal1(sK2) = sK1 ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_338]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_341,plain,
% 3.01/0.99      ( v3_ordinal1(sK0(sK1)) | k1_ordinal1(sK2) = sK1 ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_339,c_24]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_324,plain,
% 3.01/0.99      ( ~ v3_ordinal1(X0)
% 3.01/0.99      | v3_ordinal1(sK0(X0))
% 3.01/0.99      | v3_ordinal1(sK2)
% 3.01/0.99      | sK1 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_325,plain,
% 3.01/0.99      ( v3_ordinal1(sK0(sK1)) | v3_ordinal1(sK2) | ~ v3_ordinal1(sK1) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_324]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_327,plain,
% 3.01/0.99      ( v3_ordinal1(sK2) | v3_ordinal1(sK0(sK1)) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_325,c_24]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_328,plain,
% 3.01/0.99      ( v3_ordinal1(sK0(sK1)) | v3_ordinal1(sK2) ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_327]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_79,plain,
% 3.01/0.99      ( v3_ordinal1(k1_ordinal1(sK1)) | ~ v3_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_42,plain,
% 3.01/0.99      ( v4_ordinal1(sK1) | v3_ordinal1(sK0(sK1)) | ~ v3_ordinal1(sK1) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(contradiction,plain,
% 3.01/0.99      ( $false ),
% 3.01/0.99      inference(minisat,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_17885,c_17867,c_7114,c_5884,c_4295,c_4079,c_2081,
% 3.01/0.99                 c_1894,c_1670,c_1579,c_1558,c_1538,c_1527,c_1103,c_576,
% 3.01/0.99                 c_341,c_328,c_86,c_79,c_73,c_70,c_62,c_51,c_42,c_24]) ).
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  ------                               Statistics
% 3.01/0.99  
% 3.01/0.99  ------ General
% 3.01/0.99  
% 3.01/0.99  abstr_ref_over_cycles:                  0
% 3.01/0.99  abstr_ref_under_cycles:                 0
% 3.01/0.99  gc_basic_clause_elim:                   0
% 3.01/0.99  forced_gc_time:                         0
% 3.01/0.99  parsing_time:                           0.009
% 3.01/0.99  unif_index_cands_time:                  0.
% 3.01/0.99  unif_index_add_time:                    0.
% 3.01/0.99  orderings_time:                         0.
% 3.01/0.99  out_proof_time:                         0.012
% 3.01/0.99  total_time:                             0.442
% 3.01/0.99  num_of_symbols:                         37
% 3.01/0.99  num_of_terms:                           5965
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing
% 3.01/0.99  
% 3.01/0.99  num_of_splits:                          0
% 3.01/0.99  num_of_split_atoms:                     0
% 3.01/0.99  num_of_reused_defs:                     0
% 3.01/0.99  num_eq_ax_congr_red:                    12
% 3.01/0.99  num_of_sem_filtered_clauses:            1
% 3.01/0.99  num_of_subtypes:                        0
% 3.01/0.99  monotx_restored_types:                  0
% 3.01/0.99  sat_num_of_epr_types:                   0
% 3.01/0.99  sat_num_of_non_cyclic_types:            0
% 3.01/0.99  sat_guarded_non_collapsed_types:        0
% 3.01/0.99  num_pure_diseq_elim:                    0
% 3.01/0.99  simp_replaced_by:                       0
% 3.01/0.99  res_preprocessed:                       107
% 3.01/0.99  prep_upred:                             0
% 3.01/0.99  prep_unflattend:                        36
% 3.01/0.99  smt_new_axioms:                         0
% 3.01/0.99  pred_elim_cands:                        5
% 3.01/0.99  pred_elim:                              0
% 3.01/0.99  pred_elim_cl:                           0
% 3.01/0.99  pred_elim_cycles:                       4
% 3.01/0.99  merged_defs:                            0
% 3.01/0.99  merged_defs_ncl:                        0
% 3.01/0.99  bin_hyper_res:                          0
% 3.01/0.99  prep_cycles:                            4
% 3.01/0.99  pred_elim_time:                         0.009
% 3.01/0.99  splitting_time:                         0.
% 3.01/0.99  sem_filter_time:                        0.
% 3.01/0.99  monotx_time:                            0.
% 3.01/0.99  subtype_inf_time:                       0.
% 3.01/0.99  
% 3.01/0.99  ------ Problem properties
% 3.01/0.99  
% 3.01/0.99  clauses:                                23
% 3.01/0.99  conjectures:                            6
% 3.01/0.99  epr:                                    6
% 3.01/0.99  horn:                                   20
% 3.01/0.99  ground:                                 3
% 3.01/0.99  unary:                                  4
% 3.01/0.99  binary:                                 4
% 3.01/0.99  lits:                                   65
% 3.01/0.99  lits_eq:                                8
% 3.01/0.99  fd_pure:                                0
% 3.01/0.99  fd_pseudo:                              0
% 3.01/0.99  fd_cond:                                0
% 3.01/0.99  fd_pseudo_cond:                         2
% 3.01/0.99  ac_symbols:                             0
% 3.01/0.99  
% 3.01/0.99  ------ Propositional Solver
% 3.01/0.99  
% 3.01/0.99  prop_solver_calls:                      32
% 3.01/0.99  prop_fast_solver_calls:                 1656
% 3.01/0.99  smt_solver_calls:                       0
% 3.01/0.99  smt_fast_solver_calls:                  0
% 3.01/0.99  prop_num_of_clauses:                    4703
% 3.01/0.99  prop_preprocess_simplified:             9236
% 3.01/0.99  prop_fo_subsumed:                       112
% 3.01/0.99  prop_solver_time:                       0.
% 3.01/0.99  smt_solver_time:                        0.
% 3.01/0.99  smt_fast_solver_time:                   0.
% 3.01/0.99  prop_fast_solver_time:                  0.
% 3.01/0.99  prop_unsat_core_time:                   0.
% 3.01/0.99  
% 3.01/0.99  ------ QBF
% 3.01/0.99  
% 3.01/0.99  qbf_q_res:                              0
% 3.01/0.99  qbf_num_tautologies:                    0
% 3.01/0.99  qbf_prep_cycles:                        0
% 3.01/0.99  
% 3.01/0.99  ------ BMC1
% 3.01/0.99  
% 3.01/0.99  bmc1_current_bound:                     -1
% 3.01/0.99  bmc1_last_solved_bound:                 -1
% 3.01/0.99  bmc1_unsat_core_size:                   -1
% 3.01/0.99  bmc1_unsat_core_parents_size:           -1
% 3.01/0.99  bmc1_merge_next_fun:                    0
% 3.01/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation
% 3.01/0.99  
% 3.01/0.99  inst_num_of_clauses:                    1187
% 3.01/0.99  inst_num_in_passive:                    176
% 3.01/0.99  inst_num_in_active:                     805
% 3.01/0.99  inst_num_in_unprocessed:                206
% 3.01/0.99  inst_num_of_loops:                      990
% 3.01/0.99  inst_num_of_learning_restarts:          0
% 3.01/0.99  inst_num_moves_active_passive:          177
% 3.01/0.99  inst_lit_activity:                      0
% 3.01/0.99  inst_lit_activity_moves:                0
% 3.01/0.99  inst_num_tautologies:                   0
% 3.01/0.99  inst_num_prop_implied:                  0
% 3.01/0.99  inst_num_existing_simplified:           0
% 3.01/0.99  inst_num_eq_res_simplified:             0
% 3.01/0.99  inst_num_child_elim:                    0
% 3.01/0.99  inst_num_of_dismatching_blockings:      3139
% 3.01/0.99  inst_num_of_non_proper_insts:           3526
% 3.01/0.99  inst_num_of_duplicates:                 0
% 3.01/0.99  inst_inst_num_from_inst_to_res:         0
% 3.01/0.99  inst_dismatching_checking_time:         0.
% 3.01/0.99  
% 3.01/0.99  ------ Resolution
% 3.01/0.99  
% 3.01/0.99  res_num_of_clauses:                     0
% 3.01/0.99  res_num_in_passive:                     0
% 3.01/0.99  res_num_in_active:                      0
% 3.01/0.99  res_num_of_loops:                       111
% 3.01/0.99  res_forward_subset_subsumed:            428
% 3.01/0.99  res_backward_subset_subsumed:           10
% 3.01/0.99  res_forward_subsumed:                   0
% 3.01/0.99  res_backward_subsumed:                  0
% 3.01/0.99  res_forward_subsumption_resolution:     0
% 3.01/0.99  res_backward_subsumption_resolution:    0
% 3.01/0.99  res_clause_to_clause_subsumption:       14574
% 3.01/0.99  res_orphan_elimination:                 0
% 3.01/0.99  res_tautology_del:                      423
% 3.01/0.99  res_num_eq_res_simplified:              0
% 3.01/0.99  res_num_sel_changes:                    0
% 3.01/0.99  res_moves_from_active_to_pass:          0
% 3.01/0.99  
% 3.01/0.99  ------ Superposition
% 3.01/0.99  
% 3.01/0.99  sup_time_total:                         0.
% 3.01/0.99  sup_time_generating:                    0.
% 3.01/0.99  sup_time_sim_full:                      0.
% 3.01/0.99  sup_time_sim_immed:                     0.
% 3.01/0.99  
% 3.01/0.99  sup_num_of_clauses:                     428
% 3.01/0.99  sup_num_in_active:                      187
% 3.01/0.99  sup_num_in_passive:                     241
% 3.01/0.99  sup_num_of_loops:                       196
% 3.01/0.99  sup_fw_superposition:                   471
% 3.01/0.99  sup_bw_superposition:                   462
% 3.01/0.99  sup_immediate_simplified:               378
% 3.01/0.99  sup_given_eliminated:                   0
% 3.01/0.99  comparisons_done:                       0
% 3.01/0.99  comparisons_avoided:                    0
% 3.01/0.99  
% 3.01/0.99  ------ Simplifications
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  sim_fw_subset_subsumed:                 63
% 3.01/0.99  sim_bw_subset_subsumed:                 19
% 3.01/0.99  sim_fw_subsumed:                        187
% 3.01/0.99  sim_bw_subsumed:                        13
% 3.01/0.99  sim_fw_subsumption_res:                 0
% 3.01/0.99  sim_bw_subsumption_res:                 0
% 3.01/0.99  sim_tautology_del:                      6
% 3.01/0.99  sim_eq_tautology_del:                   10
% 3.01/0.99  sim_eq_res_simp:                        0
% 3.01/0.99  sim_fw_demodulated:                     133
% 3.01/0.99  sim_bw_demodulated:                     0
% 3.01/0.99  sim_light_normalised:                   0
% 3.01/0.99  sim_joinable_taut:                      0
% 3.01/0.99  sim_joinable_simp:                      0
% 3.01/0.99  sim_ac_normalised:                      0
% 3.01/0.99  sim_smt_subsumption:                    0
% 3.01/0.99  
%------------------------------------------------------------------------------
