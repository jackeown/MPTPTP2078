%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0580+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:39 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 400 expanded)
%              Number of clauses        :   48 ( 112 expanded)
%              Number of leaves         :    8 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :  273 (1803 expanded)
%              Number of equality atoms :  108 ( 536 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & r2_hidden(X1,k2_relat_1(X0)) )
     => ( k1_xboole_0 != sK3
        & r2_hidden(sK3,k2_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( k1_xboole_0 != X1
              & r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) )
        & ( ! [X2] :
              ( k1_xboole_0 = X2
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
          | v3_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(sK2)) )
        | ~ v3_relat_1(sK2) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(sK2)) )
        | v3_relat_1(sK2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ( k1_xboole_0 != sK3
        & r2_hidden(sK3,k2_relat_1(sK2)) )
      | ~ v3_relat_1(sK2) )
    & ( ! [X2] :
          ( k1_xboole_0 = X2
          | ~ r2_hidden(X2,k2_relat_1(sK2)) )
      | v3_relat_1(sK2) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f22,f21])).

fof(f34,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK2))
      | v3_relat_1(sK2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
        & ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( v3_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,
    ( k1_xboole_0 != sK3
    | ~ v3_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ v3_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f27])).

fof(f38,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f37])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_907,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(X0,k2_relat_1(sK2))
    | v3_relat_1(sK2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_903,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k2_relat_1(sK2)) != iProver_top
    | v3_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1139,plain,
    ( sK1(k2_relat_1(sK2),X0) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK2),X0) = iProver_top
    | v3_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_907,c_903])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(X0)
    | ~ v3_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_38,plain,
    ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v3_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_40,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v3_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_0,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(X0)
    | v3_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_159,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
    | v3_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_160,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0))
    | v3_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_159])).

cnf(c_9,negated_conjecture,
    ( ~ v3_relat_1(sK2)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_185,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0))
    | sK3 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_160,c_9])).

cnf(c_186,plain,
    ( sK3 != k1_xboole_0
    | r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_39,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(sK2)
    | ~ v3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_369,plain,
    ( ~ v3_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0)) ),
    inference(prop_impl,[status(thm)],[c_12,c_39])).

cnf(c_370,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0))
    | ~ v3_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_902,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0)) = iProver_top
    | v3_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ v3_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_904,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2)) = iProver_top
    | v3_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_906,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1430,plain,
    ( r2_hidden(sK3,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | v3_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_904,c_906])).

cnf(c_1467,plain,
    ( r2_hidden(sK3,k1_tarski(k1_xboole_0)) = iProver_top
    | v3_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_1430])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1052,plain,
    ( ~ r2_hidden(sK3,k1_tarski(X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1469,plain,
    ( ~ r2_hidden(sK3,k1_tarski(k1_xboole_0))
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_1470,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK3,k1_tarski(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1469])).

cnf(c_1535,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) = iProver_top
    | sK1(k2_relat_1(sK2),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1139,c_13,c_40,c_186,c_1467,c_1470])).

cnf(c_1536,plain,
    ( sK1(k2_relat_1(sK2),X0) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK2),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1535])).

cnf(c_42,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(sK2)
    | v3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_367,plain,
    ( v3_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0)) ),
    inference(prop_impl,[status(thm)],[c_12,c_42])).

cnf(c_368,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0))
    | v3_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_367])).

cnf(c_901,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0)) != iProver_top
    | v3_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_1543,plain,
    ( sK1(k2_relat_1(sK2),k1_tarski(k1_xboole_0)) = k1_xboole_0
    | v3_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_901])).

cnf(c_1699,plain,
    ( v3_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1467,c_13,c_40,c_186,c_1470])).

cnf(c_1705,plain,
    ( sK1(k2_relat_1(sK2),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1543,c_13,c_40,c_186,c_1467,c_1470])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_908,plain,
    ( r2_hidden(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1708,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_908])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1472,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1473,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1472])).

cnf(c_41,plain,
    ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v3_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_43,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_tarski(k1_xboole_0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v3_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1708,c_1699,c_1473,c_43,c_13])).


%------------------------------------------------------------------------------
