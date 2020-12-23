%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0003+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:13 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 480 expanded)
%              Number of clauses        :   50 ( 172 expanded)
%              Number of leaves         :   10 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  295 (2136 expanded)
%              Number of equality atoms :   85 ( 348 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X2] :
                ~ ( r2_hidden(X2,X1)
                  & r2_hidden(X2,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] :
            ( r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( r2_hidden(sK4,X1)
        & r2_hidden(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
        | ( ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) )
   => ( ( r1_xboole_0(sK2,sK3)
        & ? [X2] :
            ( r2_hidden(X2,sK3)
            & r2_hidden(X2,sK2) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,sK3)
            | ~ r2_hidden(X3,sK2) )
        & ~ r1_xboole_0(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( r1_xboole_0(sK2,sK3)
      & r2_hidden(sK4,sK3)
      & r2_hidden(sK4,sK2) )
    | ( ! [X3] :
          ( ~ r2_hidden(X3,sK3)
          | ~ r2_hidden(X3,sK2) )
      & ~ r1_xboole_0(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f22,f21])).

fof(f39,plain,(
    ! [X3] :
      ( r2_hidden(sK4,sK3)
      | ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,
    ( r2_hidden(sK4,sK3)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X3] :
      ( r1_xboole_0(sK2,sK3)
      | ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f37,plain,(
    ! [X3] :
      ( r2_hidden(sK4,sK2)
      | ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,
    ( r2_hidden(sK4,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_737,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_727,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1063,plain,
    ( r2_hidden(sK0(sK3),sK2) != iProver_top
    | r2_hidden(sK4,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_727])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_139,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK3)
    | r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_287,plain,
    ( r2_hidden(sK4,sK3)
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_139,c_15])).

cnf(c_288,plain,
    ( r2_hidden(sK4,sK3)
    | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_289,plain,
    ( k3_xboole_0(sK2,sK3) != k1_xboole_0
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_852,plain,
    ( r2_hidden(sK1(sK2,sK3,k1_xboole_0),sK3)
    | r2_hidden(sK1(sK2,sK3,k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_855,plain,
    ( r2_hidden(sK1(sK2,sK3,k1_xboole_0),sK2)
    | r2_hidden(sK1(sK2,sK3,k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_141,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,sK3)
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_297,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2)
    | k3_xboole_0(X1,X2) = k1_xboole_0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_141,c_12])).

cnf(c_298,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_882,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,k1_xboole_0),sK3)
    | ~ r2_hidden(sK1(sK2,sK3,k1_xboole_0),sK2)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_953,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_729,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_728,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1003,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_729,c_728])).

cnf(c_1005,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1003,c_729])).

cnf(c_1006,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1005])).

cnf(c_1283,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1063,c_289,c_852,c_855,c_882,c_953,c_1006])).

cnf(c_723,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_1289,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_723])).

cnf(c_1446,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1289,c_852,c_855,c_882,c_953,c_1006])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_732,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1453,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_732])).

cnf(c_2018,plain,
    ( r2_hidden(sK4,sK2) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_1453])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2)
    | r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_726,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1064,plain,
    ( r2_hidden(sK0(sK3),sK2) != iProver_top
    | r2_hidden(sK4,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_726])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK3)
    | r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_277,plain,
    ( r2_hidden(sK4,sK2)
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_139,c_17])).

cnf(c_278,plain,
    ( r2_hidden(sK4,sK2)
    | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_279,plain,
    ( k3_xboole_0(sK2,sK3) != k1_xboole_0
    | r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_1330,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1064,c_279,c_852,c_855,c_882,c_953,c_1006])).

cnf(c_2068,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2018,c_279,c_852,c_855,c_882,c_953,c_1006])).

cnf(c_736,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2073,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2068,c_736])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2073,c_1005])).


%------------------------------------------------------------------------------
