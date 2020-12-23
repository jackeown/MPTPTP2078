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
% DateTime   : Thu Dec  3 11:22:45 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 305 expanded)
%              Number of clauses        :   57 (  99 expanded)
%              Number of leaves         :   10 (  66 expanded)
%              Depth                    :   19
%              Number of atoms          :  328 (1672 expanded)
%              Number of equality atoms :  139 ( 419 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f9])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f33,f20])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f23])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,conjecture,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,
    ( ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))
   => k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f7,f18])).

fof(f34,plain,(
    k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    o_0_0_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(definition_unfolding,[],[f34,f20])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1000,plain,
    ( ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),X1)
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),k4_xboole_0(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3240,plain,
    ( ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),X1)
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_3241,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),X1) != iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3240])).

cnf(c_3243,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)) != iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3241])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_340,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_339,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_341,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1193,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)
    | r2_hidden(sK0(X2,X3,k2_xboole_0(X0,X1)),X1) != iProver_top
    | r2_hidden(sK0(X2,X3,k2_xboole_0(X0,X1)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_339,c_341])).

cnf(c_1367,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X2,o_0_0_xboole_0)
    | r2_hidden(sK0(X0,X1,X2),o_0_0_xboole_0) != iProver_top
    | r2_hidden(sK0(X0,X1,k2_xboole_0(X2,o_0_0_xboole_0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1193])).

cnf(c_1371,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1367,c_12])).

cnf(c_576,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_339])).

cnf(c_1699,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),o_0_0_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1371,c_576])).

cnf(c_2518,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X1
    | r2_hidden(sK0(X0,o_0_0_xboole_0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,o_0_0_xboole_0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_340,c_1699])).

cnf(c_2552,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,o_0_0_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,o_0_0_xboole_0,X0),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2518,c_12])).

cnf(c_2749,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | r2_hidden(sK0(X0,o_0_0_xboole_0,o_0_0_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2552,c_1699])).

cnf(c_2755,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK0(X0,o_0_0_xboole_0,o_0_0_xboole_0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2749,c_12])).

cnf(c_332,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3101,plain,
    ( k4_xboole_0(X0,X1) = o_0_0_xboole_0
    | r2_hidden(sK0(k4_xboole_0(X0,X1),o_0_0_xboole_0,o_0_0_xboole_0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2755,c_332])).

cnf(c_3121,plain,
    ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | r2_hidden(sK0(k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3101])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_331,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2732,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(k4_xboole_0(X0,X1),o_0_0_xboole_0,X2),X2) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(X0,X1),o_0_0_xboole_0,X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2552,c_331])).

cnf(c_2835,plain,
    ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | r2_hidden(sK0(k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2732])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_476,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),k2_xboole_0(sK2,X1))
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_621,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),k2_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),sK2) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_1838,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k2_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),sK2) ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_1839,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k2_xboole_0(sK2,sK3)) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1838])).

cnf(c_1841,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k2_xboole_0(sK2,sK3)) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_453,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),X0)
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),sK2)
    | k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1254,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),sK2)
    | k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_1255,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,X1)
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_1257,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_133,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_561,plain,
    ( k4_xboole_0(X0,X1) != X2
    | o_0_0_xboole_0 != X2
    | o_0_0_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_562,plain,
    ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_530,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),X0)
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_535,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),X0) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_537,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)) != iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_454,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),X0)
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),k2_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_529,plain,
    ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k2_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_531,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,X1)
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k2_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_533,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top
    | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k2_xboole_0(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_440,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_469,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) != k4_xboole_0(X0,X1)
    | o_0_0_xboole_0 != k4_xboole_0(X0,X1)
    | o_0_0_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_471,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) != k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK2,sK3))
    | o_0_0_xboole_0 != k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_132,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_141,plain,
    ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_13,negated_conjecture,
    ( o_0_0_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3243,c_3121,c_2835,c_1841,c_1257,c_562,c_537,c_533,c_471,c_141,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:50:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.33/0.91  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/0.91  
% 2.33/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.91  
% 2.33/0.91  ------  iProver source info
% 2.33/0.91  
% 2.33/0.91  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.91  git: non_committed_changes: false
% 2.33/0.91  git: last_make_outside_of_git: false
% 2.33/0.91  
% 2.33/0.91  ------ 
% 2.33/0.91  
% 2.33/0.91  ------ Input Options
% 2.33/0.91  
% 2.33/0.91  --out_options                           all
% 2.33/0.91  --tptp_safe_out                         true
% 2.33/0.91  --problem_path                          ""
% 2.33/0.91  --include_path                          ""
% 2.33/0.91  --clausifier                            res/vclausify_rel
% 2.33/0.91  --clausifier_options                    --mode clausify
% 2.33/0.91  --stdin                                 false
% 2.33/0.91  --stats_out                             all
% 2.33/0.91  
% 2.33/0.91  ------ General Options
% 2.33/0.91  
% 2.33/0.91  --fof                                   false
% 2.33/0.91  --time_out_real                         305.
% 2.33/0.91  --time_out_virtual                      -1.
% 2.33/0.91  --symbol_type_check                     false
% 2.33/0.91  --clausify_out                          false
% 2.33/0.91  --sig_cnt_out                           false
% 2.33/0.91  --trig_cnt_out                          false
% 2.33/0.91  --trig_cnt_out_tolerance                1.
% 2.33/0.91  --trig_cnt_out_sk_spl                   false
% 2.33/0.91  --abstr_cl_out                          false
% 2.33/0.91  
% 2.33/0.91  ------ Global Options
% 2.33/0.91  
% 2.33/0.91  --schedule                              default
% 2.33/0.91  --add_important_lit                     false
% 2.33/0.91  --prop_solver_per_cl                    1000
% 2.33/0.91  --min_unsat_core                        false
% 2.33/0.91  --soft_assumptions                      false
% 2.33/0.91  --soft_lemma_size                       3
% 2.33/0.91  --prop_impl_unit_size                   0
% 2.33/0.91  --prop_impl_unit                        []
% 2.33/0.91  --share_sel_clauses                     true
% 2.33/0.91  --reset_solvers                         false
% 2.33/0.91  --bc_imp_inh                            [conj_cone]
% 2.33/0.91  --conj_cone_tolerance                   3.
% 2.33/0.91  --extra_neg_conj                        none
% 2.33/0.91  --large_theory_mode                     true
% 2.33/0.91  --prolific_symb_bound                   200
% 2.33/0.91  --lt_threshold                          2000
% 2.33/0.91  --clause_weak_htbl                      true
% 2.33/0.91  --gc_record_bc_elim                     false
% 2.33/0.91  
% 2.33/0.91  ------ Preprocessing Options
% 2.33/0.91  
% 2.33/0.91  --preprocessing_flag                    true
% 2.33/0.91  --time_out_prep_mult                    0.1
% 2.33/0.91  --splitting_mode                        input
% 2.33/0.91  --splitting_grd                         true
% 2.33/0.91  --splitting_cvd                         false
% 2.33/0.91  --splitting_cvd_svl                     false
% 2.33/0.91  --splitting_nvd                         32
% 2.33/0.91  --sub_typing                            true
% 2.33/0.91  --prep_gs_sim                           true
% 2.33/0.91  --prep_unflatten                        true
% 2.33/0.91  --prep_res_sim                          true
% 2.33/0.91  --prep_upred                            true
% 2.33/0.91  --prep_sem_filter                       exhaustive
% 2.33/0.91  --prep_sem_filter_out                   false
% 2.33/0.91  --pred_elim                             true
% 2.33/0.91  --res_sim_input                         true
% 2.33/0.91  --eq_ax_congr_red                       true
% 2.33/0.91  --pure_diseq_elim                       true
% 2.33/0.91  --brand_transform                       false
% 2.33/0.91  --non_eq_to_eq                          false
% 2.33/0.91  --prep_def_merge                        true
% 2.33/0.91  --prep_def_merge_prop_impl              false
% 2.33/0.91  --prep_def_merge_mbd                    true
% 2.33/0.91  --prep_def_merge_tr_red                 false
% 2.33/0.91  --prep_def_merge_tr_cl                  false
% 2.33/0.91  --smt_preprocessing                     true
% 2.33/0.91  --smt_ac_axioms                         fast
% 2.33/0.91  --preprocessed_out                      false
% 2.33/0.91  --preprocessed_stats                    false
% 2.33/0.91  
% 2.33/0.91  ------ Abstraction refinement Options
% 2.33/0.91  
% 2.33/0.91  --abstr_ref                             []
% 2.33/0.91  --abstr_ref_prep                        false
% 2.33/0.91  --abstr_ref_until_sat                   false
% 2.33/0.91  --abstr_ref_sig_restrict                funpre
% 2.33/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.91  --abstr_ref_under                       []
% 2.33/0.91  
% 2.33/0.91  ------ SAT Options
% 2.33/0.91  
% 2.33/0.91  --sat_mode                              false
% 2.33/0.91  --sat_fm_restart_options                ""
% 2.33/0.91  --sat_gr_def                            false
% 2.33/0.91  --sat_epr_types                         true
% 2.33/0.91  --sat_non_cyclic_types                  false
% 2.33/0.91  --sat_finite_models                     false
% 2.33/0.91  --sat_fm_lemmas                         false
% 2.33/0.91  --sat_fm_prep                           false
% 2.33/0.91  --sat_fm_uc_incr                        true
% 2.33/0.91  --sat_out_model                         small
% 2.33/0.91  --sat_out_clauses                       false
% 2.33/0.91  
% 2.33/0.91  ------ QBF Options
% 2.33/0.91  
% 2.33/0.91  --qbf_mode                              false
% 2.33/0.91  --qbf_elim_univ                         false
% 2.33/0.91  --qbf_dom_inst                          none
% 2.33/0.91  --qbf_dom_pre_inst                      false
% 2.33/0.91  --qbf_sk_in                             false
% 2.33/0.91  --qbf_pred_elim                         true
% 2.33/0.91  --qbf_split                             512
% 2.33/0.91  
% 2.33/0.91  ------ BMC1 Options
% 2.33/0.91  
% 2.33/0.91  --bmc1_incremental                      false
% 2.33/0.91  --bmc1_axioms                           reachable_all
% 2.33/0.91  --bmc1_min_bound                        0
% 2.33/0.91  --bmc1_max_bound                        -1
% 2.33/0.91  --bmc1_max_bound_default                -1
% 2.33/0.91  --bmc1_symbol_reachability              true
% 2.33/0.91  --bmc1_property_lemmas                  false
% 2.33/0.91  --bmc1_k_induction                      false
% 2.33/0.91  --bmc1_non_equiv_states                 false
% 2.33/0.91  --bmc1_deadlock                         false
% 2.33/0.91  --bmc1_ucm                              false
% 2.33/0.91  --bmc1_add_unsat_core                   none
% 2.33/0.92  --bmc1_unsat_core_children              false
% 2.33/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.92  --bmc1_out_stat                         full
% 2.33/0.92  --bmc1_ground_init                      false
% 2.33/0.92  --bmc1_pre_inst_next_state              false
% 2.33/0.92  --bmc1_pre_inst_state                   false
% 2.33/0.92  --bmc1_pre_inst_reach_state             false
% 2.33/0.92  --bmc1_out_unsat_core                   false
% 2.33/0.92  --bmc1_aig_witness_out                  false
% 2.33/0.92  --bmc1_verbose                          false
% 2.33/0.92  --bmc1_dump_clauses_tptp                false
% 2.33/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.92  --bmc1_dump_file                        -
% 2.33/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.92  --bmc1_ucm_extend_mode                  1
% 2.33/0.92  --bmc1_ucm_init_mode                    2
% 2.33/0.92  --bmc1_ucm_cone_mode                    none
% 2.33/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.92  --bmc1_ucm_relax_model                  4
% 2.33/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.92  --bmc1_ucm_layered_model                none
% 2.33/0.92  --bmc1_ucm_max_lemma_size               10
% 2.33/0.92  
% 2.33/0.92  ------ AIG Options
% 2.33/0.92  
% 2.33/0.92  --aig_mode                              false
% 2.33/0.92  
% 2.33/0.92  ------ Instantiation Options
% 2.33/0.92  
% 2.33/0.92  --instantiation_flag                    true
% 2.33/0.92  --inst_sos_flag                         false
% 2.33/0.92  --inst_sos_phase                        true
% 2.33/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.92  --inst_lit_sel_side                     num_symb
% 2.33/0.92  --inst_solver_per_active                1400
% 2.33/0.92  --inst_solver_calls_frac                1.
% 2.33/0.92  --inst_passive_queue_type               priority_queues
% 2.33/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.92  --inst_passive_queues_freq              [25;2]
% 2.33/0.92  --inst_dismatching                      true
% 2.33/0.92  --inst_eager_unprocessed_to_passive     true
% 2.33/0.92  --inst_prop_sim_given                   true
% 2.33/0.92  --inst_prop_sim_new                     false
% 2.33/0.92  --inst_subs_new                         false
% 2.33/0.92  --inst_eq_res_simp                      false
% 2.33/0.92  --inst_subs_given                       false
% 2.33/0.92  --inst_orphan_elimination               true
% 2.33/0.92  --inst_learning_loop_flag               true
% 2.33/0.92  --inst_learning_start                   3000
% 2.33/0.92  --inst_learning_factor                  2
% 2.33/0.92  --inst_start_prop_sim_after_learn       3
% 2.33/0.92  --inst_sel_renew                        solver
% 2.33/0.92  --inst_lit_activity_flag                true
% 2.33/0.92  --inst_restr_to_given                   false
% 2.33/0.92  --inst_activity_threshold               500
% 2.33/0.92  --inst_out_proof                        true
% 2.33/0.92  
% 2.33/0.92  ------ Resolution Options
% 2.33/0.92  
% 2.33/0.92  --resolution_flag                       true
% 2.33/0.92  --res_lit_sel                           adaptive
% 2.33/0.92  --res_lit_sel_side                      none
% 2.33/0.92  --res_ordering                          kbo
% 2.33/0.92  --res_to_prop_solver                    active
% 2.33/0.92  --res_prop_simpl_new                    false
% 2.33/0.92  --res_prop_simpl_given                  true
% 2.33/0.92  --res_passive_queue_type                priority_queues
% 2.33/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.92  --res_passive_queues_freq               [15;5]
% 2.33/0.92  --res_forward_subs                      full
% 2.33/0.92  --res_backward_subs                     full
% 2.33/0.92  --res_forward_subs_resolution           true
% 2.33/0.92  --res_backward_subs_resolution          true
% 2.33/0.92  --res_orphan_elimination                true
% 2.33/0.92  --res_time_limit                        2.
% 2.33/0.92  --res_out_proof                         true
% 2.33/0.92  
% 2.33/0.92  ------ Superposition Options
% 2.33/0.92  
% 2.33/0.92  --superposition_flag                    true
% 2.33/0.92  --sup_passive_queue_type                priority_queues
% 2.33/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.92  --demod_completeness_check              fast
% 2.33/0.92  --demod_use_ground                      true
% 2.33/0.92  --sup_to_prop_solver                    passive
% 2.33/0.92  --sup_prop_simpl_new                    true
% 2.33/0.92  --sup_prop_simpl_given                  true
% 2.33/0.92  --sup_fun_splitting                     false
% 2.33/0.92  --sup_smt_interval                      50000
% 2.33/0.92  
% 2.33/0.92  ------ Superposition Simplification Setup
% 2.33/0.92  
% 2.33/0.92  --sup_indices_passive                   []
% 2.33/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.92  --sup_full_bw                           [BwDemod]
% 2.33/0.92  --sup_immed_triv                        [TrivRules]
% 2.33/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.92  --sup_immed_bw_main                     []
% 2.33/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.92  
% 2.33/0.92  ------ Combination Options
% 2.33/0.92  
% 2.33/0.92  --comb_res_mult                         3
% 2.33/0.92  --comb_sup_mult                         2
% 2.33/0.92  --comb_inst_mult                        10
% 2.33/0.92  
% 2.33/0.92  ------ Debug Options
% 2.33/0.92  
% 2.33/0.92  --dbg_backtrace                         false
% 2.33/0.92  --dbg_dump_prop_clauses                 false
% 2.33/0.92  --dbg_dump_prop_clauses_file            -
% 2.33/0.92  --dbg_out_stat                          false
% 2.33/0.92  ------ Parsing...
% 2.33/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.92  
% 2.33/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.33/0.92  
% 2.33/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.92  
% 2.33/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.92  ------ Proving...
% 2.33/0.92  ------ Problem Properties 
% 2.33/0.92  
% 2.33/0.92  
% 2.33/0.92  clauses                                 14
% 2.33/0.92  conjectures                             1
% 2.33/0.92  EPR                                     0
% 2.33/0.92  Horn                                    8
% 2.33/0.92  unary                                   2
% 2.33/0.92  binary                                  4
% 2.33/0.92  lits                                    36
% 2.33/0.92  lits eq                                 8
% 2.33/0.92  fd_pure                                 0
% 2.33/0.92  fd_pseudo                               0
% 2.33/0.92  fd_cond                                 0
% 2.33/0.92  fd_pseudo_cond                          6
% 2.33/0.92  AC symbols                              0
% 2.33/0.92  
% 2.33/0.92  ------ Schedule dynamic 5 is on 
% 2.33/0.92  
% 2.33/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.92  
% 2.33/0.92  
% 2.33/0.92  ------ 
% 2.33/0.92  Current options:
% 2.33/0.92  ------ 
% 2.33/0.92  
% 2.33/0.92  ------ Input Options
% 2.33/0.92  
% 2.33/0.92  --out_options                           all
% 2.33/0.92  --tptp_safe_out                         true
% 2.33/0.92  --problem_path                          ""
% 2.33/0.92  --include_path                          ""
% 2.33/0.92  --clausifier                            res/vclausify_rel
% 2.33/0.92  --clausifier_options                    --mode clausify
% 2.33/0.92  --stdin                                 false
% 2.33/0.92  --stats_out                             all
% 2.33/0.92  
% 2.33/0.92  ------ General Options
% 2.33/0.92  
% 2.33/0.92  --fof                                   false
% 2.33/0.92  --time_out_real                         305.
% 2.33/0.92  --time_out_virtual                      -1.
% 2.33/0.92  --symbol_type_check                     false
% 2.33/0.92  --clausify_out                          false
% 2.33/0.92  --sig_cnt_out                           false
% 2.33/0.92  --trig_cnt_out                          false
% 2.33/0.92  --trig_cnt_out_tolerance                1.
% 2.33/0.92  --trig_cnt_out_sk_spl                   false
% 2.33/0.92  --abstr_cl_out                          false
% 2.33/0.92  
% 2.33/0.92  ------ Global Options
% 2.33/0.92  
% 2.33/0.92  --schedule                              default
% 2.33/0.92  --add_important_lit                     false
% 2.33/0.92  --prop_solver_per_cl                    1000
% 2.33/0.92  --min_unsat_core                        false
% 2.33/0.92  --soft_assumptions                      false
% 2.33/0.92  --soft_lemma_size                       3
% 2.33/0.92  --prop_impl_unit_size                   0
% 2.33/0.92  --prop_impl_unit                        []
% 2.33/0.92  --share_sel_clauses                     true
% 2.33/0.92  --reset_solvers                         false
% 2.33/0.92  --bc_imp_inh                            [conj_cone]
% 2.33/0.92  --conj_cone_tolerance                   3.
% 2.33/0.92  --extra_neg_conj                        none
% 2.33/0.92  --large_theory_mode                     true
% 2.33/0.92  --prolific_symb_bound                   200
% 2.33/0.92  --lt_threshold                          2000
% 2.33/0.92  --clause_weak_htbl                      true
% 2.33/0.92  --gc_record_bc_elim                     false
% 2.33/0.92  
% 2.33/0.92  ------ Preprocessing Options
% 2.33/0.92  
% 2.33/0.92  --preprocessing_flag                    true
% 2.33/0.92  --time_out_prep_mult                    0.1
% 2.33/0.92  --splitting_mode                        input
% 2.33/0.92  --splitting_grd                         true
% 2.33/0.92  --splitting_cvd                         false
% 2.33/0.92  --splitting_cvd_svl                     false
% 2.33/0.92  --splitting_nvd                         32
% 2.33/0.92  --sub_typing                            true
% 2.33/0.92  --prep_gs_sim                           true
% 2.33/0.92  --prep_unflatten                        true
% 2.33/0.92  --prep_res_sim                          true
% 2.33/0.92  --prep_upred                            true
% 2.33/0.92  --prep_sem_filter                       exhaustive
% 2.33/0.92  --prep_sem_filter_out                   false
% 2.33/0.92  --pred_elim                             true
% 2.33/0.92  --res_sim_input                         true
% 2.33/0.92  --eq_ax_congr_red                       true
% 2.33/0.92  --pure_diseq_elim                       true
% 2.33/0.92  --brand_transform                       false
% 2.33/0.92  --non_eq_to_eq                          false
% 2.33/0.92  --prep_def_merge                        true
% 2.33/0.92  --prep_def_merge_prop_impl              false
% 2.33/0.92  --prep_def_merge_mbd                    true
% 2.33/0.92  --prep_def_merge_tr_red                 false
% 2.33/0.92  --prep_def_merge_tr_cl                  false
% 2.33/0.92  --smt_preprocessing                     true
% 2.33/0.92  --smt_ac_axioms                         fast
% 2.33/0.92  --preprocessed_out                      false
% 2.33/0.92  --preprocessed_stats                    false
% 2.33/0.92  
% 2.33/0.92  ------ Abstraction refinement Options
% 2.33/0.92  
% 2.33/0.92  --abstr_ref                             []
% 2.33/0.92  --abstr_ref_prep                        false
% 2.33/0.92  --abstr_ref_until_sat                   false
% 2.33/0.92  --abstr_ref_sig_restrict                funpre
% 2.33/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.92  --abstr_ref_under                       []
% 2.33/0.92  
% 2.33/0.92  ------ SAT Options
% 2.33/0.92  
% 2.33/0.92  --sat_mode                              false
% 2.33/0.92  --sat_fm_restart_options                ""
% 2.33/0.92  --sat_gr_def                            false
% 2.33/0.92  --sat_epr_types                         true
% 2.33/0.92  --sat_non_cyclic_types                  false
% 2.33/0.92  --sat_finite_models                     false
% 2.33/0.92  --sat_fm_lemmas                         false
% 2.33/0.92  --sat_fm_prep                           false
% 2.33/0.92  --sat_fm_uc_incr                        true
% 2.33/0.92  --sat_out_model                         small
% 2.33/0.92  --sat_out_clauses                       false
% 2.33/0.92  
% 2.33/0.92  ------ QBF Options
% 2.33/0.92  
% 2.33/0.92  --qbf_mode                              false
% 2.33/0.92  --qbf_elim_univ                         false
% 2.33/0.92  --qbf_dom_inst                          none
% 2.33/0.92  --qbf_dom_pre_inst                      false
% 2.33/0.92  --qbf_sk_in                             false
% 2.33/0.92  --qbf_pred_elim                         true
% 2.33/0.92  --qbf_split                             512
% 2.33/0.92  
% 2.33/0.92  ------ BMC1 Options
% 2.33/0.92  
% 2.33/0.92  --bmc1_incremental                      false
% 2.33/0.92  --bmc1_axioms                           reachable_all
% 2.33/0.92  --bmc1_min_bound                        0
% 2.33/0.92  --bmc1_max_bound                        -1
% 2.33/0.92  --bmc1_max_bound_default                -1
% 2.33/0.92  --bmc1_symbol_reachability              true
% 2.33/0.92  --bmc1_property_lemmas                  false
% 2.33/0.92  --bmc1_k_induction                      false
% 2.33/0.92  --bmc1_non_equiv_states                 false
% 2.33/0.92  --bmc1_deadlock                         false
% 2.33/0.92  --bmc1_ucm                              false
% 2.33/0.92  --bmc1_add_unsat_core                   none
% 2.33/0.92  --bmc1_unsat_core_children              false
% 2.33/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.92  --bmc1_out_stat                         full
% 2.33/0.92  --bmc1_ground_init                      false
% 2.33/0.92  --bmc1_pre_inst_next_state              false
% 2.33/0.92  --bmc1_pre_inst_state                   false
% 2.33/0.92  --bmc1_pre_inst_reach_state             false
% 2.33/0.92  --bmc1_out_unsat_core                   false
% 2.33/0.92  --bmc1_aig_witness_out                  false
% 2.33/0.92  --bmc1_verbose                          false
% 2.33/0.92  --bmc1_dump_clauses_tptp                false
% 2.33/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.92  --bmc1_dump_file                        -
% 2.33/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.92  --bmc1_ucm_extend_mode                  1
% 2.33/0.92  --bmc1_ucm_init_mode                    2
% 2.33/0.92  --bmc1_ucm_cone_mode                    none
% 2.33/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.92  --bmc1_ucm_relax_model                  4
% 2.33/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.92  --bmc1_ucm_layered_model                none
% 2.33/0.92  --bmc1_ucm_max_lemma_size               10
% 2.33/0.92  
% 2.33/0.92  ------ AIG Options
% 2.33/0.92  
% 2.33/0.92  --aig_mode                              false
% 2.33/0.92  
% 2.33/0.92  ------ Instantiation Options
% 2.33/0.92  
% 2.33/0.92  --instantiation_flag                    true
% 2.33/0.92  --inst_sos_flag                         false
% 2.33/0.92  --inst_sos_phase                        true
% 2.33/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.92  --inst_lit_sel_side                     none
% 2.33/0.92  --inst_solver_per_active                1400
% 2.33/0.92  --inst_solver_calls_frac                1.
% 2.33/0.92  --inst_passive_queue_type               priority_queues
% 2.33/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.92  --inst_passive_queues_freq              [25;2]
% 2.33/0.92  --inst_dismatching                      true
% 2.33/0.92  --inst_eager_unprocessed_to_passive     true
% 2.33/0.92  --inst_prop_sim_given                   true
% 2.33/0.92  --inst_prop_sim_new                     false
% 2.33/0.92  --inst_subs_new                         false
% 2.33/0.92  --inst_eq_res_simp                      false
% 2.33/0.92  --inst_subs_given                       false
% 2.33/0.92  --inst_orphan_elimination               true
% 2.33/0.92  --inst_learning_loop_flag               true
% 2.33/0.92  --inst_learning_start                   3000
% 2.33/0.92  --inst_learning_factor                  2
% 2.33/0.92  --inst_start_prop_sim_after_learn       3
% 2.33/0.92  --inst_sel_renew                        solver
% 2.33/0.92  --inst_lit_activity_flag                true
% 2.33/0.92  --inst_restr_to_given                   false
% 2.33/0.92  --inst_activity_threshold               500
% 2.33/0.92  --inst_out_proof                        true
% 2.33/0.92  
% 2.33/0.92  ------ Resolution Options
% 2.33/0.92  
% 2.33/0.92  --resolution_flag                       false
% 2.33/0.92  --res_lit_sel                           adaptive
% 2.33/0.92  --res_lit_sel_side                      none
% 2.33/0.92  --res_ordering                          kbo
% 2.33/0.92  --res_to_prop_solver                    active
% 2.33/0.92  --res_prop_simpl_new                    false
% 2.33/0.92  --res_prop_simpl_given                  true
% 2.33/0.92  --res_passive_queue_type                priority_queues
% 2.33/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.92  --res_passive_queues_freq               [15;5]
% 2.33/0.92  --res_forward_subs                      full
% 2.33/0.92  --res_backward_subs                     full
% 2.33/0.92  --res_forward_subs_resolution           true
% 2.33/0.92  --res_backward_subs_resolution          true
% 2.33/0.92  --res_orphan_elimination                true
% 2.33/0.92  --res_time_limit                        2.
% 2.33/0.92  --res_out_proof                         true
% 2.33/0.92  
% 2.33/0.92  ------ Superposition Options
% 2.33/0.92  
% 2.33/0.92  --superposition_flag                    true
% 2.33/0.92  --sup_passive_queue_type                priority_queues
% 2.33/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.92  --demod_completeness_check              fast
% 2.33/0.92  --demod_use_ground                      true
% 2.33/0.92  --sup_to_prop_solver                    passive
% 2.33/0.92  --sup_prop_simpl_new                    true
% 2.33/0.92  --sup_prop_simpl_given                  true
% 2.33/0.92  --sup_fun_splitting                     false
% 2.33/0.92  --sup_smt_interval                      50000
% 2.33/0.92  
% 2.33/0.92  ------ Superposition Simplification Setup
% 2.33/0.92  
% 2.33/0.92  --sup_indices_passive                   []
% 2.33/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.92  --sup_full_bw                           [BwDemod]
% 2.33/0.92  --sup_immed_triv                        [TrivRules]
% 2.33/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.92  --sup_immed_bw_main                     []
% 2.33/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.92  
% 2.33/0.92  ------ Combination Options
% 2.33/0.92  
% 2.33/0.92  --comb_res_mult                         3
% 2.33/0.92  --comb_sup_mult                         2
% 2.33/0.92  --comb_inst_mult                        10
% 2.33/0.92  
% 2.33/0.92  ------ Debug Options
% 2.33/0.92  
% 2.33/0.92  --dbg_backtrace                         false
% 2.33/0.92  --dbg_dump_prop_clauses                 false
% 2.33/0.92  --dbg_dump_prop_clauses_file            -
% 2.33/0.92  --dbg_out_stat                          false
% 2.33/0.92  
% 2.33/0.92  
% 2.33/0.92  
% 2.33/0.92  
% 2.33/0.92  ------ Proving...
% 2.33/0.92  
% 2.33/0.92  
% 2.33/0.92  % SZS status Theorem for theBenchmark.p
% 2.33/0.92  
% 2.33/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/0.92  
% 2.33/0.92  fof(f3,axiom,(
% 2.33/0.92    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.33/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.92  
% 2.33/0.92  fof(f13,plain,(
% 2.33/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.33/0.92    inference(nnf_transformation,[],[f3])).
% 2.33/0.92  
% 2.33/0.92  fof(f14,plain,(
% 2.33/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.33/0.92    inference(flattening,[],[f13])).
% 2.33/0.92  
% 2.33/0.92  fof(f15,plain,(
% 2.33/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.33/0.92    inference(rectify,[],[f14])).
% 2.33/0.92  
% 2.33/0.92  fof(f16,plain,(
% 2.33/0.92    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.33/0.92    introduced(choice_axiom,[])).
% 2.33/0.92  
% 2.33/0.92  fof(f17,plain,(
% 2.33/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.33/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).
% 2.33/0.92  
% 2.33/0.92  fof(f28,plain,(
% 2.33/0.92    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.33/0.92    inference(cnf_transformation,[],[f17])).
% 2.33/0.92  
% 2.33/0.92  fof(f41,plain,(
% 2.33/0.92    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.33/0.92    inference(equality_resolution,[],[f28])).
% 2.33/0.92  
% 2.33/0.92  fof(f2,axiom,(
% 2.33/0.92    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.33/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.92  
% 2.33/0.92  fof(f8,plain,(
% 2.33/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.33/0.92    inference(nnf_transformation,[],[f2])).
% 2.33/0.92  
% 2.33/0.92  fof(f9,plain,(
% 2.33/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.33/0.92    inference(flattening,[],[f8])).
% 2.33/0.92  
% 2.33/0.92  fof(f10,plain,(
% 2.33/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.33/0.92    inference(rectify,[],[f9])).
% 2.33/0.92  
% 2.33/0.92  fof(f11,plain,(
% 2.33/0.92    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.33/0.92    introduced(choice_axiom,[])).
% 2.33/0.92  
% 2.33/0.92  fof(f12,plain,(
% 2.33/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.33/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).
% 2.33/0.92  
% 2.33/0.92  fof(f24,plain,(
% 2.33/0.92    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.33/0.92    inference(cnf_transformation,[],[f12])).
% 2.33/0.92  
% 2.33/0.92  fof(f4,axiom,(
% 2.33/0.92    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.33/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.92  
% 2.33/0.92  fof(f33,plain,(
% 2.33/0.92    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.33/0.92    inference(cnf_transformation,[],[f4])).
% 2.33/0.92  
% 2.33/0.92  fof(f1,axiom,(
% 2.33/0.92    k1_xboole_0 = o_0_0_xboole_0),
% 2.33/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.92  
% 2.33/0.92  fof(f20,plain,(
% 2.33/0.92    k1_xboole_0 = o_0_0_xboole_0),
% 2.33/0.92    inference(cnf_transformation,[],[f1])).
% 2.33/0.92  
% 2.33/0.92  fof(f35,plain,(
% 2.33/0.92    ( ! [X0] : (k2_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 2.33/0.92    inference(definition_unfolding,[],[f33,f20])).
% 2.33/0.92  
% 2.33/0.92  fof(f23,plain,(
% 2.33/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.33/0.92    inference(cnf_transformation,[],[f12])).
% 2.33/0.92  
% 2.33/0.92  fof(f37,plain,(
% 2.33/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.33/0.92    inference(equality_resolution,[],[f23])).
% 2.33/0.92  
% 2.33/0.92  fof(f25,plain,(
% 2.33/0.92    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.33/0.92    inference(cnf_transformation,[],[f12])).
% 2.33/0.92  
% 2.33/0.92  fof(f27,plain,(
% 2.33/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.33/0.92    inference(cnf_transformation,[],[f17])).
% 2.33/0.92  
% 2.33/0.92  fof(f42,plain,(
% 2.33/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.33/0.92    inference(equality_resolution,[],[f27])).
% 2.33/0.92  
% 2.33/0.92  fof(f22,plain,(
% 2.33/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.33/0.92    inference(cnf_transformation,[],[f12])).
% 2.33/0.92  
% 2.33/0.92  fof(f38,plain,(
% 2.33/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 2.33/0.92    inference(equality_resolution,[],[f22])).
% 2.33/0.92  
% 2.33/0.92  fof(f30,plain,(
% 2.33/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 2.33/0.92    inference(cnf_transformation,[],[f17])).
% 2.33/0.92  
% 2.33/0.92  fof(f31,plain,(
% 2.33/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 2.33/0.92    inference(cnf_transformation,[],[f17])).
% 2.33/0.92  
% 2.33/0.92  fof(f5,conjecture,(
% 2.33/0.92    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.33/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.92  
% 2.33/0.92  fof(f6,negated_conjecture,(
% 2.33/0.92    ~! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.33/0.92    inference(negated_conjecture,[],[f5])).
% 2.33/0.92  
% 2.33/0.92  fof(f7,plain,(
% 2.33/0.92    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.33/0.92    inference(ennf_transformation,[],[f6])).
% 2.33/0.92  
% 2.33/0.92  fof(f18,plain,(
% 2.33/0.92    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) => k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3))),
% 2.33/0.92    introduced(choice_axiom,[])).
% 2.33/0.92  
% 2.33/0.92  fof(f19,plain,(
% 2.33/0.92    k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3))),
% 2.33/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f7,f18])).
% 2.33/0.92  
% 2.33/0.92  fof(f34,plain,(
% 2.33/0.92    k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3))),
% 2.33/0.92    inference(cnf_transformation,[],[f19])).
% 2.33/0.92  
% 2.33/0.92  fof(f36,plain,(
% 2.33/0.92    o_0_0_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3))),
% 2.33/0.92    inference(definition_unfolding,[],[f34,f20])).
% 2.33/0.92  
% 2.33/0.92  cnf(c_10,plain,
% 2.33/0.92      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.33/0.92      inference(cnf_transformation,[],[f41]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1000,plain,
% 2.33/0.92      ( ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),X1)
% 2.33/0.92      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),k4_xboole_0(X2,X1)) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_10]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_3240,plain,
% 2.33/0.92      ( ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),X1)
% 2.33/0.92      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_1000]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_3241,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),X1) != iProver_top
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) != iProver_top ),
% 2.33/0.92      inference(predicate_to_equality,[status(thm)],[c_3240]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_3243,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)) != iProver_top
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0) != iProver_top ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_3241]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_2,plain,
% 2.33/0.92      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),X0)
% 2.33/0.92      | k2_xboole_0(X0,X1) = X2 ),
% 2.33/0.92      inference(cnf_transformation,[],[f24]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_340,plain,
% 2.33/0.92      ( k2_xboole_0(X0,X1) = X2
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 2.33/0.92      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_12,plain,
% 2.33/0.92      ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
% 2.33/0.92      inference(cnf_transformation,[],[f35]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_3,plain,
% 2.33/0.92      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 2.33/0.92      inference(cnf_transformation,[],[f37]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_339,plain,
% 2.33/0.92      ( r2_hidden(X0,X1) != iProver_top
% 2.33/0.92      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 2.33/0.92      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1,plain,
% 2.33/0.92      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.33/0.92      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.33/0.92      | k2_xboole_0(X0,X1) = X2 ),
% 2.33/0.92      inference(cnf_transformation,[],[f25]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_341,plain,
% 2.33/0.92      ( k2_xboole_0(X0,X1) = X2
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
% 2.33/0.92      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1193,plain,
% 2.33/0.92      ( k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)
% 2.33/0.92      | r2_hidden(sK0(X2,X3,k2_xboole_0(X0,X1)),X1) != iProver_top
% 2.33/0.92      | r2_hidden(sK0(X2,X3,k2_xboole_0(X0,X1)),X2) != iProver_top ),
% 2.33/0.92      inference(superposition,[status(thm)],[c_339,c_341]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1367,plain,
% 2.33/0.92      ( k2_xboole_0(X0,X1) = k2_xboole_0(X2,o_0_0_xboole_0)
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),o_0_0_xboole_0) != iProver_top
% 2.33/0.92      | r2_hidden(sK0(X0,X1,k2_xboole_0(X2,o_0_0_xboole_0)),X0) != iProver_top ),
% 2.33/0.92      inference(superposition,[status(thm)],[c_12,c_1193]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1371,plain,
% 2.33/0.92      ( k2_xboole_0(X0,X1) = X2
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),o_0_0_xboole_0) != iProver_top ),
% 2.33/0.92      inference(demodulation,[status(thm)],[c_1367,c_12]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_576,plain,
% 2.33/0.92      ( r2_hidden(X0,X1) = iProver_top
% 2.33/0.92      | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 2.33/0.92      inference(superposition,[status(thm)],[c_12,c_339]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1699,plain,
% 2.33/0.92      ( k2_xboole_0(X0,X1) = X2
% 2.33/0.92      | r2_hidden(sK0(X0,X1,X2),o_0_0_xboole_0) != iProver_top ),
% 2.33/0.92      inference(forward_subsumption_resolution,
% 2.33/0.92                [status(thm)],
% 2.33/0.92                [c_1371,c_576]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_2518,plain,
% 2.33/0.92      ( k2_xboole_0(X0,o_0_0_xboole_0) = X1
% 2.33/0.92      | r2_hidden(sK0(X0,o_0_0_xboole_0,X1),X1) = iProver_top
% 2.33/0.92      | r2_hidden(sK0(X0,o_0_0_xboole_0,X1),X0) = iProver_top ),
% 2.33/0.92      inference(superposition,[status(thm)],[c_340,c_1699]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_2552,plain,
% 2.33/0.92      ( X0 = X1
% 2.33/0.92      | r2_hidden(sK0(X1,o_0_0_xboole_0,X0),X0) = iProver_top
% 2.33/0.92      | r2_hidden(sK0(X1,o_0_0_xboole_0,X0),X1) = iProver_top ),
% 2.33/0.92      inference(demodulation,[status(thm)],[c_2518,c_12]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_2749,plain,
% 2.33/0.92      ( k2_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
% 2.33/0.92      | o_0_0_xboole_0 = X0
% 2.33/0.92      | r2_hidden(sK0(X0,o_0_0_xboole_0,o_0_0_xboole_0),X0) = iProver_top ),
% 2.33/0.92      inference(superposition,[status(thm)],[c_2552,c_1699]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_2755,plain,
% 2.33/0.92      ( o_0_0_xboole_0 = X0
% 2.33/0.92      | r2_hidden(sK0(X0,o_0_0_xboole_0,o_0_0_xboole_0),X0) = iProver_top ),
% 2.33/0.92      inference(demodulation,[status(thm)],[c_2749,c_12]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_332,plain,
% 2.33/0.92      ( r2_hidden(X0,X1) != iProver_top
% 2.33/0.92      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.33/0.92      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_3101,plain,
% 2.33/0.92      ( k4_xboole_0(X0,X1) = o_0_0_xboole_0
% 2.33/0.92      | r2_hidden(sK0(k4_xboole_0(X0,X1),o_0_0_xboole_0,o_0_0_xboole_0),X1) != iProver_top ),
% 2.33/0.92      inference(superposition,[status(thm)],[c_2755,c_332]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_3121,plain,
% 2.33/0.92      ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
% 2.33/0.92      | r2_hidden(sK0(k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) != iProver_top ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_3101]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_11,plain,
% 2.33/0.92      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.33/0.92      inference(cnf_transformation,[],[f42]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_331,plain,
% 2.33/0.92      ( r2_hidden(X0,X1) = iProver_top
% 2.33/0.92      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 2.33/0.92      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_2732,plain,
% 2.33/0.92      ( k4_xboole_0(X0,X1) = X2
% 2.33/0.92      | r2_hidden(sK0(k4_xboole_0(X0,X1),o_0_0_xboole_0,X2),X2) = iProver_top
% 2.33/0.92      | r2_hidden(sK0(k4_xboole_0(X0,X1),o_0_0_xboole_0,X2),X0) = iProver_top ),
% 2.33/0.92      inference(superposition,[status(thm)],[c_2552,c_331]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_2835,plain,
% 2.33/0.92      ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
% 2.33/0.92      | r2_hidden(sK0(k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = iProver_top ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_2732]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_4,plain,
% 2.33/0.92      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 2.33/0.92      inference(cnf_transformation,[],[f38]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_476,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),k2_xboole_0(sK2,X1))
% 2.33/0.92      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),sK2) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_4]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_621,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),k2_xboole_0(sK2,sK3))
% 2.33/0.92      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),sK2) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_476]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1838,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k2_xboole_0(sK2,sK3))
% 2.33/0.92      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),sK2) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_621]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1839,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k2_xboole_0(sK2,sK3)) = iProver_top
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),sK2) != iProver_top ),
% 2.33/0.92      inference(predicate_to_equality,[status(thm)],[c_1838]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1841,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k2_xboole_0(sK2,sK3)) = iProver_top
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),sK2) != iProver_top ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_1839]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_8,plain,
% 2.33/0.92      ( r2_hidden(sK1(X0,X1,X2),X0)
% 2.33/0.92      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.33/0.92      | k4_xboole_0(X0,X1) = X2 ),
% 2.33/0.92      inference(cnf_transformation,[],[f30]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_453,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),X0)
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),sK2)
% 2.33/0.92      | k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = X0 ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_8]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1254,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),sK2)
% 2.33/0.92      | k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,X1) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_453]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1255,plain,
% 2.33/0.92      ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,X1)
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = iProver_top
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),sK2) = iProver_top ),
% 2.33/0.92      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_1257,plain,
% 2.33/0.92      ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),sK2) = iProver_top ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_1255]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_133,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_561,plain,
% 2.33/0.92      ( k4_xboole_0(X0,X1) != X2
% 2.33/0.92      | o_0_0_xboole_0 != X2
% 2.33/0.92      | o_0_0_xboole_0 = k4_xboole_0(X0,X1) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_133]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_562,plain,
% 2.33/0.92      ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
% 2.33/0.92      | o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
% 2.33/0.92      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_561]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_530,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),X0)
% 2.33/0.92      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_11]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_535,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),X0) = iProver_top
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) != iProver_top ),
% 2.33/0.92      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_537,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)) != iProver_top
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0) = iProver_top ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_535]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_7,plain,
% 2.33/0.92      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 2.33/0.92      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.33/0.92      | k4_xboole_0(X0,X1) = X2 ),
% 2.33/0.92      inference(cnf_transformation,[],[f31]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_454,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),X0)
% 2.33/0.92      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),X0),k2_xboole_0(sK2,sK3))
% 2.33/0.92      | k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = X0 ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_7]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_529,plain,
% 2.33/0.92      ( r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))
% 2.33/0.92      | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k2_xboole_0(sK2,sK3))
% 2.33/0.92      | k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,X1) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_454]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_531,plain,
% 2.33/0.92      ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,X1)
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = iProver_top
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(X0,X1)),k2_xboole_0(sK2,sK3)) != iProver_top ),
% 2.33/0.92      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_533,plain,
% 2.33/0.92      ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top
% 2.33/0.92      | r2_hidden(sK1(sK2,k2_xboole_0(sK2,sK3),k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)),k2_xboole_0(sK2,sK3)) != iProver_top ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_531]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_440,plain,
% 2.33/0.92      ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) != X0
% 2.33/0.92      | o_0_0_xboole_0 != X0
% 2.33/0.92      | o_0_0_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_133]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_469,plain,
% 2.33/0.92      ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) != k4_xboole_0(X0,X1)
% 2.33/0.92      | o_0_0_xboole_0 != k4_xboole_0(X0,X1)
% 2.33/0.92      | o_0_0_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_440]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_471,plain,
% 2.33/0.92      ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) != k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
% 2.33/0.92      | o_0_0_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK2,sK3))
% 2.33/0.92      | o_0_0_xboole_0 != k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_469]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_132,plain,( X0 = X0 ),theory(equality) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_141,plain,
% 2.33/0.92      ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 2.33/0.92      inference(instantiation,[status(thm)],[c_132]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(c_13,negated_conjecture,
% 2.33/0.92      ( o_0_0_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
% 2.33/0.92      inference(cnf_transformation,[],[f36]) ).
% 2.33/0.92  
% 2.33/0.92  cnf(contradiction,plain,
% 2.33/0.92      ( $false ),
% 2.33/0.92      inference(minisat,
% 2.33/0.92                [status(thm)],
% 2.33/0.92                [c_3243,c_3121,c_2835,c_1841,c_1257,c_562,c_537,c_533,
% 2.33/0.92                 c_471,c_141,c_13]) ).
% 2.33/0.92  
% 2.33/0.92  
% 2.33/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/0.92  
% 2.33/0.92  ------                               Statistics
% 2.33/0.92  
% 2.33/0.92  ------ General
% 2.33/0.92  
% 2.33/0.92  abstr_ref_over_cycles:                  0
% 2.33/0.92  abstr_ref_under_cycles:                 0
% 2.33/0.92  gc_basic_clause_elim:                   0
% 2.33/0.92  forced_gc_time:                         0
% 2.33/0.92  parsing_time:                           0.007
% 2.33/0.92  unif_index_cands_time:                  0.
% 2.33/0.92  unif_index_add_time:                    0.
% 2.33/0.92  orderings_time:                         0.
% 2.33/0.92  out_proof_time:                         0.006
% 2.33/0.92  total_time:                             0.135
% 2.33/0.92  num_of_symbols:                         39
% 2.33/0.92  num_of_terms:                           4940
% 2.33/0.92  
% 2.33/0.92  ------ Preprocessing
% 2.33/0.92  
% 2.33/0.92  num_of_splits:                          0
% 2.33/0.92  num_of_split_atoms:                     0
% 2.33/0.92  num_of_reused_defs:                     0
% 2.33/0.92  num_eq_ax_congr_red:                    12
% 2.33/0.92  num_of_sem_filtered_clauses:            1
% 2.33/0.92  num_of_subtypes:                        0
% 2.33/0.92  monotx_restored_types:                  0
% 2.33/0.92  sat_num_of_epr_types:                   0
% 2.33/0.92  sat_num_of_non_cyclic_types:            0
% 2.33/0.92  sat_guarded_non_collapsed_types:        0
% 2.33/0.92  num_pure_diseq_elim:                    0
% 2.33/0.92  simp_replaced_by:                       0
% 2.33/0.92  res_preprocessed:                       53
% 2.33/0.92  prep_upred:                             0
% 2.33/0.92  prep_unflattend:                        0
% 2.33/0.92  smt_new_axioms:                         0
% 2.33/0.92  pred_elim_cands:                        1
% 2.33/0.92  pred_elim:                              0
% 2.33/0.92  pred_elim_cl:                           0
% 2.33/0.92  pred_elim_cycles:                       1
% 2.33/0.92  merged_defs:                            0
% 2.33/0.92  merged_defs_ncl:                        0
% 2.33/0.92  bin_hyper_res:                          0
% 2.33/0.92  prep_cycles:                            3
% 2.33/0.92  pred_elim_time:                         0.
% 2.33/0.92  splitting_time:                         0.
% 2.33/0.92  sem_filter_time:                        0.
% 2.33/0.92  monotx_time:                            0.
% 2.33/0.92  subtype_inf_time:                       0.
% 2.33/0.92  
% 2.33/0.92  ------ Problem properties
% 2.33/0.92  
% 2.33/0.92  clauses:                                14
% 2.33/0.92  conjectures:                            1
% 2.33/0.92  epr:                                    0
% 2.33/0.92  horn:                                   8
% 2.33/0.92  ground:                                 1
% 2.33/0.92  unary:                                  2
% 2.33/0.92  binary:                                 4
% 2.33/0.92  lits:                                   36
% 2.33/0.92  lits_eq:                                8
% 2.33/0.92  fd_pure:                                0
% 2.33/0.92  fd_pseudo:                              0
% 2.33/0.92  fd_cond:                                0
% 2.33/0.92  fd_pseudo_cond:                         6
% 2.33/0.92  ac_symbols:                             0
% 2.33/0.92  
% 2.33/0.92  ------ Propositional Solver
% 2.33/0.92  
% 2.33/0.92  prop_solver_calls:                      23
% 2.33/0.92  prop_fast_solver_calls:                 349
% 2.33/0.92  smt_solver_calls:                       0
% 2.33/0.92  smt_fast_solver_calls:                  0
% 2.33/0.92  prop_num_of_clauses:                    1386
% 2.33/0.92  prop_preprocess_simplified:             4088
% 2.33/0.92  prop_fo_subsumed:                       0
% 2.33/0.92  prop_solver_time:                       0.
% 2.33/0.92  smt_solver_time:                        0.
% 2.33/0.92  smt_fast_solver_time:                   0.
% 2.33/0.92  prop_fast_solver_time:                  0.
% 2.33/0.92  prop_unsat_core_time:                   0.
% 2.33/0.92  
% 2.33/0.92  ------ QBF
% 2.33/0.92  
% 2.33/0.92  qbf_q_res:                              0
% 2.33/0.92  qbf_num_tautologies:                    0
% 2.33/0.92  qbf_prep_cycles:                        0
% 2.33/0.92  
% 2.33/0.92  ------ BMC1
% 2.33/0.92  
% 2.33/0.92  bmc1_current_bound:                     -1
% 2.33/0.92  bmc1_last_solved_bound:                 -1
% 2.33/0.92  bmc1_unsat_core_size:                   -1
% 2.33/0.92  bmc1_unsat_core_parents_size:           -1
% 2.33/0.92  bmc1_merge_next_fun:                    0
% 2.33/0.92  bmc1_unsat_core_clauses_time:           0.
% 2.33/0.92  
% 2.33/0.92  ------ Instantiation
% 2.33/0.92  
% 2.33/0.92  inst_num_of_clauses:                    351
% 2.33/0.92  inst_num_in_passive:                    60
% 2.33/0.92  inst_num_in_active:                     110
% 2.33/0.92  inst_num_in_unprocessed:                181
% 2.33/0.92  inst_num_of_loops:                      144
% 2.33/0.92  inst_num_of_learning_restarts:          0
% 2.33/0.92  inst_num_moves_active_passive:          30
% 2.33/0.92  inst_lit_activity:                      0
% 2.33/0.92  inst_lit_activity_moves:                0
% 2.33/0.92  inst_num_tautologies:                   0
% 2.33/0.92  inst_num_prop_implied:                  0
% 2.33/0.92  inst_num_existing_simplified:           0
% 2.33/0.92  inst_num_eq_res_simplified:             0
% 2.33/0.92  inst_num_child_elim:                    0
% 2.33/0.92  inst_num_of_dismatching_blockings:      203
% 2.33/0.92  inst_num_of_non_proper_insts:           281
% 2.33/0.92  inst_num_of_duplicates:                 0
% 2.33/0.92  inst_inst_num_from_inst_to_res:         0
% 2.33/0.92  inst_dismatching_checking_time:         0.
% 2.33/0.92  
% 2.33/0.92  ------ Resolution
% 2.33/0.92  
% 2.33/0.92  res_num_of_clauses:                     0
% 2.33/0.92  res_num_in_passive:                     0
% 2.33/0.92  res_num_in_active:                      0
% 2.33/0.92  res_num_of_loops:                       56
% 2.33/0.92  res_forward_subset_subsumed:            39
% 2.33/0.92  res_backward_subset_subsumed:           2
% 2.33/0.92  res_forward_subsumed:                   0
% 2.33/0.92  res_backward_subsumed:                  0
% 2.33/0.92  res_forward_subsumption_resolution:     0
% 2.33/0.92  res_backward_subsumption_resolution:    0
% 2.33/0.92  res_clause_to_clause_subsumption:       826
% 2.33/0.92  res_orphan_elimination:                 0
% 2.33/0.92  res_tautology_del:                      38
% 2.33/0.92  res_num_eq_res_simplified:              0
% 2.33/0.92  res_num_sel_changes:                    0
% 2.33/0.92  res_moves_from_active_to_pass:          0
% 2.33/0.92  
% 2.33/0.92  ------ Superposition
% 2.33/0.92  
% 2.33/0.92  sup_time_total:                         0.
% 2.33/0.92  sup_time_generating:                    0.
% 2.33/0.92  sup_time_sim_full:                      0.
% 2.33/0.92  sup_time_sim_immed:                     0.
% 2.33/0.92  
% 2.33/0.92  sup_num_of_clauses:                     99
% 2.33/0.92  sup_num_in_active:                      28
% 2.33/0.92  sup_num_in_passive:                     71
% 2.33/0.92  sup_num_of_loops:                       28
% 2.33/0.92  sup_fw_superposition:                   65
% 2.33/0.92  sup_bw_superposition:                   76
% 2.33/0.92  sup_immediate_simplified:               39
% 2.33/0.92  sup_given_eliminated:                   0
% 2.33/0.92  comparisons_done:                       0
% 2.33/0.92  comparisons_avoided:                    0
% 2.33/0.92  
% 2.33/0.92  ------ Simplifications
% 2.33/0.92  
% 2.33/0.92  
% 2.33/0.92  sim_fw_subset_subsumed:                 9
% 2.33/0.92  sim_bw_subset_subsumed:                 0
% 2.33/0.92  sim_fw_subsumed:                        14
% 2.33/0.92  sim_bw_subsumed:                        1
% 2.33/0.92  sim_fw_subsumption_res:                 5
% 2.33/0.92  sim_bw_subsumption_res:                 0
% 2.33/0.92  sim_tautology_del:                      19
% 2.33/0.92  sim_eq_tautology_del:                   6
% 2.33/0.92  sim_eq_res_simp:                        7
% 2.33/0.92  sim_fw_demodulated:                     17
% 2.33/0.92  sim_bw_demodulated:                     0
% 2.33/0.92  sim_light_normalised:                   0
% 2.33/0.92  sim_joinable_taut:                      0
% 2.33/0.92  sim_joinable_simp:                      0
% 2.33/0.92  sim_ac_normalised:                      0
% 2.33/0.92  sim_smt_subsumption:                    0
% 2.33/0.92  
%------------------------------------------------------------------------------
