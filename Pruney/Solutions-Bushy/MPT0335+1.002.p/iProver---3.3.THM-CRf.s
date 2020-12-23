%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0335+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:02 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 668 expanded)
%              Number of clauses        :   58 ( 208 expanded)
%              Number of leaves         :   11 ( 137 expanded)
%              Depth                    :   18
%              Number of atoms          :  322 (3293 expanded)
%              Number of equality atoms :  170 (1200 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k1_tarski(X3) = k3_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k1_tarski(X3) = k3_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k1_tarski(X3) = k3_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k1_tarski(X3) = k3_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k1_tarski(X3) = k3_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK5) != k3_xboole_0(sK2,sK4)
      & r2_hidden(sK5,sK2)
      & k1_tarski(sK5) = k3_xboole_0(sK3,sK4)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k1_tarski(sK5) != k3_xboole_0(sK2,sK4)
    & r2_hidden(sK5,sK2)
    & k1_tarski(sK5) = k3_xboole_0(sK3,sK4)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f24])).

fof(f44,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    k1_tarski(sK5) = k3_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    k1_tarski(sK5) != k3_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f28])).

fof(f47,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f46])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_479,plain,
    ( r2_hidden(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_478,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( k1_tarski(sK5) = k3_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_480,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1043,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k3_xboole_0(X0,sK4),k1_tarski(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_480])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_481,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2087,plain,
    ( k3_xboole_0(X0,sK4) = k1_tarski(sK5)
    | k3_xboole_0(X0,sK4) = k1_xboole_0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1043,c_481])).

cnf(c_2661,plain,
    ( k3_xboole_0(sK2,sK4) = k1_tarski(sK5)
    | k3_xboole_0(sK2,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_478,c_2087])).

cnf(c_16,negated_conjecture,
    ( k1_tarski(sK5) != k3_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_193,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_639,plain,
    ( k3_xboole_0(sK2,sK4) != X0
    | k1_tarski(sK5) != X0
    | k1_tarski(sK5) = k3_xboole_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_713,plain,
    ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
    | k1_tarski(sK5) = k3_xboole_0(sK2,sK4)
    | k1_tarski(sK5) != k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_192,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_714,plain,
    ( k1_tarski(sK5) = k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_2662,plain,
    ( k3_xboole_0(sK2,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2661,c_16,c_713,c_714])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_486,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2979,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2662,c_486])).

cnf(c_8890,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_479,c_2979])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_491,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_485,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2172,plain,
    ( r2_hidden(X0,k1_tarski(sK5)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_485])).

cnf(c_2183,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_491,c_2172])).

cnf(c_9375,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8890,c_2183])).

cnf(c_15,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_484,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1288,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_484])).

cnf(c_9381,plain,
    ( r2_hidden(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9375,c_1288])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_490,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9506,plain,
    ( sK5 = X0 ),
    inference(superposition,[status(thm)],[c_9381,c_490])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_487,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3437,plain,
    ( k3_xboole_0(X0,X1) = k1_tarski(sK5)
    | r2_hidden(sK1(X0,X1,k1_tarski(sK5)),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,k1_tarski(sK5)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_487,c_2172])).

cnf(c_4089,plain,
    ( k3_xboole_0(k1_tarski(sK5),X0) = k1_tarski(sK5)
    | r2_hidden(sK1(k1_tarski(sK5),X0,k1_tarski(sK5)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3437,c_2172])).

cnf(c_2980,plain,
    ( r2_hidden(X0,k1_tarski(sK5)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_486])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_489,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5082,plain,
    ( k3_xboole_0(k1_tarski(sK5),X0) = X1
    | r2_hidden(sK1(k1_tarski(sK5),X0,X1),X1) != iProver_top
    | r2_hidden(sK1(k1_tarski(sK5),X0,X1),X0) != iProver_top
    | r2_hidden(sK1(k1_tarski(sK5),X0,X1),sK3) != iProver_top
    | r2_hidden(sK1(k1_tarski(sK5),X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2980,c_489])).

cnf(c_5497,plain,
    ( k3_xboole_0(k1_tarski(sK5),X0) = k1_tarski(sK5)
    | r2_hidden(sK1(k1_tarski(sK5),X0,k1_tarski(sK5)),X0) != iProver_top
    | r2_hidden(sK1(k1_tarski(sK5),X0,k1_tarski(sK5)),sK3) != iProver_top
    | r2_hidden(sK1(k1_tarski(sK5),X0,k1_tarski(sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2980,c_5082])).

cnf(c_1289,plain,
    ( r2_hidden(X0,k1_tarski(sK5)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_484])).

cnf(c_3438,plain,
    ( k3_xboole_0(X0,X1) = k1_tarski(sK5)
    | r2_hidden(sK1(X0,X1,k1_tarski(sK5)),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,k1_tarski(sK5)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_487,c_1289])).

cnf(c_4363,plain,
    ( k3_xboole_0(k1_tarski(sK5),X0) = k1_tarski(sK5)
    | r2_hidden(sK1(k1_tarski(sK5),X0,k1_tarski(sK5)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3438,c_1289])).

cnf(c_5712,plain,
    ( k3_xboole_0(k1_tarski(sK5),X0) = k1_tarski(sK5)
    | r2_hidden(sK1(k1_tarski(sK5),X0,k1_tarski(sK5)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5497,c_4089,c_4363])).

cnf(c_5732,plain,
    ( k3_xboole_0(k1_tarski(sK5),sK4) = k1_tarski(sK5) ),
    inference(superposition,[status(thm)],[c_4089,c_5712])).

cnf(c_9555,plain,
    ( k3_xboole_0(sK5,sK4) = sK5 ),
    inference(demodulation,[status(thm)],[c_9506,c_5732])).

cnf(c_9584,plain,
    ( k3_xboole_0(sK5,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9506,c_2662])).

cnf(c_9707,plain,
    ( sK5 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9555,c_9584])).

cnf(c_2665,plain,
    ( k1_tarski(sK5) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2662,c_16])).

cnf(c_9574,plain,
    ( sK5 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9506,c_2665])).

cnf(c_9709,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9707,c_9574])).


%------------------------------------------------------------------------------
