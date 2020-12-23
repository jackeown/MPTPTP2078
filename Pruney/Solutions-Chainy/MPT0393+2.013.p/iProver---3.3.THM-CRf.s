%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:35 EST 2020

% Result     : Theorem 19.02s
% Output     : CNFRefutation 19.02s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 280 expanded)
%              Number of clauses        :   47 (  71 expanded)
%              Number of leaves         :   18 (  69 expanded)
%              Depth                    :   20
%              Number of atoms          :  352 ( 791 expanded)
%              Number of equality atoms :  202 ( 447 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f43])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f81])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f62,f82])).

fof(f115,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f63,f82])).

fof(f113,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f93])).

fof(f114,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f113])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f75,f82])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f45])).

fof(f80,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f46])).

fof(f103,plain,(
    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(definition_unfolding,[],[f80,f82])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f106,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f107,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f106])).

cnf(c_28,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_55234,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_28,c_18])).

cnf(c_54689,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_54696,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_55544,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | sK3(k2_enumset1(X0,X0,X0,X0),X1) = X0
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_54689,c_54696])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_67,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_7030,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7029,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7702,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7030,c_7029])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_7014,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8094,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7702,c_7014])).

cnf(c_58520,plain,
    ( sK3(k2_enumset1(X0,X0,X0,X0),X1) = X0
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55544,c_67,c_8094])).

cnf(c_58522,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_58520])).

cnf(c_58985,plain,
    ( sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_55234,c_58522])).

cnf(c_58986,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1 ),
    inference(renaming,[status(thm)],[c_58985])).

cnf(c_532,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_531,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_55711,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_532,c_531])).

cnf(c_59657,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | X1 = sK3(k2_enumset1(X1,X1,X1,X1),X0) ),
    inference(resolution,[status(thm)],[c_58986,c_55711])).

cnf(c_534,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_56235,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_534,c_531])).

cnf(c_59702,plain,
    ( r1_tarski(X0,X1)
    | r1_tarski(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))
    | ~ r1_tarski(sK3(k2_enumset1(X0,X0,X0,X0),X2),X1) ),
    inference(resolution,[status(thm)],[c_59657,c_56235])).

cnf(c_61768,plain,
    ( r1_tarski(X0,sK3(k2_enumset1(X0,X0,X0,X0),X1))
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) ),
    inference(resolution,[status(thm)],[c_59702,c_4])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,sK3(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_63815,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))
    | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ),
    inference(resolution,[status(thm)],[c_61768,c_27])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_54953,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(resolution,[status(thm)],[c_2,c_30])).

cnf(c_3508,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_29,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_7726,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X3,X0)),X1) ),
    inference(resolution,[status(thm)],[c_29,c_11])).

cnf(c_7467,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(resolution,[status(thm)],[c_2,c_30])).

cnf(c_8135,plain,
    ( ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ r1_tarski(sK4,sK4) ),
    inference(resolution,[status(thm)],[c_7726,c_7467])).

cnf(c_54956,plain,
    ( ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54953,c_3508,c_8135])).

cnf(c_63884,plain,
    ( k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_63815,c_54956])).

cnf(c_63933,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63884,c_55711])).

cnf(c_55709,plain,
    ( ~ r1_tarski(X0,X1)
    | X2 != k1_xboole_0
    | k4_xboole_0(X0,X1) = X2 ),
    inference(resolution,[status(thm)],[c_532,c_5])).

cnf(c_55909,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X1,X0)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55709,c_26])).

cnf(c_56792,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55909,c_4])).

cnf(c_56800,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_56792,c_67,c_8094])).

cnf(c_64088,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_63933,c_56800])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.07  % Command    : iproveropt_run.sh %d %s
% 0.06/0.26  % Computer   : n022.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 09:57:25 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.10/0.26  % Running in FOF mode
% 19.02/2.90  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.02/2.90  
% 19.02/2.90  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.02/2.90  
% 19.02/2.90  ------  iProver source info
% 19.02/2.90  
% 19.02/2.90  git: date: 2020-06-30 10:37:57 +0100
% 19.02/2.90  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.02/2.90  git: non_committed_changes: false
% 19.02/2.90  git: last_make_outside_of_git: false
% 19.02/2.90  
% 19.02/2.90  ------ 
% 19.02/2.90  ------ Parsing...
% 19.02/2.90  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  ------ Proving...
% 19.02/2.90  ------ Problem Properties 
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  clauses                                 30
% 19.02/2.90  conjectures                             1
% 19.02/2.90  EPR                                     2
% 19.02/2.90  Horn                                    21
% 19.02/2.90  unary                                   9
% 19.02/2.90  binary                                  6
% 19.02/2.90  lits                                    69
% 19.02/2.90  lits eq                                 31
% 19.02/2.90  fd_pure                                 0
% 19.02/2.90  fd_pseudo                               0
% 19.02/2.90  fd_cond                                 2
% 19.02/2.90  fd_pseudo_cond                          11
% 19.02/2.90  AC symbols                              0
% 19.02/2.90  
% 19.02/2.90  ------ Input Options Time Limit: Unbounded
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing...
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 19.02/2.90  Current options:
% 19.02/2.90  ------ 
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing...
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.02/2.90  
% 19.02/2.90  ------ Proving...
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  % SZS status Theorem for theBenchmark.p
% 19.02/2.90  
% 19.02/2.90   Resolution empty clause
% 19.02/2.90  
% 19.02/2.90  % SZS output start CNFRefutation for theBenchmark.p
% 19.02/2.90  
% 19.02/2.90  fof(f12,axiom,(
% 19.02/2.90    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f18,plain,(
% 19.02/2.90    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 19.02/2.90    inference(ennf_transformation,[],[f12])).
% 19.02/2.90  
% 19.02/2.90  fof(f19,plain,(
% 19.02/2.90    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 19.02/2.90    inference(flattening,[],[f18])).
% 19.02/2.90  
% 19.02/2.90  fof(f43,plain,(
% 19.02/2.90    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 19.02/2.90    introduced(choice_axiom,[])).
% 19.02/2.90  
% 19.02/2.90  fof(f44,plain,(
% 19.02/2.90    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 19.02/2.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f43])).
% 19.02/2.90  
% 19.02/2.90  fof(f77,plain,(
% 19.02/2.90    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 19.02/2.90    inference(cnf_transformation,[],[f44])).
% 19.02/2.90  
% 19.02/2.90  fof(f5,axiom,(
% 19.02/2.90    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f34,plain,(
% 19.02/2.90    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 19.02/2.90    inference(nnf_transformation,[],[f5])).
% 19.02/2.90  
% 19.02/2.90  fof(f35,plain,(
% 19.02/2.90    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.02/2.90    inference(rectify,[],[f34])).
% 19.02/2.90  
% 19.02/2.90  fof(f36,plain,(
% 19.02/2.90    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 19.02/2.90    introduced(choice_axiom,[])).
% 19.02/2.90  
% 19.02/2.90  fof(f37,plain,(
% 19.02/2.90    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.02/2.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 19.02/2.90  
% 19.02/2.90  fof(f62,plain,(
% 19.02/2.90    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 19.02/2.90    inference(cnf_transformation,[],[f37])).
% 19.02/2.90  
% 19.02/2.90  fof(f6,axiom,(
% 19.02/2.90    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f66,plain,(
% 19.02/2.90    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 19.02/2.90    inference(cnf_transformation,[],[f6])).
% 19.02/2.90  
% 19.02/2.90  fof(f7,axiom,(
% 19.02/2.90    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f67,plain,(
% 19.02/2.90    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.02/2.90    inference(cnf_transformation,[],[f7])).
% 19.02/2.90  
% 19.02/2.90  fof(f8,axiom,(
% 19.02/2.90    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f68,plain,(
% 19.02/2.90    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.02/2.90    inference(cnf_transformation,[],[f8])).
% 19.02/2.90  
% 19.02/2.90  fof(f81,plain,(
% 19.02/2.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.02/2.90    inference(definition_unfolding,[],[f67,f68])).
% 19.02/2.90  
% 19.02/2.90  fof(f82,plain,(
% 19.02/2.90    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.02/2.90    inference(definition_unfolding,[],[f66,f81])).
% 19.02/2.90  
% 19.02/2.90  fof(f94,plain,(
% 19.02/2.90    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 19.02/2.90    inference(definition_unfolding,[],[f62,f82])).
% 19.02/2.90  
% 19.02/2.90  fof(f115,plain,(
% 19.02/2.90    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 19.02/2.90    inference(equality_resolution,[],[f94])).
% 19.02/2.90  
% 19.02/2.90  fof(f63,plain,(
% 19.02/2.90    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 19.02/2.90    inference(cnf_transformation,[],[f37])).
% 19.02/2.90  
% 19.02/2.90  fof(f93,plain,(
% 19.02/2.90    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 19.02/2.90    inference(definition_unfolding,[],[f63,f82])).
% 19.02/2.90  
% 19.02/2.90  fof(f113,plain,(
% 19.02/2.90    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 19.02/2.90    inference(equality_resolution,[],[f93])).
% 19.02/2.90  
% 19.02/2.90  fof(f114,plain,(
% 19.02/2.90    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 19.02/2.90    inference(equality_resolution,[],[f113])).
% 19.02/2.90  
% 19.02/2.90  fof(f2,axiom,(
% 19.02/2.90    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f26,plain,(
% 19.02/2.90    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.02/2.90    inference(nnf_transformation,[],[f2])).
% 19.02/2.90  
% 19.02/2.90  fof(f27,plain,(
% 19.02/2.90    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.02/2.90    inference(flattening,[],[f26])).
% 19.02/2.90  
% 19.02/2.90  fof(f49,plain,(
% 19.02/2.90    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.02/2.90    inference(cnf_transformation,[],[f27])).
% 19.02/2.90  
% 19.02/2.90  fof(f105,plain,(
% 19.02/2.90    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.02/2.90    inference(equality_resolution,[],[f49])).
% 19.02/2.90  
% 19.02/2.90  fof(f3,axiom,(
% 19.02/2.90    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f28,plain,(
% 19.02/2.90    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 19.02/2.90    inference(nnf_transformation,[],[f3])).
% 19.02/2.90  
% 19.02/2.90  fof(f53,plain,(
% 19.02/2.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 19.02/2.90    inference(cnf_transformation,[],[f28])).
% 19.02/2.90  
% 19.02/2.90  fof(f11,axiom,(
% 19.02/2.90    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f42,plain,(
% 19.02/2.90    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 19.02/2.90    inference(nnf_transformation,[],[f11])).
% 19.02/2.90  
% 19.02/2.90  fof(f75,plain,(
% 19.02/2.90    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 19.02/2.90    inference(cnf_transformation,[],[f42])).
% 19.02/2.90  
% 19.02/2.90  fof(f102,plain,(
% 19.02/2.90    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0) )),
% 19.02/2.90    inference(definition_unfolding,[],[f75,f82])).
% 19.02/2.90  
% 19.02/2.90  fof(f78,plain,(
% 19.02/2.90    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK3(X0,X1))) )),
% 19.02/2.90    inference(cnf_transformation,[],[f44])).
% 19.02/2.90  
% 19.02/2.90  fof(f51,plain,(
% 19.02/2.90    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.02/2.90    inference(cnf_transformation,[],[f27])).
% 19.02/2.90  
% 19.02/2.90  fof(f14,conjecture,(
% 19.02/2.90    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f15,negated_conjecture,(
% 19.02/2.90    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 19.02/2.90    inference(negated_conjecture,[],[f14])).
% 19.02/2.90  
% 19.02/2.90  fof(f22,plain,(
% 19.02/2.90    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 19.02/2.90    inference(ennf_transformation,[],[f15])).
% 19.02/2.90  
% 19.02/2.90  fof(f45,plain,(
% 19.02/2.90    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK4)) != sK4),
% 19.02/2.90    introduced(choice_axiom,[])).
% 19.02/2.90  
% 19.02/2.90  fof(f46,plain,(
% 19.02/2.90    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 19.02/2.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f45])).
% 19.02/2.90  
% 19.02/2.90  fof(f80,plain,(
% 19.02/2.90    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 19.02/2.90    inference(cnf_transformation,[],[f46])).
% 19.02/2.90  
% 19.02/2.90  fof(f103,plain,(
% 19.02/2.90    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4),
% 19.02/2.90    inference(definition_unfolding,[],[f80,f82])).
% 19.02/2.90  
% 19.02/2.90  fof(f13,axiom,(
% 19.02/2.90    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f20,plain,(
% 19.02/2.90    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 19.02/2.90    inference(ennf_transformation,[],[f13])).
% 19.02/2.90  
% 19.02/2.90  fof(f21,plain,(
% 19.02/2.90    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 19.02/2.90    inference(flattening,[],[f20])).
% 19.02/2.90  
% 19.02/2.90  fof(f79,plain,(
% 19.02/2.90    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 19.02/2.90    inference(cnf_transformation,[],[f21])).
% 19.02/2.90  
% 19.02/2.90  fof(f4,axiom,(
% 19.02/2.90    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 19.02/2.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.02/2.90  
% 19.02/2.90  fof(f17,plain,(
% 19.02/2.90    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 19.02/2.90    inference(ennf_transformation,[],[f4])).
% 19.02/2.90  
% 19.02/2.90  fof(f29,plain,(
% 19.02/2.90    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.02/2.90    inference(nnf_transformation,[],[f17])).
% 19.02/2.90  
% 19.02/2.90  fof(f30,plain,(
% 19.02/2.90    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.02/2.90    inference(flattening,[],[f29])).
% 19.02/2.90  
% 19.02/2.90  fof(f31,plain,(
% 19.02/2.90    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.02/2.90    inference(rectify,[],[f30])).
% 19.02/2.90  
% 19.02/2.90  fof(f32,plain,(
% 19.02/2.90    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 19.02/2.90    introduced(choice_axiom,[])).
% 19.02/2.90  
% 19.02/2.90  fof(f33,plain,(
% 19.02/2.90    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.02/2.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 19.02/2.90  
% 19.02/2.90  fof(f57,plain,(
% 19.02/2.90    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 19.02/2.90    inference(cnf_transformation,[],[f33])).
% 19.02/2.90  
% 19.02/2.90  fof(f87,plain,(
% 19.02/2.90    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 19.02/2.90    inference(definition_unfolding,[],[f57,f68])).
% 19.02/2.90  
% 19.02/2.90  fof(f106,plain,(
% 19.02/2.90    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 19.02/2.90    inference(equality_resolution,[],[f87])).
% 19.02/2.90  
% 19.02/2.90  fof(f107,plain,(
% 19.02/2.90    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 19.02/2.90    inference(equality_resolution,[],[f106])).
% 19.02/2.90  
% 19.02/2.90  cnf(c_28,plain,
% 19.02/2.90      ( r1_tarski(X0,k1_setfam_1(X1))
% 19.02/2.90      | r2_hidden(sK3(X1,X0),X1)
% 19.02/2.90      | k1_xboole_0 = X1 ),
% 19.02/2.90      inference(cnf_transformation,[],[f77]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_18,plain,
% 19.02/2.90      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 19.02/2.90      inference(cnf_transformation,[],[f115]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_55234,plain,
% 19.02/2.90      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 19.02/2.90      | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 19.02/2.90      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_28,c_18]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_54689,plain,
% 19.02/2.90      ( k1_xboole_0 = X0
% 19.02/2.90      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
% 19.02/2.90      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 19.02/2.90      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_54696,plain,
% 19.02/2.90      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 19.02/2.90      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_55544,plain,
% 19.02/2.90      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 19.02/2.90      | sK3(k2_enumset1(X0,X0,X0,X0),X1) = X0
% 19.02/2.90      | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 19.02/2.90      inference(superposition,[status(thm)],[c_54689,c_54696]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_17,plain,
% 19.02/2.90      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 19.02/2.90      inference(cnf_transformation,[],[f114]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_67,plain,
% 19.02/2.90      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 19.02/2.90      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f105]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_7030,plain,
% 19.02/2.90      ( r1_tarski(X0,X0) = iProver_top ),
% 19.02/2.90      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_5,plain,
% 19.02/2.90      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 19.02/2.90      inference(cnf_transformation,[],[f53]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_7029,plain,
% 19.02/2.90      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 19.02/2.90      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_7702,plain,
% 19.02/2.90      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.02/2.90      inference(superposition,[status(thm)],[c_7030,c_7029]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_26,plain,
% 19.02/2.90      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
% 19.02/2.90      inference(cnf_transformation,[],[f102]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_7014,plain,
% 19.02/2.90      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
% 19.02/2.90      | r2_hidden(X1,X0) != iProver_top ),
% 19.02/2.90      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_8094,plain,
% 19.02/2.90      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 19.02/2.90      | r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 19.02/2.90      inference(superposition,[status(thm)],[c_7702,c_7014]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_58520,plain,
% 19.02/2.90      ( sK3(k2_enumset1(X0,X0,X0,X0),X1) = X0
% 19.02/2.90      | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 19.02/2.90      inference(global_propositional_subsumption,
% 19.02/2.90                [status(thm)],
% 19.02/2.90                [c_55544,c_67,c_8094]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_58522,plain,
% 19.02/2.90      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 19.02/2.90      | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1 ),
% 19.02/2.90      inference(predicate_to_equality_rev,[status(thm)],[c_58520]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_58985,plain,
% 19.02/2.90      ( sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 19.02/2.90      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
% 19.02/2.90      inference(global_propositional_subsumption,
% 19.02/2.90                [status(thm)],
% 19.02/2.90                [c_55234,c_58522]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_58986,plain,
% 19.02/2.90      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 19.02/2.90      | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1 ),
% 19.02/2.90      inference(renaming,[status(thm)],[c_58985]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_532,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_531,plain,( X0 = X0 ),theory(equality) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_55711,plain,
% 19.02/2.90      ( X0 != X1 | X1 = X0 ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_532,c_531]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_59657,plain,
% 19.02/2.90      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 19.02/2.90      | X1 = sK3(k2_enumset1(X1,X1,X1,X1),X0) ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_58986,c_55711]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_534,plain,
% 19.02/2.90      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.02/2.90      theory(equality) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_56235,plain,
% 19.02/2.90      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_534,c_531]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_59702,plain,
% 19.02/2.90      ( r1_tarski(X0,X1)
% 19.02/2.90      | r1_tarski(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))
% 19.02/2.90      | ~ r1_tarski(sK3(k2_enumset1(X0,X0,X0,X0),X2),X1) ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_59657,c_56235]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_61768,plain,
% 19.02/2.90      ( r1_tarski(X0,sK3(k2_enumset1(X0,X0,X0,X0),X1))
% 19.02/2.90      | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_59702,c_4]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_27,plain,
% 19.02/2.90      ( ~ r1_tarski(X0,sK3(X1,X0))
% 19.02/2.90      | r1_tarski(X0,k1_setfam_1(X1))
% 19.02/2.90      | k1_xboole_0 = X1 ),
% 19.02/2.90      inference(cnf_transformation,[],[f78]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_63815,plain,
% 19.02/2.90      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))
% 19.02/2.90      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_61768,c_27]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_2,plain,
% 19.02/2.90      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.02/2.90      inference(cnf_transformation,[],[f51]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_30,negated_conjecture,
% 19.02/2.90      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 19.02/2.90      inference(cnf_transformation,[],[f103]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_54953,plain,
% 19.02/2.90      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 19.02/2.90      | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_2,c_30]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_3508,plain,
% 19.02/2.90      ( r1_tarski(sK4,sK4) ),
% 19.02/2.90      inference(instantiation,[status(thm)],[c_4]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_29,plain,
% 19.02/2.90      ( ~ r1_tarski(X0,X1)
% 19.02/2.90      | r1_tarski(k1_setfam_1(X2),X1)
% 19.02/2.90      | ~ r2_hidden(X0,X2) ),
% 19.02/2.90      inference(cnf_transformation,[],[f79]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_11,plain,
% 19.02/2.90      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 19.02/2.90      inference(cnf_transformation,[],[f107]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_7726,plain,
% 19.02/2.90      ( ~ r1_tarski(X0,X1)
% 19.02/2.90      | r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X3,X0)),X1) ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_29,c_11]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_7467,plain,
% 19.02/2.90      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 19.02/2.90      | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_2,c_30]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_8135,plain,
% 19.02/2.90      ( ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 19.02/2.90      | ~ r1_tarski(sK4,sK4) ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_7726,c_7467]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_54956,plain,
% 19.02/2.90      ( ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 19.02/2.90      inference(global_propositional_subsumption,
% 19.02/2.90                [status(thm)],
% 19.02/2.90                [c_54953,c_3508,c_8135]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_63884,plain,
% 19.02/2.90      ( k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_63815,c_54956]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_63933,plain,
% 19.02/2.90      ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_63884,c_55711]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_55709,plain,
% 19.02/2.90      ( ~ r1_tarski(X0,X1) | X2 != k1_xboole_0 | k4_xboole_0(X0,X1) = X2 ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_532,c_5]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_55909,plain,
% 19.02/2.90      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 19.02/2.90      | ~ r2_hidden(X1,X0)
% 19.02/2.90      | X0 != k1_xboole_0 ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_55709,c_26]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_56792,plain,
% 19.02/2.90      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 19.02/2.90      | k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 19.02/2.90      inference(resolution,[status(thm)],[c_55909,c_4]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_56800,plain,
% 19.02/2.90      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 19.02/2.90      inference(global_propositional_subsumption,
% 19.02/2.90                [status(thm)],
% 19.02/2.90                [c_56792,c_67,c_8094]) ).
% 19.02/2.90  
% 19.02/2.90  cnf(c_64088,plain,
% 19.02/2.90      ( $false ),
% 19.02/2.90      inference(forward_subsumption_resolution,[status(thm)],[c_63933,c_56800]) ).
% 19.02/2.90  
% 19.02/2.90  
% 19.02/2.90  % SZS output end CNFRefutation for theBenchmark.p
% 19.02/2.90  
% 19.02/2.90  ------                               Statistics
% 19.02/2.90  
% 19.02/2.90  ------ Selected
% 19.02/2.90  
% 19.02/2.90  total_time:                             1.997
% 19.02/2.90  
%------------------------------------------------------------------------------
