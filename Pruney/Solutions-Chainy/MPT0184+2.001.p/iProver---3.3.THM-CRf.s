%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:44 EST 2020

% Result     : Theorem 8.07s
% Output     : CNFRefutation 8.07s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 483 expanded)
%              Number of clauses        :   42 ( 107 expanded)
%              Number of leaves         :    7 ( 108 expanded)
%              Depth                    :   20
%              Number of atoms          :  299 (3277 expanded)
%              Number of equality atoms :  228 (2586 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f10,plain,(
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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f16,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f35,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f29])).

fof(f36,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f35])).

fof(f17,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f33,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f28])).

fof(f34,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f33])).

fof(f15,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f15,f22])).

fof(f37,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f30])).

fof(f38,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f37])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) = X2
      | sK0(X0,X1,X2,X3) = X1
      | sK0(X0,X1,X2,X3) = X0
      | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) = X2
      | sK0(X0,X1,X2,X3) = X1
      | sK0(X0,X1,X2,X3) = X0
      | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f14,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f14,f22])).

fof(f39,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X2,X1,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X2,X1,X0)
   => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK3,sK2,sK1) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK3,sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f12])).

fof(f23,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(sK3,sK3,sK2,sK1) ),
    inference(definition_unfolding,[],[f23,f22,f22])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f20,f22])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3767,plain,
    ( r2_hidden(sK2,k2_enumset1(sK3,sK3,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3764,plain,
    ( r2_hidden(sK1,k2_enumset1(sK3,sK3,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_430,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) = X2
    | sK0(X0,X1,X2,X3) = X1
    | sK0(X0,X1,X2,X3) = X0
    | k2_enumset1(X0,X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_433,plain,
    ( sK0(X0,X1,X2,X3) = X2
    | sK0(X0,X1,X2,X3) = X1
    | sK0(X0,X1,X2,X3) = X0
    | k2_enumset1(X0,X0,X1,X2) = X3
    | r2_hidden(sK0(X0,X1,X2,X3),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_429,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_879,plain,
    ( sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X2
    | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X1
    | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X0
    | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X3
    | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X4
    | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X5
    | k2_enumset1(X3,X3,X4,X5) = k2_enumset1(X0,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_433,c_429])).

cnf(c_8,negated_conjecture,
    ( k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(sK3,sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_932,plain,
    ( sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = X2
    | sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = X1
    | sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = X0
    | sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3
    | sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
    | sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1
    | k2_enumset1(X0,X0,X1,X2) != k2_enumset1(sK1,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_879,c_8])).

cnf(c_1108,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1 ),
    inference(equality_resolution,[status(thm)],[c_932])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) != X2
    | k2_enumset1(X0,X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_436,plain,
    ( sK0(X0,X1,X2,X3) != X2
    | k2_enumset1(X0,X0,X1,X2) = X3
    | r2_hidden(sK0(X0,X1,X2,X3),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1182,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1
    | k2_enumset1(sK3,sK3,sK2,sK1) = k2_enumset1(sK1,sK1,sK2,sK3)
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_436])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) != X0
    | k2_enumset1(X0,X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_447,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK1
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_448,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK1
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1)
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) != X1
    | k2_enumset1(X0,X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_446,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK2
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_450,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK2
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1)
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_445,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK3
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_452,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK3
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1)
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_469,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,X0,X1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = X0
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = X1
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_565,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,X0))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = X0
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2 ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_566,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = X0
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_568,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_2530,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1182,c_8,c_448,c_450,c_452,c_568])).

cnf(c_2535,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1
    | r2_hidden(sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_2530])).

cnf(c_3206,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_430,c_2535])).

cnf(c_3605,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1
    | r2_hidden(sK2,k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_2530])).

cnf(c_3621,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK3,sK3,sK2,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3605])).

cnf(c_2532,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2530])).

cnf(c_305,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1060,plain,
    ( k2_enumset1(sK3,sK3,sK2,sK1) = k2_enumset1(sK3,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_308,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_539,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != X0
    | k2_enumset1(sK3,sK3,sK2,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_702,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK2,sK1))
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != X0
    | k2_enumset1(sK3,sK3,sK2,sK1) != k2_enumset1(sK3,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_704,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
    | ~ r2_hidden(sK1,k2_enumset1(sK3,sK3,sK2,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK1
    | k2_enumset1(sK3,sK3,sK2,sK1) != k2_enumset1(sK3,sK3,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3767,c_3764,c_3621,c_2532,c_1060,c_704])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:32:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.07/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.07/1.48  
% 8.07/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.07/1.48  
% 8.07/1.48  ------  iProver source info
% 8.07/1.48  
% 8.07/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.07/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.07/1.48  git: non_committed_changes: false
% 8.07/1.48  git: last_make_outside_of_git: false
% 8.07/1.48  
% 8.07/1.48  ------ 
% 8.07/1.48  
% 8.07/1.48  ------ Input Options
% 8.07/1.48  
% 8.07/1.48  --out_options                           all
% 8.07/1.48  --tptp_safe_out                         true
% 8.07/1.48  --problem_path                          ""
% 8.07/1.48  --include_path                          ""
% 8.07/1.48  --clausifier                            res/vclausify_rel
% 8.07/1.48  --clausifier_options                    ""
% 8.07/1.48  --stdin                                 false
% 8.07/1.48  --stats_out                             all
% 8.07/1.48  
% 8.07/1.48  ------ General Options
% 8.07/1.48  
% 8.07/1.48  --fof                                   false
% 8.07/1.48  --time_out_real                         305.
% 8.07/1.48  --time_out_virtual                      -1.
% 8.07/1.48  --symbol_type_check                     false
% 8.07/1.48  --clausify_out                          false
% 8.07/1.48  --sig_cnt_out                           false
% 8.07/1.48  --trig_cnt_out                          false
% 8.07/1.48  --trig_cnt_out_tolerance                1.
% 8.07/1.48  --trig_cnt_out_sk_spl                   false
% 8.07/1.48  --abstr_cl_out                          false
% 8.07/1.48  
% 8.07/1.48  ------ Global Options
% 8.07/1.48  
% 8.07/1.48  --schedule                              default
% 8.07/1.48  --add_important_lit                     false
% 8.07/1.48  --prop_solver_per_cl                    1000
% 8.07/1.48  --min_unsat_core                        false
% 8.07/1.48  --soft_assumptions                      false
% 8.07/1.48  --soft_lemma_size                       3
% 8.07/1.48  --prop_impl_unit_size                   0
% 8.07/1.48  --prop_impl_unit                        []
% 8.07/1.48  --share_sel_clauses                     true
% 8.07/1.48  --reset_solvers                         false
% 8.07/1.48  --bc_imp_inh                            [conj_cone]
% 8.07/1.48  --conj_cone_tolerance                   3.
% 8.07/1.48  --extra_neg_conj                        none
% 8.07/1.48  --large_theory_mode                     true
% 8.07/1.48  --prolific_symb_bound                   200
% 8.07/1.48  --lt_threshold                          2000
% 8.07/1.48  --clause_weak_htbl                      true
% 8.07/1.48  --gc_record_bc_elim                     false
% 8.07/1.48  
% 8.07/1.48  ------ Preprocessing Options
% 8.07/1.48  
% 8.07/1.48  --preprocessing_flag                    true
% 8.07/1.48  --time_out_prep_mult                    0.1
% 8.07/1.48  --splitting_mode                        input
% 8.07/1.48  --splitting_grd                         true
% 8.07/1.48  --splitting_cvd                         false
% 8.07/1.48  --splitting_cvd_svl                     false
% 8.07/1.48  --splitting_nvd                         32
% 8.07/1.48  --sub_typing                            true
% 8.07/1.48  --prep_gs_sim                           true
% 8.07/1.48  --prep_unflatten                        true
% 8.07/1.48  --prep_res_sim                          true
% 8.07/1.48  --prep_upred                            true
% 8.07/1.48  --prep_sem_filter                       exhaustive
% 8.07/1.48  --prep_sem_filter_out                   false
% 8.07/1.48  --pred_elim                             true
% 8.07/1.48  --res_sim_input                         true
% 8.07/1.48  --eq_ax_congr_red                       true
% 8.07/1.48  --pure_diseq_elim                       true
% 8.07/1.48  --brand_transform                       false
% 8.07/1.48  --non_eq_to_eq                          false
% 8.07/1.48  --prep_def_merge                        true
% 8.07/1.48  --prep_def_merge_prop_impl              false
% 8.07/1.48  --prep_def_merge_mbd                    true
% 8.07/1.48  --prep_def_merge_tr_red                 false
% 8.07/1.48  --prep_def_merge_tr_cl                  false
% 8.07/1.48  --smt_preprocessing                     true
% 8.07/1.48  --smt_ac_axioms                         fast
% 8.07/1.48  --preprocessed_out                      false
% 8.07/1.48  --preprocessed_stats                    false
% 8.07/1.48  
% 8.07/1.48  ------ Abstraction refinement Options
% 8.07/1.48  
% 8.07/1.48  --abstr_ref                             []
% 8.07/1.48  --abstr_ref_prep                        false
% 8.07/1.48  --abstr_ref_until_sat                   false
% 8.07/1.48  --abstr_ref_sig_restrict                funpre
% 8.07/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.07/1.48  --abstr_ref_under                       []
% 8.07/1.48  
% 8.07/1.48  ------ SAT Options
% 8.07/1.48  
% 8.07/1.48  --sat_mode                              false
% 8.07/1.48  --sat_fm_restart_options                ""
% 8.07/1.48  --sat_gr_def                            false
% 8.07/1.48  --sat_epr_types                         true
% 8.07/1.48  --sat_non_cyclic_types                  false
% 8.07/1.48  --sat_finite_models                     false
% 8.07/1.48  --sat_fm_lemmas                         false
% 8.07/1.48  --sat_fm_prep                           false
% 8.07/1.48  --sat_fm_uc_incr                        true
% 8.07/1.48  --sat_out_model                         small
% 8.07/1.48  --sat_out_clauses                       false
% 8.07/1.48  
% 8.07/1.48  ------ QBF Options
% 8.07/1.48  
% 8.07/1.48  --qbf_mode                              false
% 8.07/1.48  --qbf_elim_univ                         false
% 8.07/1.48  --qbf_dom_inst                          none
% 8.07/1.48  --qbf_dom_pre_inst                      false
% 8.07/1.48  --qbf_sk_in                             false
% 8.07/1.48  --qbf_pred_elim                         true
% 8.07/1.48  --qbf_split                             512
% 8.07/1.48  
% 8.07/1.48  ------ BMC1 Options
% 8.07/1.48  
% 8.07/1.48  --bmc1_incremental                      false
% 8.07/1.48  --bmc1_axioms                           reachable_all
% 8.07/1.48  --bmc1_min_bound                        0
% 8.07/1.48  --bmc1_max_bound                        -1
% 8.07/1.48  --bmc1_max_bound_default                -1
% 8.07/1.48  --bmc1_symbol_reachability              true
% 8.07/1.48  --bmc1_property_lemmas                  false
% 8.07/1.48  --bmc1_k_induction                      false
% 8.07/1.48  --bmc1_non_equiv_states                 false
% 8.07/1.48  --bmc1_deadlock                         false
% 8.07/1.48  --bmc1_ucm                              false
% 8.07/1.48  --bmc1_add_unsat_core                   none
% 8.07/1.48  --bmc1_unsat_core_children              false
% 8.07/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.07/1.48  --bmc1_out_stat                         full
% 8.07/1.48  --bmc1_ground_init                      false
% 8.07/1.48  --bmc1_pre_inst_next_state              false
% 8.07/1.48  --bmc1_pre_inst_state                   false
% 8.07/1.48  --bmc1_pre_inst_reach_state             false
% 8.07/1.48  --bmc1_out_unsat_core                   false
% 8.07/1.48  --bmc1_aig_witness_out                  false
% 8.07/1.48  --bmc1_verbose                          false
% 8.07/1.48  --bmc1_dump_clauses_tptp                false
% 8.07/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.07/1.48  --bmc1_dump_file                        -
% 8.07/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.07/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.07/1.48  --bmc1_ucm_extend_mode                  1
% 8.07/1.48  --bmc1_ucm_init_mode                    2
% 8.07/1.48  --bmc1_ucm_cone_mode                    none
% 8.07/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.07/1.48  --bmc1_ucm_relax_model                  4
% 8.07/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.07/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.07/1.48  --bmc1_ucm_layered_model                none
% 8.07/1.48  --bmc1_ucm_max_lemma_size               10
% 8.07/1.48  
% 8.07/1.48  ------ AIG Options
% 8.07/1.48  
% 8.07/1.48  --aig_mode                              false
% 8.07/1.48  
% 8.07/1.48  ------ Instantiation Options
% 8.07/1.48  
% 8.07/1.48  --instantiation_flag                    true
% 8.07/1.48  --inst_sos_flag                         true
% 8.07/1.48  --inst_sos_phase                        true
% 8.07/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.07/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.07/1.48  --inst_lit_sel_side                     num_symb
% 8.07/1.48  --inst_solver_per_active                1400
% 8.07/1.48  --inst_solver_calls_frac                1.
% 8.07/1.48  --inst_passive_queue_type               priority_queues
% 8.07/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.07/1.48  --inst_passive_queues_freq              [25;2]
% 8.07/1.48  --inst_dismatching                      true
% 8.07/1.48  --inst_eager_unprocessed_to_passive     true
% 8.07/1.48  --inst_prop_sim_given                   true
% 8.07/1.48  --inst_prop_sim_new                     false
% 8.07/1.48  --inst_subs_new                         false
% 8.07/1.48  --inst_eq_res_simp                      false
% 8.07/1.48  --inst_subs_given                       false
% 8.07/1.48  --inst_orphan_elimination               true
% 8.07/1.48  --inst_learning_loop_flag               true
% 8.07/1.48  --inst_learning_start                   3000
% 8.07/1.48  --inst_learning_factor                  2
% 8.07/1.48  --inst_start_prop_sim_after_learn       3
% 8.07/1.48  --inst_sel_renew                        solver
% 8.07/1.48  --inst_lit_activity_flag                true
% 8.07/1.48  --inst_restr_to_given                   false
% 8.07/1.48  --inst_activity_threshold               500
% 8.07/1.48  --inst_out_proof                        true
% 8.07/1.48  
% 8.07/1.48  ------ Resolution Options
% 8.07/1.48  
% 8.07/1.48  --resolution_flag                       true
% 8.07/1.48  --res_lit_sel                           adaptive
% 8.07/1.48  --res_lit_sel_side                      none
% 8.07/1.48  --res_ordering                          kbo
% 8.07/1.48  --res_to_prop_solver                    active
% 8.07/1.48  --res_prop_simpl_new                    false
% 8.07/1.48  --res_prop_simpl_given                  true
% 8.07/1.48  --res_passive_queue_type                priority_queues
% 8.07/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.07/1.48  --res_passive_queues_freq               [15;5]
% 8.07/1.48  --res_forward_subs                      full
% 8.07/1.48  --res_backward_subs                     full
% 8.07/1.48  --res_forward_subs_resolution           true
% 8.07/1.48  --res_backward_subs_resolution          true
% 8.07/1.48  --res_orphan_elimination                true
% 8.07/1.48  --res_time_limit                        2.
% 8.07/1.48  --res_out_proof                         true
% 8.07/1.48  
% 8.07/1.48  ------ Superposition Options
% 8.07/1.48  
% 8.07/1.48  --superposition_flag                    true
% 8.07/1.48  --sup_passive_queue_type                priority_queues
% 8.07/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.07/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.07/1.48  --demod_completeness_check              fast
% 8.07/1.48  --demod_use_ground                      true
% 8.07/1.48  --sup_to_prop_solver                    passive
% 8.07/1.48  --sup_prop_simpl_new                    true
% 8.07/1.48  --sup_prop_simpl_given                  true
% 8.07/1.48  --sup_fun_splitting                     true
% 8.07/1.48  --sup_smt_interval                      50000
% 8.07/1.48  
% 8.07/1.48  ------ Superposition Simplification Setup
% 8.07/1.48  
% 8.07/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.07/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.07/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.07/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.07/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.07/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.07/1.48  --sup_immed_triv                        [TrivRules]
% 8.07/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.07/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.07/1.48  --sup_immed_bw_main                     []
% 8.07/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.07/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.07/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.07/1.48  --sup_input_bw                          []
% 8.07/1.48  
% 8.07/1.48  ------ Combination Options
% 8.07/1.48  
% 8.07/1.48  --comb_res_mult                         3
% 8.07/1.48  --comb_sup_mult                         2
% 8.07/1.48  --comb_inst_mult                        10
% 8.07/1.48  
% 8.07/1.48  ------ Debug Options
% 8.07/1.48  
% 8.07/1.48  --dbg_backtrace                         false
% 8.07/1.48  --dbg_dump_prop_clauses                 false
% 8.07/1.48  --dbg_dump_prop_clauses_file            -
% 8.07/1.48  --dbg_out_stat                          false
% 8.07/1.48  ------ Parsing...
% 8.07/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.07/1.48  
% 8.07/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.07/1.48  
% 8.07/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.07/1.48  
% 8.07/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.07/1.48  ------ Proving...
% 8.07/1.48  ------ Problem Properties 
% 8.07/1.48  
% 8.07/1.48  
% 8.07/1.48  clauses                                 9
% 8.07/1.48  conjectures                             1
% 8.07/1.48  EPR                                     0
% 8.07/1.48  Horn                                    7
% 8.07/1.48  unary                                   4
% 8.07/1.48  binary                                  0
% 8.07/1.48  lits                                    22
% 8.07/1.48  lits eq                                 14
% 8.07/1.48  fd_pure                                 0
% 8.07/1.48  fd_pseudo                               0
% 8.07/1.48  fd_cond                                 0
% 8.07/1.48  fd_pseudo_cond                          4
% 8.07/1.48  AC symbols                              0
% 8.07/1.48  
% 8.07/1.48  ------ Schedule dynamic 5 is on 
% 8.07/1.48  
% 8.07/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.07/1.48  
% 8.07/1.48  
% 8.07/1.48  ------ 
% 8.07/1.48  Current options:
% 8.07/1.48  ------ 
% 8.07/1.48  
% 8.07/1.48  ------ Input Options
% 8.07/1.48  
% 8.07/1.48  --out_options                           all
% 8.07/1.48  --tptp_safe_out                         true
% 8.07/1.48  --problem_path                          ""
% 8.07/1.48  --include_path                          ""
% 8.07/1.48  --clausifier                            res/vclausify_rel
% 8.07/1.48  --clausifier_options                    ""
% 8.07/1.48  --stdin                                 false
% 8.07/1.48  --stats_out                             all
% 8.07/1.48  
% 8.07/1.48  ------ General Options
% 8.07/1.48  
% 8.07/1.48  --fof                                   false
% 8.07/1.48  --time_out_real                         305.
% 8.07/1.48  --time_out_virtual                      -1.
% 8.07/1.48  --symbol_type_check                     false
% 8.07/1.48  --clausify_out                          false
% 8.07/1.48  --sig_cnt_out                           false
% 8.07/1.48  --trig_cnt_out                          false
% 8.07/1.48  --trig_cnt_out_tolerance                1.
% 8.07/1.48  --trig_cnt_out_sk_spl                   false
% 8.07/1.48  --abstr_cl_out                          false
% 8.07/1.48  
% 8.07/1.48  ------ Global Options
% 8.07/1.48  
% 8.07/1.48  --schedule                              default
% 8.07/1.48  --add_important_lit                     false
% 8.07/1.48  --prop_solver_per_cl                    1000
% 8.07/1.48  --min_unsat_core                        false
% 8.07/1.48  --soft_assumptions                      false
% 8.07/1.48  --soft_lemma_size                       3
% 8.07/1.48  --prop_impl_unit_size                   0
% 8.07/1.48  --prop_impl_unit                        []
% 8.07/1.48  --share_sel_clauses                     true
% 8.07/1.48  --reset_solvers                         false
% 8.07/1.48  --bc_imp_inh                            [conj_cone]
% 8.07/1.48  --conj_cone_tolerance                   3.
% 8.07/1.48  --extra_neg_conj                        none
% 8.07/1.48  --large_theory_mode                     true
% 8.07/1.48  --prolific_symb_bound                   200
% 8.07/1.48  --lt_threshold                          2000
% 8.07/1.48  --clause_weak_htbl                      true
% 8.07/1.48  --gc_record_bc_elim                     false
% 8.07/1.48  
% 8.07/1.48  ------ Preprocessing Options
% 8.07/1.48  
% 8.07/1.48  --preprocessing_flag                    true
% 8.07/1.48  --time_out_prep_mult                    0.1
% 8.07/1.48  --splitting_mode                        input
% 8.07/1.48  --splitting_grd                         true
% 8.07/1.48  --splitting_cvd                         false
% 8.07/1.48  --splitting_cvd_svl                     false
% 8.07/1.48  --splitting_nvd                         32
% 8.07/1.48  --sub_typing                            true
% 8.07/1.48  --prep_gs_sim                           true
% 8.07/1.48  --prep_unflatten                        true
% 8.07/1.48  --prep_res_sim                          true
% 8.07/1.48  --prep_upred                            true
% 8.07/1.48  --prep_sem_filter                       exhaustive
% 8.07/1.48  --prep_sem_filter_out                   false
% 8.07/1.48  --pred_elim                             true
% 8.07/1.48  --res_sim_input                         true
% 8.07/1.48  --eq_ax_congr_red                       true
% 8.07/1.48  --pure_diseq_elim                       true
% 8.07/1.48  --brand_transform                       false
% 8.07/1.48  --non_eq_to_eq                          false
% 8.07/1.48  --prep_def_merge                        true
% 8.07/1.48  --prep_def_merge_prop_impl              false
% 8.07/1.48  --prep_def_merge_mbd                    true
% 8.07/1.48  --prep_def_merge_tr_red                 false
% 8.07/1.48  --prep_def_merge_tr_cl                  false
% 8.07/1.48  --smt_preprocessing                     true
% 8.07/1.48  --smt_ac_axioms                         fast
% 8.07/1.48  --preprocessed_out                      false
% 8.07/1.48  --preprocessed_stats                    false
% 8.07/1.48  
% 8.07/1.48  ------ Abstraction refinement Options
% 8.07/1.48  
% 8.07/1.48  --abstr_ref                             []
% 8.07/1.48  --abstr_ref_prep                        false
% 8.07/1.48  --abstr_ref_until_sat                   false
% 8.07/1.48  --abstr_ref_sig_restrict                funpre
% 8.07/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.07/1.48  --abstr_ref_under                       []
% 8.07/1.48  
% 8.07/1.48  ------ SAT Options
% 8.07/1.48  
% 8.07/1.48  --sat_mode                              false
% 8.07/1.48  --sat_fm_restart_options                ""
% 8.07/1.48  --sat_gr_def                            false
% 8.07/1.48  --sat_epr_types                         true
% 8.07/1.48  --sat_non_cyclic_types                  false
% 8.07/1.48  --sat_finite_models                     false
% 8.07/1.48  --sat_fm_lemmas                         false
% 8.07/1.48  --sat_fm_prep                           false
% 8.07/1.48  --sat_fm_uc_incr                        true
% 8.07/1.48  --sat_out_model                         small
% 8.07/1.48  --sat_out_clauses                       false
% 8.07/1.48  
% 8.07/1.48  ------ QBF Options
% 8.07/1.48  
% 8.07/1.48  --qbf_mode                              false
% 8.07/1.48  --qbf_elim_univ                         false
% 8.07/1.48  --qbf_dom_inst                          none
% 8.07/1.48  --qbf_dom_pre_inst                      false
% 8.07/1.48  --qbf_sk_in                             false
% 8.07/1.48  --qbf_pred_elim                         true
% 8.07/1.48  --qbf_split                             512
% 8.07/1.48  
% 8.07/1.48  ------ BMC1 Options
% 8.07/1.48  
% 8.07/1.48  --bmc1_incremental                      false
% 8.07/1.48  --bmc1_axioms                           reachable_all
% 8.07/1.48  --bmc1_min_bound                        0
% 8.07/1.48  --bmc1_max_bound                        -1
% 8.07/1.48  --bmc1_max_bound_default                -1
% 8.07/1.48  --bmc1_symbol_reachability              true
% 8.07/1.48  --bmc1_property_lemmas                  false
% 8.07/1.48  --bmc1_k_induction                      false
% 8.07/1.48  --bmc1_non_equiv_states                 false
% 8.07/1.48  --bmc1_deadlock                         false
% 8.07/1.48  --bmc1_ucm                              false
% 8.07/1.48  --bmc1_add_unsat_core                   none
% 8.07/1.48  --bmc1_unsat_core_children              false
% 8.07/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.07/1.48  --bmc1_out_stat                         full
% 8.07/1.48  --bmc1_ground_init                      false
% 8.07/1.48  --bmc1_pre_inst_next_state              false
% 8.07/1.48  --bmc1_pre_inst_state                   false
% 8.07/1.48  --bmc1_pre_inst_reach_state             false
% 8.07/1.48  --bmc1_out_unsat_core                   false
% 8.07/1.48  --bmc1_aig_witness_out                  false
% 8.07/1.48  --bmc1_verbose                          false
% 8.07/1.48  --bmc1_dump_clauses_tptp                false
% 8.07/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.07/1.48  --bmc1_dump_file                        -
% 8.07/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.07/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.07/1.48  --bmc1_ucm_extend_mode                  1
% 8.07/1.48  --bmc1_ucm_init_mode                    2
% 8.07/1.48  --bmc1_ucm_cone_mode                    none
% 8.07/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.07/1.48  --bmc1_ucm_relax_model                  4
% 8.07/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.07/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.07/1.48  --bmc1_ucm_layered_model                none
% 8.07/1.48  --bmc1_ucm_max_lemma_size               10
% 8.07/1.48  
% 8.07/1.48  ------ AIG Options
% 8.07/1.48  
% 8.07/1.48  --aig_mode                              false
% 8.07/1.48  
% 8.07/1.48  ------ Instantiation Options
% 8.07/1.48  
% 8.07/1.48  --instantiation_flag                    true
% 8.07/1.48  --inst_sos_flag                         true
% 8.07/1.48  --inst_sos_phase                        true
% 8.07/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.07/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.07/1.48  --inst_lit_sel_side                     none
% 8.07/1.48  --inst_solver_per_active                1400
% 8.07/1.48  --inst_solver_calls_frac                1.
% 8.07/1.48  --inst_passive_queue_type               priority_queues
% 8.07/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.07/1.48  --inst_passive_queues_freq              [25;2]
% 8.07/1.48  --inst_dismatching                      true
% 8.07/1.48  --inst_eager_unprocessed_to_passive     true
% 8.07/1.48  --inst_prop_sim_given                   true
% 8.07/1.48  --inst_prop_sim_new                     false
% 8.07/1.48  --inst_subs_new                         false
% 8.07/1.48  --inst_eq_res_simp                      false
% 8.07/1.48  --inst_subs_given                       false
% 8.07/1.48  --inst_orphan_elimination               true
% 8.07/1.48  --inst_learning_loop_flag               true
% 8.07/1.48  --inst_learning_start                   3000
% 8.07/1.48  --inst_learning_factor                  2
% 8.07/1.48  --inst_start_prop_sim_after_learn       3
% 8.07/1.48  --inst_sel_renew                        solver
% 8.07/1.48  --inst_lit_activity_flag                true
% 8.07/1.48  --inst_restr_to_given                   false
% 8.07/1.48  --inst_activity_threshold               500
% 8.07/1.48  --inst_out_proof                        true
% 8.07/1.48  
% 8.07/1.48  ------ Resolution Options
% 8.07/1.48  
% 8.07/1.48  --resolution_flag                       false
% 8.07/1.48  --res_lit_sel                           adaptive
% 8.07/1.48  --res_lit_sel_side                      none
% 8.07/1.48  --res_ordering                          kbo
% 8.07/1.48  --res_to_prop_solver                    active
% 8.07/1.48  --res_prop_simpl_new                    false
% 8.07/1.48  --res_prop_simpl_given                  true
% 8.07/1.48  --res_passive_queue_type                priority_queues
% 8.07/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.07/1.48  --res_passive_queues_freq               [15;5]
% 8.07/1.48  --res_forward_subs                      full
% 8.07/1.48  --res_backward_subs                     full
% 8.07/1.48  --res_forward_subs_resolution           true
% 8.07/1.48  --res_backward_subs_resolution          true
% 8.07/1.48  --res_orphan_elimination                true
% 8.07/1.48  --res_time_limit                        2.
% 8.07/1.48  --res_out_proof                         true
% 8.07/1.48  
% 8.07/1.48  ------ Superposition Options
% 8.07/1.48  
% 8.07/1.48  --superposition_flag                    true
% 8.07/1.48  --sup_passive_queue_type                priority_queues
% 8.07/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.07/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.07/1.48  --demod_completeness_check              fast
% 8.07/1.48  --demod_use_ground                      true
% 8.07/1.48  --sup_to_prop_solver                    passive
% 8.07/1.48  --sup_prop_simpl_new                    true
% 8.07/1.48  --sup_prop_simpl_given                  true
% 8.07/1.49  --sup_fun_splitting                     true
% 8.07/1.49  --sup_smt_interval                      50000
% 8.07/1.49  
% 8.07/1.49  ------ Superposition Simplification Setup
% 8.07/1.49  
% 8.07/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.07/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.07/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.07/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.07/1.49  --sup_immed_triv                        [TrivRules]
% 8.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.07/1.49  --sup_immed_bw_main                     []
% 8.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.07/1.49  --sup_input_bw                          []
% 8.07/1.49  
% 8.07/1.49  ------ Combination Options
% 8.07/1.49  
% 8.07/1.49  --comb_res_mult                         3
% 8.07/1.49  --comb_sup_mult                         2
% 8.07/1.49  --comb_inst_mult                        10
% 8.07/1.49  
% 8.07/1.49  ------ Debug Options
% 8.07/1.49  
% 8.07/1.49  --dbg_backtrace                         false
% 8.07/1.49  --dbg_dump_prop_clauses                 false
% 8.07/1.49  --dbg_dump_prop_clauses_file            -
% 8.07/1.49  --dbg_out_stat                          false
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  ------ Proving...
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  % SZS status Theorem for theBenchmark.p
% 8.07/1.49  
% 8.07/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.07/1.49  
% 8.07/1.49  fof(f1,axiom,(
% 8.07/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 8.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f5,plain,(
% 8.07/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 8.07/1.49    inference(ennf_transformation,[],[f1])).
% 8.07/1.49  
% 8.07/1.49  fof(f7,plain,(
% 8.07/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.07/1.49    inference(nnf_transformation,[],[f5])).
% 8.07/1.49  
% 8.07/1.49  fof(f8,plain,(
% 8.07/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.07/1.49    inference(flattening,[],[f7])).
% 8.07/1.49  
% 8.07/1.49  fof(f9,plain,(
% 8.07/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.07/1.49    inference(rectify,[],[f8])).
% 8.07/1.49  
% 8.07/1.49  fof(f10,plain,(
% 8.07/1.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 8.07/1.49    introduced(choice_axiom,[])).
% 8.07/1.49  
% 8.07/1.49  fof(f11,plain,(
% 8.07/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 8.07/1.49  
% 8.07/1.49  fof(f16,plain,(
% 8.07/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 8.07/1.49    inference(cnf_transformation,[],[f11])).
% 8.07/1.49  
% 8.07/1.49  fof(f2,axiom,(
% 8.07/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f22,plain,(
% 8.07/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.07/1.49    inference(cnf_transformation,[],[f2])).
% 8.07/1.49  
% 8.07/1.49  fof(f29,plain,(
% 8.07/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 8.07/1.49    inference(definition_unfolding,[],[f16,f22])).
% 8.07/1.49  
% 8.07/1.49  fof(f35,plain,(
% 8.07/1.49    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 8.07/1.49    inference(equality_resolution,[],[f29])).
% 8.07/1.49  
% 8.07/1.49  fof(f36,plain,(
% 8.07/1.49    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 8.07/1.49    inference(equality_resolution,[],[f35])).
% 8.07/1.49  
% 8.07/1.49  fof(f17,plain,(
% 8.07/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 8.07/1.49    inference(cnf_transformation,[],[f11])).
% 8.07/1.49  
% 8.07/1.49  fof(f28,plain,(
% 8.07/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 8.07/1.49    inference(definition_unfolding,[],[f17,f22])).
% 8.07/1.49  
% 8.07/1.49  fof(f33,plain,(
% 8.07/1.49    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 8.07/1.49    inference(equality_resolution,[],[f28])).
% 8.07/1.49  
% 8.07/1.49  fof(f34,plain,(
% 8.07/1.49    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 8.07/1.49    inference(equality_resolution,[],[f33])).
% 8.07/1.49  
% 8.07/1.49  fof(f15,plain,(
% 8.07/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 8.07/1.49    inference(cnf_transformation,[],[f11])).
% 8.07/1.49  
% 8.07/1.49  fof(f30,plain,(
% 8.07/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 8.07/1.49    inference(definition_unfolding,[],[f15,f22])).
% 8.07/1.49  
% 8.07/1.49  fof(f37,plain,(
% 8.07/1.49    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 8.07/1.49    inference(equality_resolution,[],[f30])).
% 8.07/1.49  
% 8.07/1.49  fof(f38,plain,(
% 8.07/1.49    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 8.07/1.49    inference(equality_resolution,[],[f37])).
% 8.07/1.49  
% 8.07/1.49  fof(f18,plain,(
% 8.07/1.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 8.07/1.49    inference(cnf_transformation,[],[f11])).
% 8.07/1.49  
% 8.07/1.49  fof(f27,plain,(
% 8.07/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 8.07/1.49    inference(definition_unfolding,[],[f18,f22])).
% 8.07/1.49  
% 8.07/1.49  fof(f14,plain,(
% 8.07/1.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 8.07/1.49    inference(cnf_transformation,[],[f11])).
% 8.07/1.49  
% 8.07/1.49  fof(f31,plain,(
% 8.07/1.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 8.07/1.49    inference(definition_unfolding,[],[f14,f22])).
% 8.07/1.49  
% 8.07/1.49  fof(f39,plain,(
% 8.07/1.49    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 8.07/1.49    inference(equality_resolution,[],[f31])).
% 8.07/1.49  
% 8.07/1.49  fof(f3,conjecture,(
% 8.07/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 8.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f4,negated_conjecture,(
% 8.07/1.49    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 8.07/1.49    inference(negated_conjecture,[],[f3])).
% 8.07/1.49  
% 8.07/1.49  fof(f6,plain,(
% 8.07/1.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X2,X1,X0)),
% 8.07/1.49    inference(ennf_transformation,[],[f4])).
% 8.07/1.49  
% 8.07/1.49  fof(f12,plain,(
% 8.07/1.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X2,X1,X0) => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK3,sK2,sK1)),
% 8.07/1.49    introduced(choice_axiom,[])).
% 8.07/1.49  
% 8.07/1.49  fof(f13,plain,(
% 8.07/1.49    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK3,sK2,sK1)),
% 8.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f12])).
% 8.07/1.49  
% 8.07/1.49  fof(f23,plain,(
% 8.07/1.49    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK3,sK2,sK1)),
% 8.07/1.49    inference(cnf_transformation,[],[f13])).
% 8.07/1.49  
% 8.07/1.49  fof(f32,plain,(
% 8.07/1.49    k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(sK3,sK3,sK2,sK1)),
% 8.07/1.49    inference(definition_unfolding,[],[f23,f22,f22])).
% 8.07/1.49  
% 8.07/1.49  fof(f21,plain,(
% 8.07/1.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X2 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 8.07/1.49    inference(cnf_transformation,[],[f11])).
% 8.07/1.49  
% 8.07/1.49  fof(f24,plain,(
% 8.07/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X2 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 8.07/1.49    inference(definition_unfolding,[],[f21,f22])).
% 8.07/1.49  
% 8.07/1.49  fof(f19,plain,(
% 8.07/1.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X0 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 8.07/1.49    inference(cnf_transformation,[],[f11])).
% 8.07/1.49  
% 8.07/1.49  fof(f26,plain,(
% 8.07/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X0 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 8.07/1.49    inference(definition_unfolding,[],[f19,f22])).
% 8.07/1.49  
% 8.07/1.49  fof(f20,plain,(
% 8.07/1.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X1 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 8.07/1.49    inference(cnf_transformation,[],[f11])).
% 8.07/1.49  
% 8.07/1.49  fof(f25,plain,(
% 8.07/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X1 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 8.07/1.49    inference(definition_unfolding,[],[f20,f22])).
% 8.07/1.49  
% 8.07/1.49  cnf(c_5,plain,
% 8.07/1.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 8.07/1.49      inference(cnf_transformation,[],[f36]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_3767,plain,
% 8.07/1.49      ( r2_hidden(sK2,k2_enumset1(sK3,sK3,sK2,sK1)) ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_4,plain,
% 8.07/1.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 8.07/1.49      inference(cnf_transformation,[],[f34]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_3764,plain,
% 8.07/1.49      ( r2_hidden(sK1,k2_enumset1(sK3,sK3,sK2,sK1)) ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_6,plain,
% 8.07/1.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 8.07/1.49      inference(cnf_transformation,[],[f38]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_430,plain,
% 8.07/1.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_3,plain,
% 8.07/1.49      ( r2_hidden(sK0(X0,X1,X2,X3),X3)
% 8.07/1.49      | sK0(X0,X1,X2,X3) = X2
% 8.07/1.49      | sK0(X0,X1,X2,X3) = X1
% 8.07/1.49      | sK0(X0,X1,X2,X3) = X0
% 8.07/1.49      | k2_enumset1(X0,X0,X1,X2) = X3 ),
% 8.07/1.49      inference(cnf_transformation,[],[f27]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_433,plain,
% 8.07/1.49      ( sK0(X0,X1,X2,X3) = X2
% 8.07/1.49      | sK0(X0,X1,X2,X3) = X1
% 8.07/1.49      | sK0(X0,X1,X2,X3) = X0
% 8.07/1.49      | k2_enumset1(X0,X0,X1,X2) = X3
% 8.07/1.49      | r2_hidden(sK0(X0,X1,X2,X3),X3) = iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_7,plain,
% 8.07/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 8.07/1.49      | X0 = X1
% 8.07/1.49      | X0 = X2
% 8.07/1.49      | X0 = X3 ),
% 8.07/1.49      inference(cnf_transformation,[],[f39]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_429,plain,
% 8.07/1.49      ( X0 = X1
% 8.07/1.49      | X0 = X2
% 8.07/1.49      | X0 = X3
% 8.07/1.49      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_879,plain,
% 8.07/1.49      ( sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X2
% 8.07/1.49      | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X1
% 8.07/1.49      | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X0
% 8.07/1.49      | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X3
% 8.07/1.49      | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X4
% 8.07/1.49      | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X5
% 8.07/1.49      | k2_enumset1(X3,X3,X4,X5) = k2_enumset1(X0,X0,X1,X2) ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_433,c_429]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_8,negated_conjecture,
% 8.07/1.49      ( k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(sK3,sK3,sK2,sK1) ),
% 8.07/1.49      inference(cnf_transformation,[],[f32]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_932,plain,
% 8.07/1.49      ( sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = X2
% 8.07/1.49      | sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = X1
% 8.07/1.49      | sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = X0
% 8.07/1.49      | sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3
% 8.07/1.49      | sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
% 8.07/1.49      | sK0(X0,X1,X2,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1
% 8.07/1.49      | k2_enumset1(X0,X0,X1,X2) != k2_enumset1(sK1,sK1,sK2,sK3) ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_879,c_8]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1108,plain,
% 8.07/1.49      ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1 ),
% 8.07/1.49      inference(equality_resolution,[status(thm)],[c_932]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_0,plain,
% 8.07/1.49      ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
% 8.07/1.49      | sK0(X0,X1,X2,X3) != X2
% 8.07/1.49      | k2_enumset1(X0,X0,X1,X2) = X3 ),
% 8.07/1.49      inference(cnf_transformation,[],[f24]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_436,plain,
% 8.07/1.49      ( sK0(X0,X1,X2,X3) != X2
% 8.07/1.49      | k2_enumset1(X0,X0,X1,X2) = X3
% 8.07/1.49      | r2_hidden(sK0(X0,X1,X2,X3),X3) != iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1182,plain,
% 8.07/1.49      ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1
% 8.07/1.49      | k2_enumset1(sK3,sK3,sK2,sK1) = k2_enumset1(sK1,sK1,sK2,sK3)
% 8.07/1.49      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_1108,c_436]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_2,plain,
% 8.07/1.49      ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
% 8.07/1.49      | sK0(X0,X1,X2,X3) != X0
% 8.07/1.49      | k2_enumset1(X0,X0,X1,X2) = X3 ),
% 8.07/1.49      inference(cnf_transformation,[],[f26]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_447,plain,
% 8.07/1.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK1
% 8.07/1.49      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1) ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_448,plain,
% 8.07/1.49      ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK1
% 8.07/1.49      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1)
% 8.07/1.49      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1,plain,
% 8.07/1.49      ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
% 8.07/1.49      | sK0(X0,X1,X2,X3) != X1
% 8.07/1.49      | k2_enumset1(X0,X0,X1,X2) = X3 ),
% 8.07/1.49      inference(cnf_transformation,[],[f25]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_446,plain,
% 8.07/1.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK2
% 8.07/1.49      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1) ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_450,plain,
% 8.07/1.49      ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK2
% 8.07/1.49      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1)
% 8.07/1.49      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_445,plain,
% 8.07/1.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK3
% 8.07/1.49      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1) ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_452,plain,
% 8.07/1.49      ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK3
% 8.07/1.49      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK3,sK3,sK2,sK1)
% 8.07/1.49      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_469,plain,
% 8.07/1.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,X0,X1))
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = X0
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = X1
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3 ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_565,plain,
% 8.07/1.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,X0))
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = X0
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2 ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_469]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_566,plain,
% 8.07/1.49      ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = X0
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
% 8.07/1.49      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,X0)) != iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_568,plain,
% 8.07/1.49      ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK3
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1
% 8.07/1.49      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_566]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_2530,plain,
% 8.07/1.49      ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
% 8.07/1.49      inference(global_propositional_subsumption,
% 8.07/1.49                [status(thm)],
% 8.07/1.49                [c_1182,c_8,c_448,c_450,c_452,c_568]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_2535,plain,
% 8.07/1.49      ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1
% 8.07/1.49      | r2_hidden(sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_1108,c_2530]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_3206,plain,
% 8.07/1.49      ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK2
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1 ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_430,c_2535]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_3605,plain,
% 8.07/1.49      ( sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1
% 8.07/1.49      | r2_hidden(sK2,k2_enumset1(sK3,sK3,sK2,sK1)) != iProver_top ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_3206,c_2530]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_3621,plain,
% 8.07/1.49      ( ~ r2_hidden(sK2,k2_enumset1(sK3,sK3,sK2,sK1))
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) = sK1 ),
% 8.07/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3605]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_2532,plain,
% 8.07/1.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1)) ),
% 8.07/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2530]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_305,plain,( X0 = X0 ),theory(equality) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1060,plain,
% 8.07/1.49      ( k2_enumset1(sK3,sK3,sK2,sK1) = k2_enumset1(sK3,sK3,sK2,sK1) ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_305]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_308,plain,
% 8.07/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.07/1.49      theory(equality) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_539,plain,
% 8.07/1.49      ( ~ r2_hidden(X0,X1)
% 8.07/1.49      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != X0
% 8.07/1.49      | k2_enumset1(sK3,sK3,sK2,sK1) != X1 ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_308]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_702,plain,
% 8.07/1.49      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK2,sK1))
% 8.07/1.49      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != X0
% 8.07/1.49      | k2_enumset1(sK3,sK3,sK2,sK1) != k2_enumset1(sK3,sK3,sK2,sK1) ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_539]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_704,plain,
% 8.07/1.49      ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)),k2_enumset1(sK3,sK3,sK2,sK1))
% 8.07/1.49      | ~ r2_hidden(sK1,k2_enumset1(sK3,sK3,sK2,sK1))
% 8.07/1.49      | sK0(sK1,sK2,sK3,k2_enumset1(sK3,sK3,sK2,sK1)) != sK1
% 8.07/1.49      | k2_enumset1(sK3,sK3,sK2,sK1) != k2_enumset1(sK3,sK3,sK2,sK1) ),
% 8.07/1.49      inference(instantiation,[status(thm)],[c_702]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(contradiction,plain,
% 8.07/1.49      ( $false ),
% 8.07/1.49      inference(minisat,
% 8.07/1.49                [status(thm)],
% 8.07/1.49                [c_3767,c_3764,c_3621,c_2532,c_1060,c_704]) ).
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.07/1.49  
% 8.07/1.49  ------                               Statistics
% 8.07/1.49  
% 8.07/1.49  ------ General
% 8.07/1.49  
% 8.07/1.49  abstr_ref_over_cycles:                  0
% 8.07/1.49  abstr_ref_under_cycles:                 0
% 8.07/1.49  gc_basic_clause_elim:                   0
% 8.07/1.49  forced_gc_time:                         0
% 8.07/1.49  parsing_time:                           0.007
% 8.07/1.49  unif_index_cands_time:                  0.
% 8.07/1.49  unif_index_add_time:                    0.
% 8.07/1.49  orderings_time:                         0.
% 8.07/1.49  out_proof_time:                         0.008
% 8.07/1.49  total_time:                             0.935
% 8.07/1.49  num_of_symbols:                         34
% 8.07/1.49  num_of_terms:                           7906
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing
% 8.07/1.49  
% 8.07/1.49  num_of_splits:                          0
% 8.07/1.49  num_of_split_atoms:                     0
% 8.07/1.49  num_of_reused_defs:                     0
% 8.07/1.49  num_eq_ax_congr_red:                    8
% 8.07/1.49  num_of_sem_filtered_clauses:            1
% 8.07/1.49  num_of_subtypes:                        0
% 8.07/1.49  monotx_restored_types:                  0
% 8.07/1.49  sat_num_of_epr_types:                   0
% 8.07/1.49  sat_num_of_non_cyclic_types:            0
% 8.07/1.49  sat_guarded_non_collapsed_types:        0
% 8.07/1.49  num_pure_diseq_elim:                    0
% 8.07/1.49  simp_replaced_by:                       0
% 8.07/1.49  res_preprocessed:                       36
% 8.07/1.49  prep_upred:                             0
% 8.07/1.49  prep_unflattend:                        14
% 8.07/1.49  smt_new_axioms:                         0
% 8.07/1.49  pred_elim_cands:                        1
% 8.07/1.49  pred_elim:                              0
% 8.07/1.49  pred_elim_cl:                           0
% 8.07/1.49  pred_elim_cycles:                       1
% 8.07/1.49  merged_defs:                            0
% 8.07/1.49  merged_defs_ncl:                        0
% 8.07/1.49  bin_hyper_res:                          0
% 8.07/1.49  prep_cycles:                            3
% 8.07/1.49  pred_elim_time:                         0.003
% 8.07/1.49  splitting_time:                         0.
% 8.07/1.49  sem_filter_time:                        0.
% 8.07/1.49  monotx_time:                            0.
% 8.07/1.49  subtype_inf_time:                       0.
% 8.07/1.49  
% 8.07/1.49  ------ Problem properties
% 8.07/1.49  
% 8.07/1.49  clauses:                                9
% 8.07/1.49  conjectures:                            1
% 8.07/1.49  epr:                                    0
% 8.07/1.49  horn:                                   7
% 8.07/1.49  ground:                                 1
% 8.07/1.49  unary:                                  4
% 8.07/1.49  binary:                                 0
% 8.07/1.49  lits:                                   22
% 8.07/1.49  lits_eq:                                14
% 8.07/1.49  fd_pure:                                0
% 8.07/1.49  fd_pseudo:                              0
% 8.07/1.49  fd_cond:                                0
% 8.07/1.49  fd_pseudo_cond:                         4
% 8.07/1.49  ac_symbols:                             0
% 8.07/1.49  
% 8.07/1.49  ------ Propositional Solver
% 8.07/1.49  
% 8.07/1.49  prop_solver_calls:                      24
% 8.07/1.49  prop_fast_solver_calls:                 516
% 8.07/1.49  smt_solver_calls:                       0
% 8.07/1.49  smt_fast_solver_calls:                  0
% 8.07/1.49  prop_num_of_clauses:                    1602
% 8.07/1.49  prop_preprocess_simplified:             3499
% 8.07/1.49  prop_fo_subsumed:                       3
% 8.07/1.49  prop_solver_time:                       0.
% 8.07/1.49  smt_solver_time:                        0.
% 8.07/1.49  smt_fast_solver_time:                   0.
% 8.07/1.49  prop_fast_solver_time:                  0.
% 8.07/1.49  prop_unsat_core_time:                   0.
% 8.07/1.49  
% 8.07/1.49  ------ QBF
% 8.07/1.49  
% 8.07/1.49  qbf_q_res:                              0
% 8.07/1.49  qbf_num_tautologies:                    0
% 8.07/1.49  qbf_prep_cycles:                        0
% 8.07/1.49  
% 8.07/1.49  ------ BMC1
% 8.07/1.49  
% 8.07/1.49  bmc1_current_bound:                     -1
% 8.07/1.49  bmc1_last_solved_bound:                 -1
% 8.07/1.49  bmc1_unsat_core_size:                   -1
% 8.07/1.49  bmc1_unsat_core_parents_size:           -1
% 8.07/1.49  bmc1_merge_next_fun:                    0
% 8.07/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.07/1.49  
% 8.07/1.49  ------ Instantiation
% 8.07/1.49  
% 8.07/1.49  inst_num_of_clauses:                    342
% 8.07/1.49  inst_num_in_passive:                    136
% 8.07/1.49  inst_num_in_active:                     169
% 8.07/1.49  inst_num_in_unprocessed:                36
% 8.07/1.49  inst_num_of_loops:                      186
% 8.07/1.49  inst_num_of_learning_restarts:          0
% 8.07/1.49  inst_num_moves_active_passive:          14
% 8.07/1.49  inst_lit_activity:                      0
% 8.07/1.49  inst_lit_activity_moves:                0
% 8.07/1.49  inst_num_tautologies:                   0
% 8.07/1.49  inst_num_prop_implied:                  0
% 8.07/1.49  inst_num_existing_simplified:           0
% 8.07/1.49  inst_num_eq_res_simplified:             0
% 8.07/1.49  inst_num_child_elim:                    0
% 8.07/1.49  inst_num_of_dismatching_blockings:      156
% 8.07/1.49  inst_num_of_non_proper_insts:           372
% 8.07/1.49  inst_num_of_duplicates:                 0
% 8.07/1.49  inst_inst_num_from_inst_to_res:         0
% 8.07/1.49  inst_dismatching_checking_time:         0.
% 8.07/1.49  
% 8.07/1.49  ------ Resolution
% 8.07/1.49  
% 8.07/1.49  res_num_of_clauses:                     0
% 8.07/1.49  res_num_in_passive:                     0
% 8.07/1.49  res_num_in_active:                      0
% 8.07/1.49  res_num_of_loops:                       39
% 8.07/1.49  res_forward_subset_subsumed:            88
% 8.07/1.49  res_backward_subset_subsumed:           0
% 8.07/1.49  res_forward_subsumed:                   0
% 8.07/1.49  res_backward_subsumed:                  0
% 8.07/1.49  res_forward_subsumption_resolution:     0
% 8.07/1.49  res_backward_subsumption_resolution:    0
% 8.07/1.49  res_clause_to_clause_subsumption:       17708
% 8.07/1.49  res_orphan_elimination:                 0
% 8.07/1.49  res_tautology_del:                      18
% 8.07/1.49  res_num_eq_res_simplified:              0
% 8.07/1.49  res_num_sel_changes:                    0
% 8.07/1.49  res_moves_from_active_to_pass:          0
% 8.07/1.49  
% 8.07/1.49  ------ Superposition
% 8.07/1.49  
% 8.07/1.49  sup_time_total:                         0.
% 8.07/1.49  sup_time_generating:                    0.
% 8.07/1.49  sup_time_sim_full:                      0.
% 8.07/1.49  sup_time_sim_immed:                     0.
% 8.07/1.49  
% 8.07/1.49  sup_num_of_clauses:                     479
% 8.07/1.49  sup_num_in_active:                      32
% 8.07/1.49  sup_num_in_passive:                     447
% 8.07/1.49  sup_num_of_loops:                       36
% 8.07/1.49  sup_fw_superposition:                   508
% 8.07/1.49  sup_bw_superposition:                   473
% 8.07/1.49  sup_immediate_simplified:               285
% 8.07/1.49  sup_given_eliminated:                   0
% 8.07/1.49  comparisons_done:                       0
% 8.07/1.49  comparisons_avoided:                    129
% 8.07/1.49  
% 8.07/1.49  ------ Simplifications
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  sim_fw_subset_subsumed:                 49
% 8.07/1.49  sim_bw_subset_subsumed:                 5
% 8.07/1.49  sim_fw_subsumed:                        216
% 8.07/1.49  sim_bw_subsumed:                        19
% 8.07/1.49  sim_fw_subsumption_res:                 0
% 8.07/1.49  sim_bw_subsumption_res:                 0
% 8.07/1.49  sim_tautology_del:                      18
% 8.07/1.49  sim_eq_tautology_del:                   67
% 8.07/1.49  sim_eq_res_simp:                        0
% 8.07/1.49  sim_fw_demodulated:                     0
% 8.07/1.49  sim_bw_demodulated:                     0
% 8.07/1.49  sim_light_normalised:                   0
% 8.07/1.49  sim_joinable_taut:                      0
% 8.07/1.49  sim_joinable_simp:                      0
% 8.07/1.49  sim_ac_normalised:                      0
% 8.07/1.49  sim_smt_subsumption:                    0
% 8.07/1.49  
%------------------------------------------------------------------------------
