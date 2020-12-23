%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0243+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:48 EST 2020

% Result     : Theorem 1.30s
% Output     : CNFRefutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 314 expanded)
%              Number of clauses        :   40 (  87 expanded)
%              Number of leaves         :    6 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  261 (1533 expanded)
%              Number of equality atoms :  119 ( 469 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK3,sK4)
        | ~ r2_hidden(sK2,sK4)
        | ~ r1_tarski(k2_tarski(sK2,sK3),sK4) )
      & ( ( r2_hidden(sK3,sK4)
          & r2_hidden(sK2,sK4) )
        | r1_tarski(k2_tarski(sK2,sK3),sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(sK2,sK4)
      | ~ r1_tarski(k2_tarski(sK2,sK3),sK4) )
    & ( ( r2_hidden(sK3,sK4)
        & r2_hidden(sK2,sK4) )
      | r1_tarski(k2_tarski(sK2,sK3),sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f18])).

fof(f31,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK2,sK4)
    | ~ r1_tarski(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,
    ( r2_hidden(sK3,sK4)
    | r1_tarski(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f22])).

fof(f33,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f32])).

fof(f29,plain,
    ( r2_hidden(sK2,sK4)
    | r1_tarski(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f21])).

fof(f35,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f34])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_447,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_449,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_777,plain,
    ( sK1(k2_tarski(X0,X1),X2) = X0
    | sK1(k2_tarski(X0,X1),X2) = X1
    | r1_tarski(k2_tarski(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_447,c_449])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(sK2,sK3),sK4)
    | ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_445,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1347,plain,
    ( sK1(k2_tarski(sK2,sK3),sK4) = sK2
    | sK1(k2_tarski(sK2,sK3),sK4) = sK3
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_445])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4)
    | r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_444,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_446,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_682,plain,
    ( r2_hidden(X0,k2_tarski(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_444,c_446])).

cnf(c_13,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_539,plain,
    ( ~ r1_tarski(k2_tarski(X0,X1),X2)
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_tarski(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_574,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK3),sK4)
    | ~ r2_hidden(sK3,k2_tarski(sK2,sK3))
    | r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_575,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) != iProver_top
    | r2_hidden(sK3,k2_tarski(sK2,sK3)) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_3,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_627,plain,
    ( r2_hidden(sK3,k2_tarski(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_628,plain,
    ( r2_hidden(sK3,k2_tarski(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_980,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_682,c_13,c_575,c_628])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4)
    | r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_443,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_683,plain,
    ( r2_hidden(X0,k2_tarski(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_443,c_446])).

cnf(c_12,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_544,plain,
    ( ~ r1_tarski(k2_tarski(X0,X1),X2)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_584,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK3),sK4)
    | ~ r2_hidden(sK2,k2_tarski(sK2,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_585,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) != iProver_top
    | r2_hidden(sK2,k2_tarski(sK2,sK3)) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_630,plain,
    ( r2_hidden(sK2,k2_tarski(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_631,plain,
    ( r2_hidden(sK2,k2_tarski(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_1142,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_12,c_585,c_631])).

cnf(c_1369,plain,
    ( sK1(k2_tarski(sK2,sK3),sK4) = sK2
    | sK1(k2_tarski(sK2,sK3),sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1347,c_12,c_13,c_575,c_585,c_628,c_631])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_448,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1374,plain,
    ( sK1(k2_tarski(sK2,sK3),sK4) = sK3
    | r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1369,c_448])).

cnf(c_14,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1530,plain,
    ( sK1(k2_tarski(sK2,sK3),sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1374,c_12,c_13,c_14,c_575,c_585,c_628,c_631])).

cnf(c_1535,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_448])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1535,c_1142,c_980,c_14])).


%------------------------------------------------------------------------------
