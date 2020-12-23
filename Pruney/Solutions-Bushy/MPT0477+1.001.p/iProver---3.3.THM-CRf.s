%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0477+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:23 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 237 expanded)
%              Number of clauses        :   41 (  86 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   22
%              Number of atoms          :  311 (1473 expanded)
%              Number of equality atoms :  168 ( 597 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK0(X0,X1) != sK1(X0,X1)
          | ~ r2_hidden(sK0(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( ( sK0(X0,X1) = sK1(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK0(X0,X1) != sK1(X0,X1)
              | ~ r2_hidden(sK0(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( ( sK0(X0,X1) = sK1(X0,X1)
                & r2_hidden(sK0(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f21,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f20,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f22,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f22])).

fof(f33,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,conjecture,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,
    ( ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0))
   => k6_relat_1(sK4) != k4_relat_1(k6_relat_1(sK4)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k6_relat_1(sK4) != k4_relat_1(k6_relat_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f8,f18])).

fof(f31,plain,(
    k6_relat_1(sK4) != k4_relat_1(k6_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_10,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_312,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_315,plain,
    ( k4_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) = iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | ~ v1_relat_1(k6_relat_1(X2))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_318,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) != iProver_top
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_772,plain,
    ( sK2(k6_relat_1(X0),X1) = sK3(k6_relat_1(X0),X1)
    | k4_relat_1(k6_relat_1(X0)) = X1
    | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK3(k6_relat_1(X0),X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_315,c_318])).

cnf(c_12,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1544,plain,
    ( v1_relat_1(X1) != iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK3(k6_relat_1(X0),X1)),X1) = iProver_top
    | k4_relat_1(k6_relat_1(X0)) = X1
    | sK2(k6_relat_1(X0),X1) = sK3(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_772,c_12])).

cnf(c_1545,plain,
    ( sK2(k6_relat_1(X0),X1) = sK3(k6_relat_1(X0),X1)
    | k4_relat_1(k6_relat_1(X0)) = X1
    | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK3(k6_relat_1(X0),X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1544])).

cnf(c_1550,plain,
    ( sK2(k6_relat_1(X0),k6_relat_1(X1)) = sK3(k6_relat_1(X0),k6_relat_1(X1))
    | k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_318])).

cnf(c_1619,plain,
    ( sK2(k6_relat_1(X0),k6_relat_1(X1)) = sK3(k6_relat_1(X0),k6_relat_1(X1))
    | k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1) ),
    inference(superposition,[status(thm)],[c_312,c_1550])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_317,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_773,plain,
    ( k4_relat_1(k6_relat_1(X0)) = X1
    | r2_hidden(sK3(k6_relat_1(X0),X1),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK3(k6_relat_1(X0),X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_315,c_317])).

cnf(c_2076,plain,
    ( v1_relat_1(X1) != iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK3(k6_relat_1(X0),X1)),X1) = iProver_top
    | r2_hidden(sK3(k6_relat_1(X0),X1),X0) = iProver_top
    | k4_relat_1(k6_relat_1(X0)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_773,c_12])).

cnf(c_2077,plain,
    ( k4_relat_1(k6_relat_1(X0)) = X1
    | r2_hidden(sK3(k6_relat_1(X0),X1),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK3(k6_relat_1(X0),X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2076])).

cnf(c_2084,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
    | r2_hidden(sK2(k6_relat_1(X0),k6_relat_1(X1)),X1) = iProver_top
    | r2_hidden(sK3(k6_relat_1(X0),k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2077,c_317])).

cnf(c_2166,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
    | r2_hidden(sK3(k6_relat_1(X0),k6_relat_1(X1)),X1) = iProver_top
    | r2_hidden(sK3(k6_relat_1(X0),k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_2084])).

cnf(c_2169,plain,
    ( k4_relat_1(k6_relat_1(sK4)) = k6_relat_1(sK4)
    | r2_hidden(sK3(k6_relat_1(sK4),k6_relat_1(sK4)),sK4) = iProver_top
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2166])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_319,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_316,plain,
    ( k4_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1703,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
    | r2_hidden(k4_tarski(sK3(k6_relat_1(X0),k6_relat_1(X1)),sK2(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X0)) != iProver_top
    | r2_hidden(k4_tarski(sK3(k6_relat_1(X0),k6_relat_1(X1)),sK3(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_316])).

cnf(c_1928,plain,
    ( r2_hidden(k4_tarski(sK3(k6_relat_1(X0),k6_relat_1(X1)),sK3(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(k6_relat_1(X0),k6_relat_1(X1)),sK2(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X0)) != iProver_top
    | k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1703,c_12])).

cnf(c_1929,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
    | r2_hidden(k4_tarski(sK3(k6_relat_1(X0),k6_relat_1(X1)),sK2(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X0)) != iProver_top
    | r2_hidden(k4_tarski(sK3(k6_relat_1(X0),k6_relat_1(X1)),sK3(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1928])).

cnf(c_1932,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
    | r2_hidden(sK3(k6_relat_1(X0),k6_relat_1(X1)),X1) != iProver_top
    | r2_hidden(k4_tarski(sK3(k6_relat_1(X0),k6_relat_1(X1)),sK2(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_319,c_1929])).

cnf(c_1938,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
    | r2_hidden(sK3(k6_relat_1(X0),k6_relat_1(X1)),X1) != iProver_top
    | r2_hidden(k4_tarski(sK3(k6_relat_1(X0),k6_relat_1(X1)),sK3(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1932])).

cnf(c_1994,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1)
    | r2_hidden(sK3(k6_relat_1(X0),k6_relat_1(X1)),X1) != iProver_top
    | r2_hidden(sK3(k6_relat_1(X0),k6_relat_1(X1)),X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_319,c_1938])).

cnf(c_1996,plain,
    ( k4_relat_1(k6_relat_1(sK4)) = k6_relat_1(sK4)
    | r2_hidden(sK3(k6_relat_1(sK4),k6_relat_1(sK4)),sK4) != iProver_top
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1994])).

cnf(c_132,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_348,plain,
    ( k4_relat_1(k6_relat_1(sK4)) != X0
    | k6_relat_1(sK4) != X0
    | k6_relat_1(sK4) = k4_relat_1(k6_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_390,plain,
    ( k4_relat_1(k6_relat_1(sK4)) != k6_relat_1(sK4)
    | k6_relat_1(sK4) = k4_relat_1(k6_relat_1(sK4))
    | k6_relat_1(sK4) != k6_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_131,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_144,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_133,plain,
    ( X0 != X1
    | k6_relat_1(X0) = k6_relat_1(X1) ),
    theory(equality)).

cnf(c_138,plain,
    ( k6_relat_1(sK4) = k6_relat_1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_14,plain,
    ( v1_relat_1(k6_relat_1(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,negated_conjecture,
    ( k6_relat_1(sK4) != k4_relat_1(k6_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2169,c_1996,c_390,c_144,c_138,c_14,c_11])).


%------------------------------------------------------------------------------
