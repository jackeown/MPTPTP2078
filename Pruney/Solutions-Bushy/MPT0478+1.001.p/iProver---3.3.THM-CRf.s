%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0478+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:24 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 112 expanded)
%              Number of clauses        :   31 (  37 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 ( 482 expanded)
%              Number of equality atoms :   72 ( 104 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f6])).

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
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f22,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ( r2_hidden(X2,X0)
             => r2_hidden(k4_tarski(X2,X2),X1) )
         => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),X1)
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),X1)
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k6_relat_1(X0),X1)
        & ! [X2] :
            ( r2_hidden(k4_tarski(X2,X2),X1)
            | ~ r2_hidden(X2,X0) )
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_relat_1(sK4),sK5)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),sK5)
          | ~ r2_hidden(X2,sK4) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_tarski(k6_relat_1(sK4),sK5)
    & ! [X2] :
        ( r2_hidden(k4_tarski(X2,X2),sK5)
        | ~ r2_hidden(X2,sK4) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f9,f19])).

fof(f33,plain,(
    ~ r1_tarski(k6_relat_1(sK4),sK5) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(X2,X2),sK5)
      | ~ r2_hidden(X2,sK4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_757,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | ~ v1_relat_1(k6_relat_1(X2))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_760,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) != iProver_top
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_755,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_778,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X0),k6_relat_1(X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_760,c_755])).

cnf(c_1213,plain,
    ( sK3(k6_relat_1(X0),X1) = sK2(k6_relat_1(X0),X1)
    | r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_757,c_778])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2023,plain,
    ( r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | sK3(k6_relat_1(X0),X1) = sK2(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1213,c_18])).

cnf(c_2024,plain,
    ( sK3(k6_relat_1(X0),X1) = sK2(k6_relat_1(X0),X1)
    | r1_tarski(k6_relat_1(X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2023])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k6_relat_1(sK4),sK5) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_754,plain,
    ( r1_tarski(k6_relat_1(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2032,plain,
    ( sK3(k6_relat_1(sK4),sK5) = sK2(k6_relat_1(sK4),sK5) ),
    inference(superposition,[status(thm)],[c_2024,c_754])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_758,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2058,plain,
    ( r1_tarski(k6_relat_1(sK4),sK5) = iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),sK5),sK2(k6_relat_1(sK4),sK5)),sK5) != iProver_top
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2032,c_758])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(k4_tarski(X0,X0),sK5) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_970,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK4),sK5),sK4)
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),sK5),sK2(k6_relat_1(sK4),sK5)),sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_971,plain,
    ( r2_hidden(sK2(k6_relat_1(sK4),sK5),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),sK5),sK2(k6_relat_1(sK4),sK5)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_908,plain,
    ( r2_hidden(sK2(k6_relat_1(sK4),sK5),sK4)
    | ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),sK5),sK3(k6_relat_1(sK4),sK5)),k6_relat_1(sK4))
    | ~ v1_relat_1(k6_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_909,plain,
    ( r2_hidden(sK2(k6_relat_1(sK4),sK5),sK4) = iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),sK5),sK3(k6_relat_1(sK4),sK5)),k6_relat_1(sK4)) != iProver_top
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_908])).

cnf(c_897,plain,
    ( v1_relat_1(k6_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_898,plain,
    ( v1_relat_1(k6_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_176,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0)
    | k6_relat_1(sK4) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_177,plain,
    ( r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),sK5),sK3(k6_relat_1(sK4),sK5)),k6_relat_1(sK4))
    | ~ v1_relat_1(k6_relat_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_183,plain,
    ( r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),sK5),sK3(k6_relat_1(sK4),sK5)),k6_relat_1(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_177,c_9])).

cnf(c_185,plain,
    ( r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),sK5),sK3(k6_relat_1(sK4),sK5)),k6_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_17,plain,
    ( r1_tarski(k6_relat_1(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2058,c_971,c_909,c_898,c_185,c_17])).


%------------------------------------------------------------------------------
