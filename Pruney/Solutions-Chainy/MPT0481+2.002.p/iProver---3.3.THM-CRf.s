%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:34 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  105 (5634 expanded)
%              Number of clauses        :   66 (1938 expanded)
%              Number of leaves         :   11 (1242 expanded)
%              Depth                    :   39
%              Number of atoms          :  311 (17594 expanded)
%              Number of equality atoms :  147 (5263 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f19])).

fof(f22,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f22,f21])).

fof(f32,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK2(X4),sK3(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
        | ~ r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
      | ~ r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f28])).

fof(f44,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
    | ~ r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_460,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_456,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK2(X0),sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_457,plain,
    ( k4_tarski(sK2(X0),sK3(X0)) = X0
    | r2_hidden(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_771,plain,
    ( k4_tarski(sK2(sK0(X0,X1)),sK3(sK0(X0,X1))) = sK0(X0,X1)
    | r1_tarski(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_457])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
    | ~ r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_448,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) != iProver_top
    | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1193,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
    | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_448])).

cnf(c_1199,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
    | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | v1_relat_1(k5_relat_1(k6_relat_1(sK4),sK5)) != iProver_top
    | v1_relat_1(k5_relat_1(sK5,k6_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_1193])).

cnf(c_1208,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
    | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | v1_relat_1(k5_relat_1(sK5,k6_relat_1(sK4))) != iProver_top
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_456,c_1199])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_674,plain,
    ( v1_relat_1(k5_relat_1(sK5,k6_relat_1(sK4)))
    | ~ v1_relat_1(k6_relat_1(sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_675,plain,
    ( v1_relat_1(k5_relat_1(sK5,k6_relat_1(sK4))) = iProver_top
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_936,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK4),sK5))
    | ~ v1_relat_1(k6_relat_1(sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_937,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK4),sK5)) = iProver_top
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_1211,plain,
    ( v1_relat_1(k6_relat_1(sK4)) != iProver_top
    | k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
    | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1208,c_15,c_675,c_937,c_1199])).

cnf(c_1212,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
    | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1211])).

cnf(c_6,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_455,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1218,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
    | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1212,c_455])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_452,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3)) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1225,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | r2_hidden(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_452])).

cnf(c_1362,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | r2_hidden(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK4) = iProver_top
    | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_1225])).

cnf(c_1772,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
    | r2_hidden(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK4) = iProver_top
    | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1362,c_15])).

cnf(c_1773,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | r2_hidden(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK4) = iProver_top
    | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_1772])).

cnf(c_1779,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | k4_tarski(sK2(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),sK3(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)))) = sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))
    | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_457])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_571,plain,
    ( ~ r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),sK5)
    | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_572,plain,
    ( r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),sK5) != iProver_top
    | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_8,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_453,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1219,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),X0) = iProver_top
    | r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),k5_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_453])).

cnf(c_1590,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),sK5) = iProver_top
    | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_1219])).

cnf(c_1802,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
    | r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),sK5) = iProver_top
    | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1590,c_15])).

cnf(c_1803,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),sK5) = iProver_top
    | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_1802])).

cnf(c_1809,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),sK5) = iProver_top
    | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1803])).

cnf(c_1904,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
    | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1779,c_572,c_1809])).

cnf(c_1905,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_1904])).

cnf(c_1910,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_448])).

cnf(c_1915,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | v1_relat_1(k5_relat_1(sK5,k6_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_1910])).

cnf(c_1978,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_456,c_1915])).

cnf(c_1981,plain,
    ( v1_relat_1(k6_relat_1(sK4)) != iProver_top
    | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1978,c_15])).

cnf(c_1982,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1981])).

cnf(c_1987,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1982,c_455])).

cnf(c_11,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,k6_relat_1(X3)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_450,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,k6_relat_1(X3))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1989,plain,
    ( r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))),X0) = iProver_top
    | r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1987,c_450])).

cnf(c_2062,plain,
    ( r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),X0) = iProver_top
    | r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1989,c_1987])).

cnf(c_2161,plain,
    ( r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),sK5) = iProver_top
    | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_2062])).

cnf(c_593,plain,
    ( ~ r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),sK5)
    | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_594,plain,
    ( r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),sK5) != iProver_top
    | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_2344,plain,
    ( r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2161,c_15,c_594])).

cnf(c_2349,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
    | v1_relat_1(k5_relat_1(k6_relat_1(sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2344,c_1193])).

cnf(c_2362,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_456,c_2349])).

cnf(c_2363,plain,
    ( ~ v1_relat_1(k6_relat_1(sK4))
    | ~ v1_relat_1(sK5)
    | k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2362])).

cnf(c_2457,plain,
    ( v1_relat_1(k6_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2483,plain,
    ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2362,c_14,c_2363,c_2457])).

cnf(c_2486,plain,
    ( r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),X0) = iProver_top
    | r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),k5_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2483,c_453])).

cnf(c_2567,plain,
    ( r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),X0) = iProver_top
    | r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),k5_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2486,c_2483])).

cnf(c_2661,plain,
    ( r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),sK5) = iProver_top
    | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_2567])).

cnf(c_16,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) != iProver_top
    | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2661,c_2344,c_572,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:53:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.28/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/0.96  
% 2.28/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.28/0.96  
% 2.28/0.96  ------  iProver source info
% 2.28/0.96  
% 2.28/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.28/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.28/0.96  git: non_committed_changes: false
% 2.28/0.96  git: last_make_outside_of_git: false
% 2.28/0.96  
% 2.28/0.96  ------ 
% 2.28/0.96  
% 2.28/0.96  ------ Input Options
% 2.28/0.96  
% 2.28/0.96  --out_options                           all
% 2.28/0.96  --tptp_safe_out                         true
% 2.28/0.96  --problem_path                          ""
% 2.28/0.96  --include_path                          ""
% 2.28/0.96  --clausifier                            res/vclausify_rel
% 2.28/0.96  --clausifier_options                    --mode clausify
% 2.28/0.96  --stdin                                 false
% 2.28/0.96  --stats_out                             all
% 2.28/0.96  
% 2.28/0.96  ------ General Options
% 2.28/0.96  
% 2.28/0.96  --fof                                   false
% 2.28/0.96  --time_out_real                         305.
% 2.28/0.96  --time_out_virtual                      -1.
% 2.28/0.96  --symbol_type_check                     false
% 2.28/0.96  --clausify_out                          false
% 2.28/0.96  --sig_cnt_out                           false
% 2.28/0.96  --trig_cnt_out                          false
% 2.28/0.96  --trig_cnt_out_tolerance                1.
% 2.28/0.96  --trig_cnt_out_sk_spl                   false
% 2.28/0.96  --abstr_cl_out                          false
% 2.28/0.96  
% 2.28/0.96  ------ Global Options
% 2.28/0.96  
% 2.28/0.96  --schedule                              default
% 2.28/0.96  --add_important_lit                     false
% 2.28/0.96  --prop_solver_per_cl                    1000
% 2.28/0.96  --min_unsat_core                        false
% 2.28/0.96  --soft_assumptions                      false
% 2.28/0.96  --soft_lemma_size                       3
% 2.28/0.96  --prop_impl_unit_size                   0
% 2.28/0.96  --prop_impl_unit                        []
% 2.28/0.96  --share_sel_clauses                     true
% 2.28/0.96  --reset_solvers                         false
% 2.28/0.96  --bc_imp_inh                            [conj_cone]
% 2.28/0.96  --conj_cone_tolerance                   3.
% 2.28/0.96  --extra_neg_conj                        none
% 2.28/0.96  --large_theory_mode                     true
% 2.28/0.96  --prolific_symb_bound                   200
% 2.28/0.96  --lt_threshold                          2000
% 2.28/0.96  --clause_weak_htbl                      true
% 2.28/0.96  --gc_record_bc_elim                     false
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing Options
% 2.28/0.96  
% 2.28/0.96  --preprocessing_flag                    true
% 2.28/0.96  --time_out_prep_mult                    0.1
% 2.28/0.96  --splitting_mode                        input
% 2.28/0.96  --splitting_grd                         true
% 2.28/0.96  --splitting_cvd                         false
% 2.28/0.96  --splitting_cvd_svl                     false
% 2.28/0.96  --splitting_nvd                         32
% 2.28/0.96  --sub_typing                            true
% 2.28/0.96  --prep_gs_sim                           true
% 2.28/0.96  --prep_unflatten                        true
% 2.28/0.96  --prep_res_sim                          true
% 2.28/0.96  --prep_upred                            true
% 2.28/0.96  --prep_sem_filter                       exhaustive
% 2.28/0.96  --prep_sem_filter_out                   false
% 2.28/0.96  --pred_elim                             true
% 2.28/0.96  --res_sim_input                         true
% 2.28/0.96  --eq_ax_congr_red                       true
% 2.28/0.96  --pure_diseq_elim                       true
% 2.28/0.96  --brand_transform                       false
% 2.28/0.96  --non_eq_to_eq                          false
% 2.28/0.96  --prep_def_merge                        true
% 2.28/0.96  --prep_def_merge_prop_impl              false
% 2.28/0.96  --prep_def_merge_mbd                    true
% 2.28/0.96  --prep_def_merge_tr_red                 false
% 2.28/0.96  --prep_def_merge_tr_cl                  false
% 2.28/0.96  --smt_preprocessing                     true
% 2.28/0.96  --smt_ac_axioms                         fast
% 2.28/0.96  --preprocessed_out                      false
% 2.28/0.96  --preprocessed_stats                    false
% 2.28/0.96  
% 2.28/0.96  ------ Abstraction refinement Options
% 2.28/0.96  
% 2.28/0.96  --abstr_ref                             []
% 2.28/0.96  --abstr_ref_prep                        false
% 2.28/0.96  --abstr_ref_until_sat                   false
% 2.28/0.96  --abstr_ref_sig_restrict                funpre
% 2.28/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.28/0.96  --abstr_ref_under                       []
% 2.28/0.96  
% 2.28/0.96  ------ SAT Options
% 2.28/0.96  
% 2.28/0.96  --sat_mode                              false
% 2.28/0.96  --sat_fm_restart_options                ""
% 2.28/0.96  --sat_gr_def                            false
% 2.28/0.96  --sat_epr_types                         true
% 2.28/0.96  --sat_non_cyclic_types                  false
% 2.28/0.96  --sat_finite_models                     false
% 2.28/0.96  --sat_fm_lemmas                         false
% 2.28/0.96  --sat_fm_prep                           false
% 2.28/0.96  --sat_fm_uc_incr                        true
% 2.28/0.96  --sat_out_model                         small
% 2.28/0.96  --sat_out_clauses                       false
% 2.28/0.96  
% 2.28/0.96  ------ QBF Options
% 2.28/0.96  
% 2.28/0.96  --qbf_mode                              false
% 2.28/0.96  --qbf_elim_univ                         false
% 2.28/0.96  --qbf_dom_inst                          none
% 2.28/0.96  --qbf_dom_pre_inst                      false
% 2.28/0.96  --qbf_sk_in                             false
% 2.28/0.96  --qbf_pred_elim                         true
% 2.28/0.96  --qbf_split                             512
% 2.28/0.96  
% 2.28/0.96  ------ BMC1 Options
% 2.28/0.96  
% 2.28/0.96  --bmc1_incremental                      false
% 2.28/0.96  --bmc1_axioms                           reachable_all
% 2.28/0.96  --bmc1_min_bound                        0
% 2.28/0.96  --bmc1_max_bound                        -1
% 2.28/0.96  --bmc1_max_bound_default                -1
% 2.28/0.96  --bmc1_symbol_reachability              true
% 2.28/0.96  --bmc1_property_lemmas                  false
% 2.28/0.96  --bmc1_k_induction                      false
% 2.28/0.96  --bmc1_non_equiv_states                 false
% 2.28/0.96  --bmc1_deadlock                         false
% 2.28/0.96  --bmc1_ucm                              false
% 2.28/0.96  --bmc1_add_unsat_core                   none
% 2.28/0.96  --bmc1_unsat_core_children              false
% 2.28/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.28/0.96  --bmc1_out_stat                         full
% 2.28/0.96  --bmc1_ground_init                      false
% 2.28/0.96  --bmc1_pre_inst_next_state              false
% 2.28/0.96  --bmc1_pre_inst_state                   false
% 2.28/0.96  --bmc1_pre_inst_reach_state             false
% 2.28/0.96  --bmc1_out_unsat_core                   false
% 2.28/0.96  --bmc1_aig_witness_out                  false
% 2.28/0.96  --bmc1_verbose                          false
% 2.28/0.96  --bmc1_dump_clauses_tptp                false
% 2.28/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.28/0.96  --bmc1_dump_file                        -
% 2.28/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.28/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.28/0.96  --bmc1_ucm_extend_mode                  1
% 2.28/0.96  --bmc1_ucm_init_mode                    2
% 2.28/0.96  --bmc1_ucm_cone_mode                    none
% 2.28/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.28/0.96  --bmc1_ucm_relax_model                  4
% 2.28/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.28/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.28/0.96  --bmc1_ucm_layered_model                none
% 2.28/0.96  --bmc1_ucm_max_lemma_size               10
% 2.28/0.96  
% 2.28/0.96  ------ AIG Options
% 2.28/0.96  
% 2.28/0.96  --aig_mode                              false
% 2.28/0.96  
% 2.28/0.96  ------ Instantiation Options
% 2.28/0.96  
% 2.28/0.96  --instantiation_flag                    true
% 2.28/0.96  --inst_sos_flag                         false
% 2.28/0.96  --inst_sos_phase                        true
% 2.28/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.28/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.28/0.96  --inst_lit_sel_side                     num_symb
% 2.28/0.96  --inst_solver_per_active                1400
% 2.28/0.96  --inst_solver_calls_frac                1.
% 2.28/0.96  --inst_passive_queue_type               priority_queues
% 2.28/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.28/0.96  --inst_passive_queues_freq              [25;2]
% 2.28/0.96  --inst_dismatching                      true
% 2.28/0.96  --inst_eager_unprocessed_to_passive     true
% 2.28/0.96  --inst_prop_sim_given                   true
% 2.28/0.96  --inst_prop_sim_new                     false
% 2.28/0.96  --inst_subs_new                         false
% 2.28/0.96  --inst_eq_res_simp                      false
% 2.28/0.96  --inst_subs_given                       false
% 2.28/0.96  --inst_orphan_elimination               true
% 2.28/0.96  --inst_learning_loop_flag               true
% 2.28/0.96  --inst_learning_start                   3000
% 2.28/0.96  --inst_learning_factor                  2
% 2.28/0.96  --inst_start_prop_sim_after_learn       3
% 2.28/0.96  --inst_sel_renew                        solver
% 2.28/0.96  --inst_lit_activity_flag                true
% 2.28/0.96  --inst_restr_to_given                   false
% 2.28/0.96  --inst_activity_threshold               500
% 2.28/0.96  --inst_out_proof                        true
% 2.28/0.96  
% 2.28/0.96  ------ Resolution Options
% 2.28/0.96  
% 2.28/0.96  --resolution_flag                       true
% 2.28/0.96  --res_lit_sel                           adaptive
% 2.28/0.96  --res_lit_sel_side                      none
% 2.28/0.96  --res_ordering                          kbo
% 2.28/0.96  --res_to_prop_solver                    active
% 2.28/0.96  --res_prop_simpl_new                    false
% 2.28/0.96  --res_prop_simpl_given                  true
% 2.28/0.96  --res_passive_queue_type                priority_queues
% 2.28/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.28/0.96  --res_passive_queues_freq               [15;5]
% 2.28/0.96  --res_forward_subs                      full
% 2.28/0.96  --res_backward_subs                     full
% 2.28/0.96  --res_forward_subs_resolution           true
% 2.28/0.96  --res_backward_subs_resolution          true
% 2.28/0.96  --res_orphan_elimination                true
% 2.28/0.96  --res_time_limit                        2.
% 2.28/0.96  --res_out_proof                         true
% 2.28/0.96  
% 2.28/0.96  ------ Superposition Options
% 2.28/0.96  
% 2.28/0.96  --superposition_flag                    true
% 2.28/0.96  --sup_passive_queue_type                priority_queues
% 2.28/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.28/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.28/0.96  --demod_completeness_check              fast
% 2.28/0.96  --demod_use_ground                      true
% 2.28/0.96  --sup_to_prop_solver                    passive
% 2.28/0.96  --sup_prop_simpl_new                    true
% 2.28/0.96  --sup_prop_simpl_given                  true
% 2.28/0.96  --sup_fun_splitting                     false
% 2.28/0.96  --sup_smt_interval                      50000
% 2.28/0.96  
% 2.28/0.96  ------ Superposition Simplification Setup
% 2.28/0.96  
% 2.28/0.96  --sup_indices_passive                   []
% 2.28/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.28/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_full_bw                           [BwDemod]
% 2.28/0.96  --sup_immed_triv                        [TrivRules]
% 2.28/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.28/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_immed_bw_main                     []
% 2.28/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.28/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.96  
% 2.28/0.96  ------ Combination Options
% 2.28/0.96  
% 2.28/0.96  --comb_res_mult                         3
% 2.28/0.96  --comb_sup_mult                         2
% 2.28/0.96  --comb_inst_mult                        10
% 2.28/0.96  
% 2.28/0.96  ------ Debug Options
% 2.28/0.96  
% 2.28/0.96  --dbg_backtrace                         false
% 2.28/0.96  --dbg_dump_prop_clauses                 false
% 2.28/0.96  --dbg_dump_prop_clauses_file            -
% 2.28/0.96  --dbg_out_stat                          false
% 2.28/0.96  ------ Parsing...
% 2.28/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.28/0.96  ------ Proving...
% 2.28/0.96  ------ Problem Properties 
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  clauses                                 15
% 2.28/0.96  conjectures                             2
% 2.28/0.96  EPR                                     1
% 2.28/0.96  Horn                                    13
% 2.28/0.96  unary                                   2
% 2.28/0.96  binary                                  5
% 2.28/0.96  lits                                    38
% 2.28/0.96  lits eq                                 2
% 2.28/0.96  fd_pure                                 0
% 2.28/0.96  fd_pseudo                               0
% 2.28/0.96  fd_cond                                 0
% 2.28/0.96  fd_pseudo_cond                          0
% 2.28/0.96  AC symbols                              0
% 2.28/0.96  
% 2.28/0.96  ------ Schedule dynamic 5 is on 
% 2.28/0.96  
% 2.28/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  ------ 
% 2.28/0.96  Current options:
% 2.28/0.96  ------ 
% 2.28/0.96  
% 2.28/0.96  ------ Input Options
% 2.28/0.96  
% 2.28/0.96  --out_options                           all
% 2.28/0.96  --tptp_safe_out                         true
% 2.28/0.96  --problem_path                          ""
% 2.28/0.96  --include_path                          ""
% 2.28/0.96  --clausifier                            res/vclausify_rel
% 2.28/0.96  --clausifier_options                    --mode clausify
% 2.28/0.96  --stdin                                 false
% 2.28/0.96  --stats_out                             all
% 2.28/0.96  
% 2.28/0.96  ------ General Options
% 2.28/0.96  
% 2.28/0.96  --fof                                   false
% 2.28/0.96  --time_out_real                         305.
% 2.28/0.96  --time_out_virtual                      -1.
% 2.28/0.96  --symbol_type_check                     false
% 2.28/0.96  --clausify_out                          false
% 2.28/0.96  --sig_cnt_out                           false
% 2.28/0.96  --trig_cnt_out                          false
% 2.28/0.96  --trig_cnt_out_tolerance                1.
% 2.28/0.96  --trig_cnt_out_sk_spl                   false
% 2.28/0.96  --abstr_cl_out                          false
% 2.28/0.96  
% 2.28/0.96  ------ Global Options
% 2.28/0.96  
% 2.28/0.96  --schedule                              default
% 2.28/0.96  --add_important_lit                     false
% 2.28/0.96  --prop_solver_per_cl                    1000
% 2.28/0.96  --min_unsat_core                        false
% 2.28/0.96  --soft_assumptions                      false
% 2.28/0.96  --soft_lemma_size                       3
% 2.28/0.96  --prop_impl_unit_size                   0
% 2.28/0.96  --prop_impl_unit                        []
% 2.28/0.96  --share_sel_clauses                     true
% 2.28/0.96  --reset_solvers                         false
% 2.28/0.96  --bc_imp_inh                            [conj_cone]
% 2.28/0.96  --conj_cone_tolerance                   3.
% 2.28/0.96  --extra_neg_conj                        none
% 2.28/0.96  --large_theory_mode                     true
% 2.28/0.96  --prolific_symb_bound                   200
% 2.28/0.96  --lt_threshold                          2000
% 2.28/0.96  --clause_weak_htbl                      true
% 2.28/0.96  --gc_record_bc_elim                     false
% 2.28/0.96  
% 2.28/0.96  ------ Preprocessing Options
% 2.28/0.96  
% 2.28/0.96  --preprocessing_flag                    true
% 2.28/0.96  --time_out_prep_mult                    0.1
% 2.28/0.96  --splitting_mode                        input
% 2.28/0.96  --splitting_grd                         true
% 2.28/0.96  --splitting_cvd                         false
% 2.28/0.96  --splitting_cvd_svl                     false
% 2.28/0.96  --splitting_nvd                         32
% 2.28/0.96  --sub_typing                            true
% 2.28/0.96  --prep_gs_sim                           true
% 2.28/0.96  --prep_unflatten                        true
% 2.28/0.96  --prep_res_sim                          true
% 2.28/0.96  --prep_upred                            true
% 2.28/0.96  --prep_sem_filter                       exhaustive
% 2.28/0.96  --prep_sem_filter_out                   false
% 2.28/0.96  --pred_elim                             true
% 2.28/0.96  --res_sim_input                         true
% 2.28/0.96  --eq_ax_congr_red                       true
% 2.28/0.96  --pure_diseq_elim                       true
% 2.28/0.96  --brand_transform                       false
% 2.28/0.96  --non_eq_to_eq                          false
% 2.28/0.96  --prep_def_merge                        true
% 2.28/0.96  --prep_def_merge_prop_impl              false
% 2.28/0.96  --prep_def_merge_mbd                    true
% 2.28/0.96  --prep_def_merge_tr_red                 false
% 2.28/0.96  --prep_def_merge_tr_cl                  false
% 2.28/0.96  --smt_preprocessing                     true
% 2.28/0.96  --smt_ac_axioms                         fast
% 2.28/0.96  --preprocessed_out                      false
% 2.28/0.96  --preprocessed_stats                    false
% 2.28/0.96  
% 2.28/0.96  ------ Abstraction refinement Options
% 2.28/0.96  
% 2.28/0.96  --abstr_ref                             []
% 2.28/0.96  --abstr_ref_prep                        false
% 2.28/0.96  --abstr_ref_until_sat                   false
% 2.28/0.96  --abstr_ref_sig_restrict                funpre
% 2.28/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.28/0.96  --abstr_ref_under                       []
% 2.28/0.96  
% 2.28/0.96  ------ SAT Options
% 2.28/0.96  
% 2.28/0.96  --sat_mode                              false
% 2.28/0.96  --sat_fm_restart_options                ""
% 2.28/0.96  --sat_gr_def                            false
% 2.28/0.96  --sat_epr_types                         true
% 2.28/0.96  --sat_non_cyclic_types                  false
% 2.28/0.96  --sat_finite_models                     false
% 2.28/0.96  --sat_fm_lemmas                         false
% 2.28/0.96  --sat_fm_prep                           false
% 2.28/0.96  --sat_fm_uc_incr                        true
% 2.28/0.96  --sat_out_model                         small
% 2.28/0.96  --sat_out_clauses                       false
% 2.28/0.96  
% 2.28/0.96  ------ QBF Options
% 2.28/0.96  
% 2.28/0.96  --qbf_mode                              false
% 2.28/0.96  --qbf_elim_univ                         false
% 2.28/0.96  --qbf_dom_inst                          none
% 2.28/0.96  --qbf_dom_pre_inst                      false
% 2.28/0.96  --qbf_sk_in                             false
% 2.28/0.96  --qbf_pred_elim                         true
% 2.28/0.96  --qbf_split                             512
% 2.28/0.96  
% 2.28/0.96  ------ BMC1 Options
% 2.28/0.96  
% 2.28/0.96  --bmc1_incremental                      false
% 2.28/0.96  --bmc1_axioms                           reachable_all
% 2.28/0.96  --bmc1_min_bound                        0
% 2.28/0.96  --bmc1_max_bound                        -1
% 2.28/0.96  --bmc1_max_bound_default                -1
% 2.28/0.96  --bmc1_symbol_reachability              true
% 2.28/0.96  --bmc1_property_lemmas                  false
% 2.28/0.96  --bmc1_k_induction                      false
% 2.28/0.96  --bmc1_non_equiv_states                 false
% 2.28/0.96  --bmc1_deadlock                         false
% 2.28/0.96  --bmc1_ucm                              false
% 2.28/0.96  --bmc1_add_unsat_core                   none
% 2.28/0.96  --bmc1_unsat_core_children              false
% 2.28/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.28/0.96  --bmc1_out_stat                         full
% 2.28/0.96  --bmc1_ground_init                      false
% 2.28/0.96  --bmc1_pre_inst_next_state              false
% 2.28/0.96  --bmc1_pre_inst_state                   false
% 2.28/0.96  --bmc1_pre_inst_reach_state             false
% 2.28/0.96  --bmc1_out_unsat_core                   false
% 2.28/0.96  --bmc1_aig_witness_out                  false
% 2.28/0.96  --bmc1_verbose                          false
% 2.28/0.96  --bmc1_dump_clauses_tptp                false
% 2.28/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.28/0.96  --bmc1_dump_file                        -
% 2.28/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.28/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.28/0.96  --bmc1_ucm_extend_mode                  1
% 2.28/0.96  --bmc1_ucm_init_mode                    2
% 2.28/0.96  --bmc1_ucm_cone_mode                    none
% 2.28/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.28/0.96  --bmc1_ucm_relax_model                  4
% 2.28/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.28/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.28/0.96  --bmc1_ucm_layered_model                none
% 2.28/0.96  --bmc1_ucm_max_lemma_size               10
% 2.28/0.96  
% 2.28/0.96  ------ AIG Options
% 2.28/0.96  
% 2.28/0.96  --aig_mode                              false
% 2.28/0.96  
% 2.28/0.96  ------ Instantiation Options
% 2.28/0.96  
% 2.28/0.96  --instantiation_flag                    true
% 2.28/0.96  --inst_sos_flag                         false
% 2.28/0.96  --inst_sos_phase                        true
% 2.28/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.28/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.28/0.96  --inst_lit_sel_side                     none
% 2.28/0.96  --inst_solver_per_active                1400
% 2.28/0.96  --inst_solver_calls_frac                1.
% 2.28/0.96  --inst_passive_queue_type               priority_queues
% 2.28/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.28/0.96  --inst_passive_queues_freq              [25;2]
% 2.28/0.96  --inst_dismatching                      true
% 2.28/0.96  --inst_eager_unprocessed_to_passive     true
% 2.28/0.96  --inst_prop_sim_given                   true
% 2.28/0.96  --inst_prop_sim_new                     false
% 2.28/0.96  --inst_subs_new                         false
% 2.28/0.96  --inst_eq_res_simp                      false
% 2.28/0.96  --inst_subs_given                       false
% 2.28/0.96  --inst_orphan_elimination               true
% 2.28/0.96  --inst_learning_loop_flag               true
% 2.28/0.96  --inst_learning_start                   3000
% 2.28/0.96  --inst_learning_factor                  2
% 2.28/0.96  --inst_start_prop_sim_after_learn       3
% 2.28/0.96  --inst_sel_renew                        solver
% 2.28/0.96  --inst_lit_activity_flag                true
% 2.28/0.96  --inst_restr_to_given                   false
% 2.28/0.96  --inst_activity_threshold               500
% 2.28/0.96  --inst_out_proof                        true
% 2.28/0.96  
% 2.28/0.96  ------ Resolution Options
% 2.28/0.96  
% 2.28/0.96  --resolution_flag                       false
% 2.28/0.96  --res_lit_sel                           adaptive
% 2.28/0.96  --res_lit_sel_side                      none
% 2.28/0.96  --res_ordering                          kbo
% 2.28/0.96  --res_to_prop_solver                    active
% 2.28/0.96  --res_prop_simpl_new                    false
% 2.28/0.96  --res_prop_simpl_given                  true
% 2.28/0.96  --res_passive_queue_type                priority_queues
% 2.28/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.28/0.96  --res_passive_queues_freq               [15;5]
% 2.28/0.96  --res_forward_subs                      full
% 2.28/0.96  --res_backward_subs                     full
% 2.28/0.96  --res_forward_subs_resolution           true
% 2.28/0.96  --res_backward_subs_resolution          true
% 2.28/0.96  --res_orphan_elimination                true
% 2.28/0.96  --res_time_limit                        2.
% 2.28/0.96  --res_out_proof                         true
% 2.28/0.96  
% 2.28/0.96  ------ Superposition Options
% 2.28/0.96  
% 2.28/0.96  --superposition_flag                    true
% 2.28/0.96  --sup_passive_queue_type                priority_queues
% 2.28/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.28/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.28/0.96  --demod_completeness_check              fast
% 2.28/0.96  --demod_use_ground                      true
% 2.28/0.96  --sup_to_prop_solver                    passive
% 2.28/0.96  --sup_prop_simpl_new                    true
% 2.28/0.96  --sup_prop_simpl_given                  true
% 2.28/0.96  --sup_fun_splitting                     false
% 2.28/0.96  --sup_smt_interval                      50000
% 2.28/0.96  
% 2.28/0.96  ------ Superposition Simplification Setup
% 2.28/0.96  
% 2.28/0.96  --sup_indices_passive                   []
% 2.28/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.28/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_full_bw                           [BwDemod]
% 2.28/0.96  --sup_immed_triv                        [TrivRules]
% 2.28/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.28/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_immed_bw_main                     []
% 2.28/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.28/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.96  
% 2.28/0.96  ------ Combination Options
% 2.28/0.96  
% 2.28/0.96  --comb_res_mult                         3
% 2.28/0.96  --comb_sup_mult                         2
% 2.28/0.96  --comb_inst_mult                        10
% 2.28/0.96  
% 2.28/0.96  ------ Debug Options
% 2.28/0.96  
% 2.28/0.96  --dbg_backtrace                         false
% 2.28/0.96  --dbg_dump_prop_clauses                 false
% 2.28/0.96  --dbg_dump_prop_clauses_file            -
% 2.28/0.96  --dbg_out_stat                          false
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  ------ Proving...
% 2.28/0.96  
% 2.28/0.96  
% 2.28/0.96  % SZS status Theorem for theBenchmark.p
% 2.28/0.96  
% 2.28/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.28/0.96  
% 2.28/0.96  fof(f1,axiom,(
% 2.28/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.28/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f9,plain,(
% 2.28/0.96    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.28/0.96    inference(unused_predicate_definition_removal,[],[f1])).
% 2.28/0.96  
% 2.28/0.96  fof(f10,plain,(
% 2.28/0.96    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.28/0.96    inference(ennf_transformation,[],[f9])).
% 2.28/0.96  
% 2.28/0.96  fof(f17,plain,(
% 2.28/0.96    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f18,plain,(
% 2.28/0.96    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.28/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f17])).
% 2.28/0.96  
% 2.28/0.96  fof(f30,plain,(
% 2.28/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.28/0.96    inference(cnf_transformation,[],[f18])).
% 2.28/0.96  
% 2.28/0.96  fof(f3,axiom,(
% 2.28/0.96    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.28/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f12,plain,(
% 2.28/0.96    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.28/0.96    inference(ennf_transformation,[],[f3])).
% 2.28/0.96  
% 2.28/0.96  fof(f13,plain,(
% 2.28/0.96    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.28/0.96    inference(flattening,[],[f12])).
% 2.28/0.96  
% 2.28/0.96  fof(f35,plain,(
% 2.28/0.96    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.28/0.96    inference(cnf_transformation,[],[f13])).
% 2.28/0.96  
% 2.28/0.96  fof(f2,axiom,(
% 2.28/0.96    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 2.28/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f11,plain,(
% 2.28/0.96    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 2.28/0.96    inference(ennf_transformation,[],[f2])).
% 2.28/0.96  
% 2.28/0.96  fof(f19,plain,(
% 2.28/0.96    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 2.28/0.96    inference(nnf_transformation,[],[f11])).
% 2.28/0.96  
% 2.28/0.96  fof(f20,plain,(
% 2.28/0.96    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 2.28/0.96    inference(rectify,[],[f19])).
% 2.28/0.96  
% 2.28/0.96  fof(f22,plain,(
% 2.28/0.96    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f21,plain,(
% 2.28/0.96    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f23,plain,(
% 2.28/0.96    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 2.28/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f22,f21])).
% 2.28/0.96  
% 2.28/0.96  fof(f32,plain,(
% 2.28/0.96    ( ! [X4,X0] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 2.28/0.96    inference(cnf_transformation,[],[f23])).
% 2.28/0.96  
% 2.28/0.96  fof(f7,conjecture,(
% 2.28/0.96    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 2.28/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f8,negated_conjecture,(
% 2.28/0.96    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 2.28/0.96    inference(negated_conjecture,[],[f7])).
% 2.28/0.96  
% 2.28/0.96  fof(f16,plain,(
% 2.28/0.96    ? [X0,X1] : ((~r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) & v1_relat_1(X1))),
% 2.28/0.96    inference(ennf_transformation,[],[f8])).
% 2.28/0.96  
% 2.28/0.96  fof(f28,plain,(
% 2.28/0.96    ? [X0,X1] : ((~r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) & v1_relat_1(X1)) => ((~r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) | ~r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)) & v1_relat_1(sK5))),
% 2.28/0.96    introduced(choice_axiom,[])).
% 2.28/0.96  
% 2.28/0.96  fof(f29,plain,(
% 2.28/0.96    (~r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) | ~r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)) & v1_relat_1(sK5)),
% 2.28/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f28])).
% 2.28/0.96  
% 2.28/0.96  fof(f44,plain,(
% 2.28/0.96    ~r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) | ~r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),
% 2.28/0.96    inference(cnf_transformation,[],[f29])).
% 2.28/0.96  
% 2.28/0.96  fof(f43,plain,(
% 2.28/0.96    v1_relat_1(sK5)),
% 2.28/0.96    inference(cnf_transformation,[],[f29])).
% 2.28/0.96  
% 2.28/0.96  fof(f4,axiom,(
% 2.28/0.96    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.28/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f36,plain,(
% 2.28/0.96    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.28/0.96    inference(cnf_transformation,[],[f4])).
% 2.28/0.96  
% 2.28/0.96  fof(f5,axiom,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 2.28/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f14,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 2.28/0.96    inference(ennf_transformation,[],[f5])).
% 2.28/0.96  
% 2.28/0.96  fof(f24,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 2.28/0.96    inference(nnf_transformation,[],[f14])).
% 2.28/0.96  
% 2.28/0.96  fof(f25,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 2.28/0.96    inference(flattening,[],[f24])).
% 2.28/0.96  
% 2.28/0.96  fof(f37,plain,(
% 2.28/0.96    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X3)) )),
% 2.28/0.96    inference(cnf_transformation,[],[f25])).
% 2.28/0.96  
% 2.28/0.96  fof(f31,plain,(
% 2.28/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.28/0.96    inference(cnf_transformation,[],[f18])).
% 2.28/0.96  
% 2.28/0.96  fof(f38,plain,(
% 2.28/0.96    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X3)) )),
% 2.28/0.96    inference(cnf_transformation,[],[f25])).
% 2.28/0.96  
% 2.28/0.96  fof(f6,axiom,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 2.28/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.96  
% 2.28/0.96  fof(f15,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 2.28/0.96    inference(ennf_transformation,[],[f6])).
% 2.28/0.96  
% 2.28/0.96  fof(f26,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 2.28/0.96    inference(nnf_transformation,[],[f15])).
% 2.28/0.96  
% 2.28/0.96  fof(f27,plain,(
% 2.28/0.96    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 2.28/0.96    inference(flattening,[],[f26])).
% 2.28/0.96  
% 2.28/0.96  fof(f41,plain,(
% 2.28/0.96    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~v1_relat_1(X3)) )),
% 2.28/0.96    inference(cnf_transformation,[],[f27])).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1,plain,
% 2.28/0.96      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.28/0.96      inference(cnf_transformation,[],[f30]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_460,plain,
% 2.28/0.96      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.28/0.96      | r1_tarski(X0,X1) = iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_5,plain,
% 2.28/0.96      ( ~ v1_relat_1(X0)
% 2.28/0.96      | ~ v1_relat_1(X1)
% 2.28/0.96      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 2.28/0.96      inference(cnf_transformation,[],[f35]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_456,plain,
% 2.28/0.96      ( v1_relat_1(X0) != iProver_top
% 2.28/0.96      | v1_relat_1(X1) != iProver_top
% 2.28/0.96      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_4,plain,
% 2.28/0.96      ( ~ r2_hidden(X0,X1)
% 2.28/0.96      | ~ v1_relat_1(X1)
% 2.28/0.96      | k4_tarski(sK2(X0),sK3(X0)) = X0 ),
% 2.28/0.96      inference(cnf_transformation,[],[f32]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_457,plain,
% 2.28/0.96      ( k4_tarski(sK2(X0),sK3(X0)) = X0
% 2.28/0.96      | r2_hidden(X0,X1) != iProver_top
% 2.28/0.96      | v1_relat_1(X1) != iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_771,plain,
% 2.28/0.96      ( k4_tarski(sK2(sK0(X0,X1)),sK3(sK0(X0,X1))) = sK0(X0,X1)
% 2.28/0.96      | r1_tarski(X0,X1) = iProver_top
% 2.28/0.96      | v1_relat_1(X0) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_460,c_457]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_13,negated_conjecture,
% 2.28/0.96      ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
% 2.28/0.96      | ~ r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
% 2.28/0.96      inference(cnf_transformation,[],[f44]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_448,plain,
% 2.28/0.96      ( r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) != iProver_top
% 2.28/0.96      | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) != iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1193,plain,
% 2.28/0.96      ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
% 2.28/0.96      | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) != iProver_top
% 2.28/0.96      | v1_relat_1(k5_relat_1(k6_relat_1(sK4),sK5)) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_771,c_448]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1199,plain,
% 2.28/0.96      ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
% 2.28/0.96      | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.96      | v1_relat_1(k5_relat_1(k6_relat_1(sK4),sK5)) != iProver_top
% 2.28/0.96      | v1_relat_1(k5_relat_1(sK5,k6_relat_1(sK4))) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_771,c_1193]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1208,plain,
% 2.28/0.96      ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
% 2.28/0.96      | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.96      | v1_relat_1(k5_relat_1(sK5,k6_relat_1(sK4))) != iProver_top
% 2.28/0.96      | v1_relat_1(k6_relat_1(sK4)) != iProver_top
% 2.28/0.96      | v1_relat_1(sK5) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_456,c_1199]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_14,negated_conjecture,
% 2.28/0.96      ( v1_relat_1(sK5) ),
% 2.28/0.96      inference(cnf_transformation,[],[f43]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_15,plain,
% 2.28/0.96      ( v1_relat_1(sK5) = iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_674,plain,
% 2.28/0.96      ( v1_relat_1(k5_relat_1(sK5,k6_relat_1(sK4)))
% 2.28/0.96      | ~ v1_relat_1(k6_relat_1(sK4))
% 2.28/0.96      | ~ v1_relat_1(sK5) ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_5]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_675,plain,
% 2.28/0.96      ( v1_relat_1(k5_relat_1(sK5,k6_relat_1(sK4))) = iProver_top
% 2.28/0.96      | v1_relat_1(k6_relat_1(sK4)) != iProver_top
% 2.28/0.96      | v1_relat_1(sK5) != iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_936,plain,
% 2.28/0.96      ( v1_relat_1(k5_relat_1(k6_relat_1(sK4),sK5))
% 2.28/0.96      | ~ v1_relat_1(k6_relat_1(sK4))
% 2.28/0.96      | ~ v1_relat_1(sK5) ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_5]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_937,plain,
% 2.28/0.96      ( v1_relat_1(k5_relat_1(k6_relat_1(sK4),sK5)) = iProver_top
% 2.28/0.96      | v1_relat_1(k6_relat_1(sK4)) != iProver_top
% 2.28/0.96      | v1_relat_1(sK5) != iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1211,plain,
% 2.28/0.96      ( v1_relat_1(k6_relat_1(sK4)) != iProver_top
% 2.28/0.96      | k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
% 2.28/0.96      | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
% 2.28/0.96      inference(global_propositional_subsumption,
% 2.28/0.96                [status(thm)],
% 2.28/0.96                [c_1208,c_15,c_675,c_937,c_1199]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1212,plain,
% 2.28/0.96      ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
% 2.28/0.96      | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.96      | v1_relat_1(k6_relat_1(sK4)) != iProver_top ),
% 2.28/0.96      inference(renaming,[status(thm)],[c_1211]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_6,plain,
% 2.28/0.96      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.28/0.96      inference(cnf_transformation,[],[f36]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_455,plain,
% 2.28/0.96      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1218,plain,
% 2.28/0.96      ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
% 2.28/0.96      | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
% 2.28/0.96      inference(forward_subsumption_resolution,
% 2.28/0.96                [status(thm)],
% 2.28/0.96                [c_1212,c_455]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_9,plain,
% 2.28/0.96      ( r2_hidden(X0,X1)
% 2.28/0.96      | ~ r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
% 2.28/0.96      | ~ v1_relat_1(X3) ),
% 2.28/0.96      inference(cnf_transformation,[],[f37]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_452,plain,
% 2.28/0.96      ( r2_hidden(X0,X1) = iProver_top
% 2.28/0.96      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3)) != iProver_top
% 2.28/0.96      | v1_relat_1(X3) != iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1225,plain,
% 2.28/0.96      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.96      | r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),k5_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 2.28/0.96      | r2_hidden(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),X0) = iProver_top
% 2.28/0.96      | v1_relat_1(X1) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_1218,c_452]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1362,plain,
% 2.28/0.96      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.96      | r2_hidden(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK4) = iProver_top
% 2.28/0.96      | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
% 2.28/0.96      | v1_relat_1(sK5) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_460,c_1225]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1772,plain,
% 2.28/0.96      ( r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
% 2.28/0.96      | r2_hidden(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK4) = iProver_top
% 2.28/0.96      | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
% 2.28/0.96      inference(global_propositional_subsumption,
% 2.28/0.96                [status(thm)],
% 2.28/0.96                [c_1362,c_15]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1773,plain,
% 2.28/0.96      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.96      | r2_hidden(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK4) = iProver_top
% 2.28/0.96      | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top ),
% 2.28/0.96      inference(renaming,[status(thm)],[c_1772]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_1779,plain,
% 2.28/0.96      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.96      | k4_tarski(sK2(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),sK3(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)))) = sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))
% 2.28/0.96      | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
% 2.28/0.96      | v1_relat_1(sK4) != iProver_top ),
% 2.28/0.96      inference(superposition,[status(thm)],[c_1773,c_457]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_0,plain,
% 2.28/0.96      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.28/0.96      inference(cnf_transformation,[],[f31]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_571,plain,
% 2.28/0.96      ( ~ r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),sK5)
% 2.28/0.96      | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) ),
% 2.28/0.96      inference(instantiation,[status(thm)],[c_0]) ).
% 2.28/0.96  
% 2.28/0.96  cnf(c_572,plain,
% 2.28/0.96      ( r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),sK5) != iProver_top
% 2.28/0.96      | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top ),
% 2.28/0.96      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_8,plain,
% 2.28/0.97      ( r2_hidden(k4_tarski(X0,X1),X2)
% 2.28/0.97      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2))
% 2.28/0.97      | ~ v1_relat_1(X2) ),
% 2.28/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_453,plain,
% 2.28/0.97      ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
% 2.28/0.97      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2)) != iProver_top
% 2.28/0.97      | v1_relat_1(X2) != iProver_top ),
% 2.28/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1219,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.97      | r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),X0) = iProver_top
% 2.28/0.97      | r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),k5_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 2.28/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_1218,c_453]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1590,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.97      | r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),sK5) = iProver_top
% 2.28/0.97      | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
% 2.28/0.97      | v1_relat_1(sK5) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_460,c_1219]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1802,plain,
% 2.28/0.97      ( r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
% 2.28/0.97      | r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),sK5) = iProver_top
% 2.28/0.97      | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
% 2.28/0.97      inference(global_propositional_subsumption,
% 2.28/0.97                [status(thm)],
% 2.28/0.97                [c_1590,c_15]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1803,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.97      | r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),sK5) = iProver_top
% 2.28/0.97      | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top ),
% 2.28/0.97      inference(renaming,[status(thm)],[c_1802]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1809,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.97      | r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),sK5) = iProver_top
% 2.28/0.97      | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_1218,c_1803]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1904,plain,
% 2.28/0.97      ( r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
% 2.28/0.97      | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
% 2.28/0.97      inference(global_propositional_subsumption,
% 2.28/0.97                [status(thm)],
% 2.28/0.97                [c_1779,c_572,c_1809]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1905,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.97      | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top ),
% 2.28/0.97      inference(renaming,[status(thm)],[c_1904]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1910,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.97      | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_1905,c_448]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1915,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.97      | v1_relat_1(k5_relat_1(sK5,k6_relat_1(sK4))) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_771,c_1910]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1978,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.97      | v1_relat_1(k6_relat_1(sK4)) != iProver_top
% 2.28/0.97      | v1_relat_1(sK5) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_456,c_1915]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1981,plain,
% 2.28/0.97      ( v1_relat_1(k6_relat_1(sK4)) != iProver_top
% 2.28/0.97      | k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
% 2.28/0.97      inference(global_propositional_subsumption,
% 2.28/0.97                [status(thm)],
% 2.28/0.97                [c_1978,c_15]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1982,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)
% 2.28/0.97      | v1_relat_1(k6_relat_1(sK4)) != iProver_top ),
% 2.28/0.97      inference(renaming,[status(thm)],[c_1981]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1987,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))) = sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
% 2.28/0.97      inference(forward_subsumption_resolution,
% 2.28/0.97                [status(thm)],
% 2.28/0.97                [c_1982,c_455]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_11,plain,
% 2.28/0.97      ( r2_hidden(k4_tarski(X0,X1),X2)
% 2.28/0.97      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,k6_relat_1(X3)))
% 2.28/0.97      | ~ v1_relat_1(X2) ),
% 2.28/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_450,plain,
% 2.28/0.97      ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
% 2.28/0.97      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,k6_relat_1(X3))) != iProver_top
% 2.28/0.97      | v1_relat_1(X2) != iProver_top ),
% 2.28/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_1989,plain,
% 2.28/0.97      ( r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5)),sK3(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5))),X0) = iProver_top
% 2.28/0.97      | r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
% 2.28/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_1987,c_450]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2062,plain,
% 2.28/0.97      ( r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),X0) = iProver_top
% 2.28/0.97      | r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),k5_relat_1(X0,k6_relat_1(X1))) != iProver_top
% 2.28/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.28/0.97      inference(light_normalisation,[status(thm)],[c_1989,c_1987]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2161,plain,
% 2.28/0.97      ( r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),sK5) = iProver_top
% 2.28/0.97      | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) = iProver_top
% 2.28/0.97      | v1_relat_1(sK5) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_460,c_2062]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_593,plain,
% 2.28/0.97      ( ~ r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),sK5)
% 2.28/0.97      | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) ),
% 2.28/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_594,plain,
% 2.28/0.97      ( r2_hidden(sK0(k5_relat_1(sK5,k6_relat_1(sK4)),sK5),sK5) != iProver_top
% 2.28/0.97      | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) = iProver_top ),
% 2.28/0.97      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2344,plain,
% 2.28/0.97      ( r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) = iProver_top ),
% 2.28/0.97      inference(global_propositional_subsumption,
% 2.28/0.97                [status(thm)],
% 2.28/0.97                [c_2161,c_15,c_594]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2349,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
% 2.28/0.97      | v1_relat_1(k5_relat_1(k6_relat_1(sK4),sK5)) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_2344,c_1193]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2362,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)
% 2.28/0.97      | v1_relat_1(k6_relat_1(sK4)) != iProver_top
% 2.28/0.97      | v1_relat_1(sK5) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_456,c_2349]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2363,plain,
% 2.28/0.97      ( ~ v1_relat_1(k6_relat_1(sK4))
% 2.28/0.97      | ~ v1_relat_1(sK5)
% 2.28/0.97      | k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5) ),
% 2.28/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2362]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2457,plain,
% 2.28/0.97      ( v1_relat_1(k6_relat_1(sK4)) ),
% 2.28/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2483,plain,
% 2.28/0.97      ( k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))) = sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5) ),
% 2.28/0.97      inference(global_propositional_subsumption,
% 2.28/0.97                [status(thm)],
% 2.28/0.97                [c_2362,c_14,c_2363,c_2457]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2486,plain,
% 2.28/0.97      ( r2_hidden(k4_tarski(sK2(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5)),sK3(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5))),X0) = iProver_top
% 2.28/0.97      | r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),k5_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 2.28/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_2483,c_453]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2567,plain,
% 2.28/0.97      ( r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),X0) = iProver_top
% 2.28/0.97      | r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),k5_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 2.28/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.28/0.97      inference(light_normalisation,[status(thm)],[c_2486,c_2483]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_2661,plain,
% 2.28/0.97      ( r2_hidden(sK0(k5_relat_1(k6_relat_1(sK4),sK5),sK5),sK5) = iProver_top
% 2.28/0.97      | r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) = iProver_top
% 2.28/0.97      | v1_relat_1(sK5) != iProver_top ),
% 2.28/0.97      inference(superposition,[status(thm)],[c_460,c_2567]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(c_16,plain,
% 2.28/0.97      ( r1_tarski(k5_relat_1(k6_relat_1(sK4),sK5),sK5) != iProver_top
% 2.28/0.97      | r1_tarski(k5_relat_1(sK5,k6_relat_1(sK4)),sK5) != iProver_top ),
% 2.28/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.28/0.97  
% 2.28/0.97  cnf(contradiction,plain,
% 2.28/0.97      ( $false ),
% 2.28/0.97      inference(minisat,[status(thm)],[c_2661,c_2344,c_572,c_16,c_15]) ).
% 2.28/0.97  
% 2.28/0.97  
% 2.28/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.28/0.97  
% 2.28/0.97  ------                               Statistics
% 2.28/0.97  
% 2.28/0.97  ------ General
% 2.28/0.97  
% 2.28/0.97  abstr_ref_over_cycles:                  0
% 2.28/0.97  abstr_ref_under_cycles:                 0
% 2.28/0.97  gc_basic_clause_elim:                   0
% 2.28/0.97  forced_gc_time:                         0
% 2.28/0.97  parsing_time:                           0.009
% 2.28/0.97  unif_index_cands_time:                  0.
% 2.28/0.97  unif_index_add_time:                    0.
% 2.28/0.97  orderings_time:                         0.
% 2.28/0.97  out_proof_time:                         0.008
% 2.28/0.97  total_time:                             0.122
% 2.28/0.97  num_of_symbols:                         43
% 2.28/0.97  num_of_terms:                           1999
% 2.28/0.97  
% 2.28/0.97  ------ Preprocessing
% 2.28/0.97  
% 2.28/0.97  num_of_splits:                          0
% 2.28/0.97  num_of_split_atoms:                     0
% 2.28/0.97  num_of_reused_defs:                     0
% 2.28/0.97  num_eq_ax_congr_red:                    10
% 2.28/0.97  num_of_sem_filtered_clauses:            1
% 2.28/0.97  num_of_subtypes:                        0
% 2.28/0.97  monotx_restored_types:                  0
% 2.28/0.97  sat_num_of_epr_types:                   0
% 2.28/0.97  sat_num_of_non_cyclic_types:            0
% 2.28/0.97  sat_guarded_non_collapsed_types:        0
% 2.28/0.97  num_pure_diseq_elim:                    0
% 2.28/0.97  simp_replaced_by:                       0
% 2.28/0.97  res_preprocessed:                       62
% 2.28/0.97  prep_upred:                             0
% 2.28/0.97  prep_unflattend:                        0
% 2.28/0.97  smt_new_axioms:                         0
% 2.28/0.97  pred_elim_cands:                        3
% 2.28/0.97  pred_elim:                              0
% 2.28/0.97  pred_elim_cl:                           0
% 2.28/0.97  pred_elim_cycles:                       1
% 2.28/0.97  merged_defs:                            0
% 2.28/0.97  merged_defs_ncl:                        0
% 2.28/0.97  bin_hyper_res:                          0
% 2.28/0.97  prep_cycles:                            3
% 2.28/0.97  pred_elim_time:                         0.
% 2.28/0.97  splitting_time:                         0.
% 2.28/0.97  sem_filter_time:                        0.
% 2.28/0.97  monotx_time:                            0.001
% 2.28/0.97  subtype_inf_time:                       0.
% 2.28/0.97  
% 2.28/0.97  ------ Problem properties
% 2.28/0.97  
% 2.28/0.97  clauses:                                15
% 2.28/0.97  conjectures:                            2
% 2.28/0.97  epr:                                    1
% 2.28/0.97  horn:                                   13
% 2.28/0.97  ground:                                 2
% 2.28/0.97  unary:                                  2
% 2.28/0.97  binary:                                 5
% 2.28/0.97  lits:                                   38
% 2.28/0.97  lits_eq:                                2
% 2.28/0.97  fd_pure:                                0
% 2.28/0.97  fd_pseudo:                              0
% 2.28/0.97  fd_cond:                                0
% 2.28/0.97  fd_pseudo_cond:                         0
% 2.28/0.97  ac_symbols:                             0
% 2.28/0.97  
% 2.28/0.97  ------ Propositional Solver
% 2.28/0.97  
% 2.28/0.97  prop_solver_calls:                      25
% 2.28/0.97  prop_fast_solver_calls:                 527
% 2.28/0.97  smt_solver_calls:                       0
% 2.28/0.97  smt_fast_solver_calls:                  0
% 2.28/0.97  prop_num_of_clauses:                    769
% 2.28/0.97  prop_preprocess_simplified:             2905
% 2.28/0.97  prop_fo_subsumed:                       16
% 2.28/0.97  prop_solver_time:                       0.
% 2.28/0.97  smt_solver_time:                        0.
% 2.28/0.97  smt_fast_solver_time:                   0.
% 2.28/0.97  prop_fast_solver_time:                  0.
% 2.28/0.97  prop_unsat_core_time:                   0.
% 2.28/0.97  
% 2.28/0.97  ------ QBF
% 2.28/0.97  
% 2.28/0.97  qbf_q_res:                              0
% 2.28/0.97  qbf_num_tautologies:                    0
% 2.28/0.97  qbf_prep_cycles:                        0
% 2.28/0.97  
% 2.28/0.97  ------ BMC1
% 2.28/0.97  
% 2.28/0.97  bmc1_current_bound:                     -1
% 2.28/0.97  bmc1_last_solved_bound:                 -1
% 2.28/0.97  bmc1_unsat_core_size:                   -1
% 2.28/0.97  bmc1_unsat_core_parents_size:           -1
% 2.28/0.97  bmc1_merge_next_fun:                    0
% 2.28/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.28/0.97  
% 2.28/0.97  ------ Instantiation
% 2.28/0.97  
% 2.28/0.97  inst_num_of_clauses:                    240
% 2.28/0.97  inst_num_in_passive:                    18
% 2.28/0.97  inst_num_in_active:                     186
% 2.28/0.97  inst_num_in_unprocessed:                37
% 2.28/0.97  inst_num_of_loops:                      260
% 2.28/0.97  inst_num_of_learning_restarts:          0
% 2.28/0.97  inst_num_moves_active_passive:          67
% 2.28/0.97  inst_lit_activity:                      0
% 2.28/0.97  inst_lit_activity_moves:                0
% 2.28/0.97  inst_num_tautologies:                   0
% 2.28/0.97  inst_num_prop_implied:                  0
% 2.28/0.97  inst_num_existing_simplified:           0
% 2.28/0.97  inst_num_eq_res_simplified:             0
% 2.28/0.97  inst_num_child_elim:                    0
% 2.28/0.97  inst_num_of_dismatching_blockings:      131
% 2.28/0.97  inst_num_of_non_proper_insts:           326
% 2.28/0.97  inst_num_of_duplicates:                 0
% 2.28/0.97  inst_inst_num_from_inst_to_res:         0
% 2.28/0.97  inst_dismatching_checking_time:         0.
% 2.28/0.97  
% 2.28/0.97  ------ Resolution
% 2.28/0.97  
% 2.28/0.97  res_num_of_clauses:                     0
% 2.28/0.97  res_num_in_passive:                     0
% 2.28/0.97  res_num_in_active:                      0
% 2.28/0.97  res_num_of_loops:                       65
% 2.28/0.97  res_forward_subset_subsumed:            61
% 2.28/0.97  res_backward_subset_subsumed:           2
% 2.28/0.97  res_forward_subsumed:                   0
% 2.28/0.97  res_backward_subsumed:                  0
% 2.28/0.97  res_forward_subsumption_resolution:     0
% 2.28/0.97  res_backward_subsumption_resolution:    0
% 2.28/0.97  res_clause_to_clause_subsumption:       222
% 2.28/0.97  res_orphan_elimination:                 0
% 2.28/0.97  res_tautology_del:                      52
% 2.28/0.97  res_num_eq_res_simplified:              0
% 2.28/0.97  res_num_sel_changes:                    0
% 2.28/0.97  res_moves_from_active_to_pass:          0
% 2.28/0.97  
% 2.28/0.97  ------ Superposition
% 2.28/0.97  
% 2.28/0.97  sup_time_total:                         0.
% 2.28/0.97  sup_time_generating:                    0.
% 2.28/0.97  sup_time_sim_full:                      0.
% 2.28/0.97  sup_time_sim_immed:                     0.
% 2.28/0.97  
% 2.28/0.97  sup_num_of_clauses:                     48
% 2.28/0.97  sup_num_in_active:                      33
% 2.28/0.97  sup_num_in_passive:                     15
% 2.28/0.97  sup_num_of_loops:                       51
% 2.28/0.97  sup_fw_superposition:                   14
% 2.28/0.97  sup_bw_superposition:                   53
% 2.28/0.97  sup_immediate_simplified:               14
% 2.28/0.97  sup_given_eliminated:                   0
% 2.28/0.97  comparisons_done:                       0
% 2.28/0.97  comparisons_avoided:                    6
% 2.28/0.97  
% 2.28/0.97  ------ Simplifications
% 2.28/0.97  
% 2.28/0.97  
% 2.28/0.97  sim_fw_subset_subsumed:                 0
% 2.28/0.97  sim_bw_subset_subsumed:                 26
% 2.28/0.97  sim_fw_subsumed:                        2
% 2.28/0.97  sim_bw_subsumed:                        0
% 2.28/0.97  sim_fw_subsumption_res:                 10
% 2.28/0.97  sim_bw_subsumption_res:                 0
% 2.28/0.97  sim_tautology_del:                      5
% 2.28/0.97  sim_eq_tautology_del:                   0
% 2.28/0.97  sim_eq_res_simp:                        0
% 2.28/0.97  sim_fw_demodulated:                     0
% 2.28/0.97  sim_bw_demodulated:                     0
% 2.28/0.97  sim_light_normalised:                   12
% 2.28/0.97  sim_joinable_taut:                      0
% 2.28/0.97  sim_joinable_simp:                      0
% 2.28/0.97  sim_ac_normalised:                      0
% 2.28/0.97  sim_smt_subsumption:                    0
% 2.28/0.97  
%------------------------------------------------------------------------------
