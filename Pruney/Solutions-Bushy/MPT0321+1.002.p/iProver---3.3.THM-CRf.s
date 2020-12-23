%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0321+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:00 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 538 expanded)
%              Number of clauses        :   66 ( 198 expanded)
%              Number of leaves         :   10 ( 126 expanded)
%              Depth                    :   18
%              Number of atoms          :  268 (1761 expanded)
%              Number of equality atoms :  194 (1176 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f19])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f23])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f12])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK3 != sK5
        | sK2 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( sK3 != sK5
      | sK2 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f21])).

fof(f32,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f33,f23])).

fof(f34,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    o_0_0_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f34,f23])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,
    ( sK3 != sK5
    | sK2 != sK4 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_286,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_291,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,negated_conjecture,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_290,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_589,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_290])).

cnf(c_813,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_291,c_589])).

cnf(c_1088,plain,
    ( sK2 = o_0_0_xboole_0
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_286,c_813])).

cnf(c_10,negated_conjecture,
    ( o_0_0_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_160,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_167,plain,
    ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_161,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_359,plain,
    ( sK2 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_360,plain,
    ( sK2 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1486,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1088,c_10,c_167,c_360])).

cnf(c_1494,plain,
    ( sK3 = o_0_0_xboole_0
    | r2_hidden(sK1(sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_286,c_1486])).

cnf(c_9,negated_conjecture,
    ( o_0_0_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_357,plain,
    ( sK3 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_358,plain,
    ( sK3 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_1647,plain,
    ( r2_hidden(sK1(sK3),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1494,c_9,c_167,c_358])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_289,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_450,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_289])).

cnf(c_812,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_291,c_450])).

cnf(c_1050,plain,
    ( sK2 = o_0_0_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK1(sK2),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_286,c_812])).

cnf(c_1612,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK1(sK2),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1050,c_10,c_167,c_360])).

cnf(c_1620,plain,
    ( sK3 = o_0_0_xboole_0
    | r2_hidden(sK1(sK2),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_286,c_1612])).

cnf(c_1829,plain,
    ( r2_hidden(sK1(sK2),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1620,c_9,c_167,c_358])).

cnf(c_809,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_291])).

cnf(c_845,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(X1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_290])).

cnf(c_1835,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1829,c_845])).

cnf(c_2140,plain,
    ( r2_hidden(sK1(sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1647,c_1835])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_287,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1052,plain,
    ( sK2 = X0
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(sK0(sK2,X0),X0) = iProver_top
    | r2_hidden(sK0(sK2,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_287,c_812])).

cnf(c_3327,plain,
    ( sK2 = X0
    | r2_hidden(sK0(sK2,X0),X0) = iProver_top
    | r2_hidden(sK0(sK2,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2140,c_1052])).

cnf(c_10734,plain,
    ( sK4 = sK2
    | r2_hidden(sK0(sK2,sK4),sK4) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3327])).

cnf(c_10736,plain,
    ( sK4 = sK2
    | r2_hidden(sK0(sK2,sK4),sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10734])).

cnf(c_846,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_289])).

cnf(c_1256,plain,
    ( sK4 = X0
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(sK0(X0,sK4),X0) = iProver_top
    | r2_hidden(sK0(X0,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_287,c_846])).

cnf(c_3133,plain,
    ( sK4 = X0
    | r2_hidden(sK0(X0,sK4),X0) = iProver_top
    | r2_hidden(sK0(X0,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1647,c_1256])).

cnf(c_10081,plain,
    ( sK4 = sK2
    | r2_hidden(sK0(sK2,sK4),sK2) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3133])).

cnf(c_10083,plain,
    ( sK4 = sK2
    | r2_hidden(sK0(sK2,sK4),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10081])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_594,plain,
    ( ~ r2_hidden(sK0(X0,sK5),X0)
    | ~ r2_hidden(sK0(X0,sK5),sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4346,plain,
    ( ~ r2_hidden(sK0(sK3,sK5),sK5)
    | ~ r2_hidden(sK0(sK3,sK5),sK3)
    | sK5 = sK3 ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_4349,plain,
    ( sK5 = sK3
    | r2_hidden(sK0(sK3,sK5),sK5) != iProver_top
    | r2_hidden(sK0(sK3,sK5),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4346])).

cnf(c_2136,plain,
    ( sK5 = X0
    | r2_hidden(sK0(X0,sK5),X0) = iProver_top
    | r2_hidden(sK0(X0,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_287,c_1835])).

cnf(c_4288,plain,
    ( sK5 = sK3
    | r2_hidden(sK0(sK3,sK5),sK3) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2136])).

cnf(c_4290,plain,
    ( sK5 = sK3
    | r2_hidden(sK0(sK3,sK5),sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4288])).

cnf(c_1496,plain,
    ( sK3 = X0
    | r2_hidden(sK0(sK3,X0),X0) = iProver_top
    | r2_hidden(sK0(sK3,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_287,c_1486])).

cnf(c_4214,plain,
    ( sK5 = sK3
    | r2_hidden(sK0(sK3,sK5),sK5) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1496])).

cnf(c_4216,plain,
    ( sK5 = sK3
    | r2_hidden(sK0(sK3,sK5),sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4214])).

cnf(c_355,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_2182,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_434,plain,
    ( ~ r2_hidden(sK0(X0,sK4),X0)
    | ~ r2_hidden(sK0(X0,sK4),sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1425,plain,
    ( ~ r2_hidden(sK0(sK2,sK4),sK4)
    | ~ r2_hidden(sK0(sK2,sK4),sK2)
    | sK4 = sK2 ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_1431,plain,
    ( sK4 = sK2
    | r2_hidden(sK0(sK2,sK4),sK4) != iProver_top
    | r2_hidden(sK0(sK2,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1425])).

cnf(c_399,plain,
    ( sK5 != X0
    | sK3 != X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_1159,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_517,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_488,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_8,negated_conjecture,
    ( sK2 != sK4
    | sK3 != sK5 ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10736,c_10083,c_4349,c_4290,c_4216,c_2182,c_1431,c_1159,c_517,c_488,c_8])).


%------------------------------------------------------------------------------
