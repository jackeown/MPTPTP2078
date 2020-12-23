%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0592+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 18.66s
% Output     : CNFRefutation 18.66s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 199 expanded)
%              Number of clauses        :   39 (  51 expanded)
%              Number of leaves         :   13 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  188 ( 627 expanded)
%              Number of equality atoms :  122 ( 395 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f786,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k1_relat_1(X1)
              & k1_xboole_0 = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f787,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k1_relat_1(X1)
                & k1_xboole_0 = k1_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f786])).

fof(f1453,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f787])).

fof(f1454,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1453])).

fof(f1992,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
     => ( sK162 != X0
        & k1_xboole_0 = k1_relat_1(sK162)
        & k1_xboole_0 = k1_relat_1(X0)
        & v1_relat_1(sK162) ) ) ),
    introduced(choice_axiom,[])).

fof(f1991,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k1_xboole_0 = k1_relat_1(X1)
            & k1_xboole_0 = k1_relat_1(X0)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK161 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(sK161)
          & v1_relat_1(X1) )
      & v1_relat_1(sK161) ) ),
    introduced(choice_axiom,[])).

fof(f1993,plain,
    ( sK161 != sK162
    & k1_xboole_0 = k1_relat_1(sK162)
    & k1_xboole_0 = k1_relat_1(sK161)
    & v1_relat_1(sK162)
    & v1_relat_1(sK161) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK161,sK162])],[f1454,f1992,f1991])).

fof(f3227,plain,(
    k1_xboole_0 = k1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f1993])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2015,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3865,plain,(
    o_0_0_xboole_0 = k1_relat_1(sK162) ),
    inference(definition_unfolding,[],[f3227,f2015])).

fof(f849,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1529,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f849])).

fof(f2007,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1529])).

fof(f3310,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2007])).

fof(f3893,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3310,f2015])).

fof(f851,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1531,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f851])).

fof(f1532,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1531])).

fof(f3312,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1532])).

fof(f3225,plain,(
    v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f1993])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2141,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f3405,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2141,f2015])).

fof(f3226,plain,(
    k1_xboole_0 = k1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f1993])).

fof(f3866,plain,(
    o_0_0_xboole_0 = k1_relat_1(sK161) ),
    inference(definition_unfolding,[],[f3226,f2015])).

fof(f3224,plain,(
    v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f1993])).

fof(f703,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3128,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f703])).

fof(f3830,plain,(
    ! [X0] : o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f3128,f2015,f2015])).

fof(f3309,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2007])).

fof(f3894,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | o_0_0_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3309,f2015])).

fof(f821,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3268,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f821])).

fof(f3881,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f3268,f2015,f2015])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2764,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2701,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f3325,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2701,f2015])).

fof(f3742,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2764,f3325])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1290,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f3012,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1290])).

fof(f3228,plain,(
    sK161 != sK162 ),
    inference(cnf_transformation,[],[f1993])).

cnf(c_1203,negated_conjecture,
    ( o_0_0_xboole_0 = k1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f3865])).

cnf(c_1287,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3893])).

cnf(c_52625,plain,
    ( k7_relat_1(X0,X1) = o_0_0_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1287])).

cnf(c_64231,plain,
    ( k7_relat_1(sK162,X0) = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(sK162) != iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_52625])).

cnf(c_1290,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f3312])).

cnf(c_52622,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1290])).

cnf(c_63304,plain,
    ( k7_relat_1(sK162,X0) = sK162
    | r1_tarski(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(sK162) != iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_52622])).

cnf(c_1205,negated_conjecture,
    ( v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f3225])).

cnf(c_1294,plain,
    ( v1_relat_1(sK162) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1205])).

cnf(c_133,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3405])).

cnf(c_3705,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_63729,plain,
    ( k7_relat_1(sK162,X0) = sK162 ),
    inference(global_propositional_subsumption,[status(thm)],[c_63304,c_1294,c_3705])).

cnf(c_64258,plain,
    ( sK162 = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(sK162) != iProver_top ),
    inference(demodulation,[status(thm)],[c_64231,c_63729])).

cnf(c_1204,negated_conjecture,
    ( o_0_0_xboole_0 = k1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f3866])).

cnf(c_64232,plain,
    ( k7_relat_1(sK161,X0) = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(sK161) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_52625])).

cnf(c_63305,plain,
    ( k7_relat_1(sK161,X0) = sK161
    | r1_tarski(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(sK161) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_52622])).

cnf(c_1206,negated_conjecture,
    ( v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f3224])).

cnf(c_1293,plain,
    ( v1_relat_1(sK161) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1206])).

cnf(c_63735,plain,
    ( k7_relat_1(sK161,X0) = sK161 ),
    inference(global_propositional_subsumption,[status(thm)],[c_63305,c_1293,c_3705])).

cnf(c_64251,plain,
    ( sK161 = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(sK161) != iProver_top ),
    inference(demodulation,[status(thm)],[c_64232,c_63735])).

cnf(c_1106,plain,
    ( k7_relat_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3830])).

cnf(c_1288,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3894])).

cnf(c_52624,plain,
    ( k7_relat_1(X0,X1) != o_0_0_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_63792,plain,
    ( r1_xboole_0(k1_relat_1(o_0_0_xboole_0),X0) = iProver_top
    | v1_relat_1(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1106,c_52624])).

cnf(c_1247,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3881])).

cnf(c_63827,plain,
    ( r1_xboole_0(o_0_0_xboole_0,X0) = iProver_top
    | v1_relat_1(o_0_0_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_63792,c_1247])).

cnf(c_34030,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_63760,plain,
    ( sK162 != X0
    | sK161 != X0
    | sK161 = sK162 ),
    inference(instantiation,[status(thm)],[c_34030])).

cnf(c_63761,plain,
    ( sK162 != o_0_0_xboole_0
    | sK161 = sK162
    | sK161 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_63760])).

cnf(c_743,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3742])).

cnf(c_2649,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_990,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f3012])).

cnf(c_2039,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_990])).

cnf(c_2041,plain,
    ( v1_relat_1(o_0_0_xboole_0) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2039])).

cnf(c_1202,negated_conjecture,
    ( sK161 != sK162 ),
    inference(cnf_transformation,[],[f3228])).

cnf(c_64272,plain,
    ( sK162 = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | v1_relat_1(sK162) != iProver_top ),
    inference(grounding,[status(thm)],[c_64258:[bind(X0,$fot(o_0_0_xboole_0))]])).

cnf(c_64273,plain,
    ( sK161 = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | v1_relat_1(sK161) != iProver_top ),
    inference(grounding,[status(thm)],[c_64251:[bind(X0,$fot(o_0_0_xboole_0))]])).

cnf(c_64274,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top
    | v1_relat_1(o_0_0_xboole_0) != iProver_top ),
    inference(grounding,[status(thm)],[c_63827:[bind(X0,$fot(o_0_0_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_64272,c_64273,c_64274,c_63761,c_2649,c_2041,c_1202,c_1294,c_1293])).

%------------------------------------------------------------------------------
