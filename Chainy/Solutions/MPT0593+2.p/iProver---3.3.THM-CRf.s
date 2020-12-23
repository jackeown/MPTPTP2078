%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0593+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 18.50s
% Output     : CNFRefutation 18.50s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 201 expanded)
%              Number of clauses        :   46 (  59 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  238 ( 667 expanded)
%              Number of equality atoms :  141 ( 406 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f829,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3283,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f829])).

fof(f787,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k1_xboole_0 = k2_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f788,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k2_relat_1(X1)
                & k1_xboole_0 = k2_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f787])).

fof(f1456,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f788])).

fof(f1457,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1456])).

fof(f1995,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
     => ( sK162 != X0
        & k1_xboole_0 = k2_relat_1(sK162)
        & k1_xboole_0 = k2_relat_1(X0)
        & v1_relat_1(sK162) ) ) ),
    introduced(choice_axiom,[])).

fof(f1994,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k1_xboole_0 = k2_relat_1(X1)
            & k1_xboole_0 = k2_relat_1(X0)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK161 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(sK161)
          & v1_relat_1(X1) )
      & v1_relat_1(sK161) ) ),
    introduced(choice_axiom,[])).

fof(f1996,plain,
    ( sK161 != sK162
    & k1_xboole_0 = k2_relat_1(sK162)
    & k1_xboole_0 = k2_relat_1(sK161)
    & v1_relat_1(sK162)
    & v1_relat_1(sK161) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK161,sK162])],[f1457,f1995,f1994])).

fof(f3230,plain,(
    k1_xboole_0 = k2_relat_1(sK161) ),
    inference(cnf_transformation,[],[f1996])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2018,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3871,plain,(
    o_0_0_xboole_0 = k2_relat_1(sK161) ),
    inference(definition_unfolding,[],[f3230,f2018])).

fof(f828,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
           => k1_xboole_0 = k5_relat_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1507,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f828])).

fof(f1508,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1507])).

fof(f3282,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_relat_1(X0,X1)
      | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1508])).

fof(f3895,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k5_relat_1(X0,X1)
      | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3282,f2018])).

fof(f3228,plain,(
    v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f1996])).

fof(f837,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1517,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f837])).

fof(f1518,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1517])).

fof(f3298,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1518])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2144,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f3409,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2144,f2018])).

fof(f3231,plain,(
    k1_xboole_0 = k2_relat_1(sK162) ),
    inference(cnf_transformation,[],[f1996])).

fof(f3870,plain,(
    o_0_0_xboole_0 = k2_relat_1(sK162) ),
    inference(definition_unfolding,[],[f3231,f2018])).

fof(f3229,plain,(
    v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f1996])).

fof(f511,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1153,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f511])).

fof(f1810,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f1153])).

fof(f2820,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1810])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2704,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f3329,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2704,f2018])).

fof(f3760,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | o_0_0_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f2820,f3329])).

fof(f4033,plain,(
    ! [X0] :
      ( r1_tarski(o_0_0_xboole_0,k3_subset_1(X0,o_0_0_xboole_0))
      | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f3760])).

fof(f516,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1159,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f516])).

fof(f1812,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f1159])).

fof(f2827,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1812])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2836,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f3765,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f2836,f2018])).

fof(f661,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3082,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f661])).

fof(f3232,plain,(
    sK161 != sK162 ),
    inference(cnf_transformation,[],[f1996])).

cnf(c_1259,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3283])).

cnf(c_1205,negated_conjecture,
    ( o_0_0_xboole_0 = k2_relat_1(sK161) ),
    inference(cnf_transformation,[],[f3871])).

cnf(c_1257,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3895])).

cnf(c_52685,plain,
    ( k5_relat_1(X0,X1) = o_0_0_xboole_0
    | r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_65164,plain,
    ( k5_relat_1(sK161,X0) = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK161) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_52685])).

cnf(c_1207,negated_conjecture,
    ( v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f3228])).

cnf(c_1294,plain,
    ( v1_relat_1(sK161) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_65443,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_xboole_0(o_0_0_xboole_0,k1_relat_1(X0)) != iProver_top
    | k5_relat_1(sK161,X0) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_65164,c_1294])).

cnf(c_65444,plain,
    ( k5_relat_1(sK161,X0) = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_65443])).

cnf(c_65453,plain,
    ( k5_relat_1(sK161,k6_relat_1(X0)) = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_65444])).

cnf(c_1273,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f3298])).

cnf(c_52672,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_64369,plain,
    ( k5_relat_1(sK161,k6_relat_1(X0)) = sK161
    | r1_tarski(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(sK161) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_52672])).

cnf(c_133,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3409])).

cnf(c_3707,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_64895,plain,
    ( k5_relat_1(sK161,k6_relat_1(X0)) = sK161 ),
    inference(global_propositional_subsumption,[status(thm)],[c_64369,c_1294,c_3707])).

cnf(c_65457,plain,
    ( sK161 = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_65453,c_64895])).

cnf(c_65469,plain,
    ( sK161 = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(o_0_0_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_65457])).

cnf(c_1204,negated_conjecture,
    ( o_0_0_xboole_0 = k2_relat_1(sK162) ),
    inference(cnf_transformation,[],[f3870])).

cnf(c_65163,plain,
    ( k5_relat_1(sK162,X0) = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK162) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_52685])).

cnf(c_1206,negated_conjecture,
    ( v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f3229])).

cnf(c_1295,plain,
    ( v1_relat_1(sK162) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1206])).

cnf(c_65347,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_xboole_0(o_0_0_xboole_0,k1_relat_1(X0)) != iProver_top
    | k5_relat_1(sK162,X0) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_65163,c_1295])).

cnf(c_65348,plain,
    ( k5_relat_1(sK162,X0) = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_65347])).

cnf(c_65357,plain,
    ( k5_relat_1(sK162,k6_relat_1(X0)) = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_65348])).

cnf(c_64368,plain,
    ( k5_relat_1(sK162,k6_relat_1(X0)) = sK162
    | r1_tarski(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(sK162) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_52672])).

cnf(c_64870,plain,
    ( k5_relat_1(sK162,k6_relat_1(X0)) = sK162 ),
    inference(global_propositional_subsumption,[status(thm)],[c_64368,c_1295,c_3707])).

cnf(c_65361,plain,
    ( sK162 = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_65357,c_64870])).

cnf(c_65373,plain,
    ( sK162 = o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(o_0_0_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_65361])).

cnf(c_34047,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_63726,plain,
    ( sK162 != X0
    | sK161 != X0
    | sK161 = sK162 ),
    inference(instantiation,[status(thm)],[c_34047])).

cnf(c_63727,plain,
    ( sK162 != o_0_0_xboole_0
    | sK161 = sK162
    | sK161 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_63726])).

cnf(c_794,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))
    | r1_tarski(o_0_0_xboole_0,k3_subset_1(X0,o_0_0_xboole_0)) ),
    inference(cnf_transformation,[],[f4033])).

cnf(c_2530,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(o_0_0_xboole_0,k3_subset_1(X0,o_0_0_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_2532,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) != iProver_top
    | r1_tarski(o_0_0_xboole_0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2530])).

cnf(c_801,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_xboole_0(X2,X0)
    | ~ r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f2827])).

cnf(c_2509,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X2,X0) = iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_2511,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) != iProver_top
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top
    | r1_tarski(o_0_0_xboole_0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2509])).

cnf(c_811,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3765])).

cnf(c_2485,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_2487,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2485])).

cnf(c_1057,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3082])).

cnf(c_1898,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_1900,plain,
    ( v1_relat_1(k6_relat_1(o_0_0_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1898])).

cnf(c_1203,negated_conjecture,
    ( sK161 != sK162 ),
    inference(cnf_transformation,[],[f3232])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65469,c_65373,c_63727,c_2532,c_2511,c_2487,c_1900,c_1203])).

%------------------------------------------------------------------------------
