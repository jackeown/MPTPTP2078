%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1030+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Theorem 38.96s
% Output     : CNFRefutation 38.96s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 536 expanded)
%              Number of clauses        :   36 ( 147 expanded)
%              Number of leaves         :    7 ( 114 expanded)
%              Depth                    :   17
%              Number of atoms          :  215 (2327 expanded)
%              Number of equality atoms :  112 ( 892 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1521,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1522,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1521])).

fof(f3155,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1522])).

fof(f3156,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f3155])).

fof(f4525,plain,
    ( ? [X0,X1,X2] :
        ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ v1_partfun1(k3_partfun1(sK531,sK529,sK530),sK529)
      & ( k1_xboole_0 = sK529
        | k1_xboole_0 != sK530 )
      & m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
      & v1_funct_2(sK531,sK529,sK530)
      & v1_funct_1(sK531) ) ),
    introduced(choice_axiom,[])).

fof(f4526,plain,
    ( ~ v1_partfun1(k3_partfun1(sK531,sK529,sK530),sK529)
    & ( k1_xboole_0 = sK529
      | k1_xboole_0 != sK530 )
    & m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
    & v1_funct_2(sK531,sK529,sK530)
    & v1_funct_1(sK531) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK529,sK530,sK531])],[f3156,f4525])).

fof(f7415,plain,(
    m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) ),
    inference(cnf_transformation,[],[f4526])).

fof(f1520,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3153,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1520])).

fof(f3154,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3153])).

fof(f7411,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3154])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4575,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8615,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7411,f4575])).

fof(f7413,plain,(
    v1_funct_1(sK531) ),
    inference(cnf_transformation,[],[f4526])).

fof(f7414,plain,(
    v1_funct_2(sK531,sK529,sK530) ),
    inference(cnf_transformation,[],[f4526])).

fof(f1579,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3268,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1579])).

fof(f3269,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3268])).

fof(f7552,plain,(
    ! [X2,X0,X1] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3269])).

fof(f7417,plain,(
    ~ v1_partfun1(k3_partfun1(sK531,sK529,sK530),sK529) ),
    inference(cnf_transformation,[],[f4526])).

fof(f7416,plain,
    ( k1_xboole_0 = sK529
    | k1_xboole_0 != sK530 ),
    inference(cnf_transformation,[],[f4526])).

fof(f8616,plain,
    ( o_0_0_xboole_0 = sK529
    | o_0_0_xboole_0 != sK530 ),
    inference(definition_unfolding,[],[f7416,f4575,f4575])).

fof(f7412,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3154])).

fof(f8614,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | o_0_0_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7412,f4575])).

fof(f9015,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,o_0_0_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_2(X2,o_0_0_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f8614])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3484,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f3485,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f3484])).

fof(f5031,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f3485])).

fof(f7857,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f5031,f4575,f4575])).

fof(f8754,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f7857])).

fof(f376,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5110,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f7905,plain,(
    k1_tarski(o_0_0_xboole_0) = k1_zfmisc_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f5110,f4575,f4575])).

fof(f5032,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f3485])).

fof(f7856,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f5032,f4575,f4575])).

fof(f8753,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f7856])).

cnf(c_2823,negated_conjecture,
    ( m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) ),
    inference(cnf_transformation,[],[f7415])).

cnf(c_85250,plain,
    ( m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2823])).

cnf(c_2820,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f8615])).

cnf(c_85252,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2820])).

cnf(c_111014,plain,
    ( sK530 = o_0_0_xboole_0
    | v1_funct_2(sK531,sK529,sK530) != iProver_top
    | v1_partfun1(sK531,sK529) = iProver_top
    | v1_funct_1(sK531) != iProver_top ),
    inference(superposition,[status(thm)],[c_85250,c_85252])).

cnf(c_2825,negated_conjecture,
    ( v1_funct_1(sK531) ),
    inference(cnf_transformation,[],[f7413])).

cnf(c_2977,plain,
    ( v1_funct_1(sK531) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_2824,negated_conjecture,
    ( v1_funct_2(sK531,sK529,sK530) ),
    inference(cnf_transformation,[],[f7414])).

cnf(c_2978,plain,
    ( v1_funct_2(sK531,sK529,sK530) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2824])).

cnf(c_2960,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_partfun1(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f7552])).

cnf(c_85127,plain,
    ( k3_partfun1(X0,X1,X2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2960])).

cnf(c_110892,plain,
    ( k3_partfun1(sK531,sK529,sK530) = sK531
    | v1_funct_1(sK531) != iProver_top ),
    inference(superposition,[status(thm)],[c_85250,c_85127])).

cnf(c_110932,plain,
    ( k3_partfun1(sK531,sK529,sK530) = sK531 ),
    inference(global_propositional_subsumption,[status(thm)],[c_110892,c_2977])).

cnf(c_2821,negated_conjecture,
    ( ~ v1_partfun1(k3_partfun1(sK531,sK529,sK530),sK529) ),
    inference(cnf_transformation,[],[f7417])).

cnf(c_85251,plain,
    ( v1_partfun1(k3_partfun1(sK531,sK529,sK530),sK529) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2821])).

cnf(c_110935,plain,
    ( v1_partfun1(sK531,sK529) != iProver_top ),
    inference(demodulation,[status(thm)],[c_110932,c_85251])).

cnf(c_111068,plain,
    ( sK530 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_111014,c_2977,c_2978,c_110935])).

cnf(c_85249,plain,
    ( v1_funct_2(sK531,sK529,sK530) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2824])).

cnf(c_111073,plain,
    ( v1_funct_2(sK531,sK529,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_111068,c_85249])).

cnf(c_2822,negated_conjecture,
    ( o_0_0_xboole_0 != sK530
    | o_0_0_xboole_0 = sK529 ),
    inference(cnf_transformation,[],[f8616])).

cnf(c_111074,plain,
    ( sK529 = o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_111068,c_2822])).

cnf(c_111075,plain,
    ( sK529 = o_0_0_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_111074])).

cnf(c_111078,plain,
    ( v1_funct_2(sK531,o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_111073,c_111075])).

cnf(c_2819,plain,
    ( ~ v1_funct_2(X0,o_0_0_xboole_0,X1)
    | v1_partfun1(X0,o_0_0_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f9015])).

cnf(c_85253,plain,
    ( v1_funct_2(X0,o_0_0_xboole_0,X1) != iProver_top
    | v1_partfun1(X0,o_0_0_xboole_0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2819])).

cnf(c_451,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f8754])).

cnf(c_530,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = k1_tarski(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7905])).

cnf(c_95511,plain,
    ( v1_funct_2(X0,o_0_0_xboole_0,X1) != iProver_top
    | v1_partfun1(X0,o_0_0_xboole_0) = iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_85253,c_451,c_530])).

cnf(c_116777,plain,
    ( v1_partfun1(sK531,o_0_0_xboole_0) = iProver_top
    | m1_subset_1(sK531,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(sK531) != iProver_top ),
    inference(superposition,[status(thm)],[c_111078,c_95511])).

cnf(c_450,plain,
    ( k2_zfmisc_1(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f8753])).

cnf(c_111072,plain,
    ( m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,o_0_0_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_111068,c_85250])).

cnf(c_111081,plain,
    ( m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_111072,c_111075])).

cnf(c_111194,plain,
    ( m1_subset_1(sK531,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_450,c_111081])).

cnf(c_111276,plain,
    ( m1_subset_1(sK531,k1_tarski(o_0_0_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_111194,c_530])).

cnf(c_111090,plain,
    ( v1_partfun1(sK531,o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_111075,c_110935])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_116777,c_111276,c_111090,c_2977])).

%------------------------------------------------------------------------------
