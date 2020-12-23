%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1029+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Theorem 35.07s
% Output     : CNFRefutation 35.07s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 106 expanded)
%              Number of clauses        :   27 (  31 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 516 expanded)
%              Number of equality atoms :   56 ( 148 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1518,conjecture,(
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

fof(f1519,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) )
         => ( v1_partfun1(X2,X0)
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1518])).

fof(f3145,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1519])).

fof(f3146,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f3145])).

fof(f4513,plain,
    ( ? [X0,X1,X2] :
        ( ~ v1_partfun1(X2,X0)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ v1_partfun1(sK531,sK529)
      & ( k1_xboole_0 = sK529
        | k1_xboole_0 != sK530 )
      & m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
      & v1_funct_2(sK531,sK529,sK530)
      & v1_funct_1(sK531)
      & m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
      & v1_funct_1(sK531) ) ),
    introduced(choice_axiom,[])).

fof(f4514,plain,
    ( ~ v1_partfun1(sK531,sK529)
    & ( k1_xboole_0 = sK529
      | k1_xboole_0 != sK530 )
    & m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
    & v1_funct_2(sK531,sK529,sK530)
    & v1_funct_1(sK531)
    & m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
    & v1_funct_1(sK531) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK529,sK530,sK531])],[f3146,f4513])).

fof(f7397,plain,(
    m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) ),
    inference(cnf_transformation,[],[f4514])).

fof(f1469,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3074,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1469])).

fof(f7262,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3074])).

fof(f7402,plain,(
    ~ v1_partfun1(sK531,sK529) ),
    inference(cnf_transformation,[],[f4514])).

fof(f7401,plain,
    ( k1_xboole_0 = sK529
    | k1_xboole_0 != sK530 ),
    inference(cnf_transformation,[],[f4514])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4563,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8598,plain,
    ( o_0_0_xboole_0 = sK529
    | o_0_0_xboole_0 != sK530 ),
    inference(definition_unfolding,[],[f7401,f4563,f4563])).

fof(f7396,plain,(
    v1_funct_1(sK531) ),
    inference(cnf_transformation,[],[f4514])).

fof(f7399,plain,(
    v1_funct_2(sK531,sK529,sK530) ),
    inference(cnf_transformation,[],[f4514])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1694,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f4738,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1694])).

fof(f7680,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f4738,f4563])).

fof(f1475,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3085,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1475])).

fof(f3086,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f3085])).

fof(f7275,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f3086])).

fof(f1429,axiom,
    ( v1_xboole_0(k1_wellord2(k1_xboole_0))
    & v1_relat_1(k1_wellord2(k1_xboole_0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7147,plain,(
    v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f1429])).

fof(f8566,plain,(
    v1_xboole_0(k1_wellord2(o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f7147,f4563])).

fof(f1430,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( ~ v1_xboole_0(k1_wellord2(X0))
        & v1_relat_1(k1_wellord2(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3033,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(k1_wellord2(X0))
        & v1_relat_1(k1_wellord2(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1430])).

fof(f7149,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_wellord2(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3033])).

cnf(c_2821,negated_conjecture,
    ( m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) ),
    inference(cnf_transformation,[],[f7397])).

cnf(c_85076,plain,
    ( m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2821])).

cnf(c_2683,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f7262])).

cnf(c_85196,plain,
    ( v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2683])).

cnf(c_111027,plain,
    ( v1_partfun1(sK531,sK529) = iProver_top
    | v1_xboole_0(sK529) != iProver_top ),
    inference(superposition,[status(thm)],[c_85076,c_85196])).

cnf(c_2816,negated_conjecture,
    ( ~ v1_partfun1(sK531,sK529) ),
    inference(cnf_transformation,[],[f7402])).

cnf(c_2978,plain,
    ( v1_partfun1(sK531,sK529) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2816])).

cnf(c_112156,plain,
    ( v1_xboole_0(sK529) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_111027,c_2978])).

cnf(c_2817,negated_conjecture,
    ( o_0_0_xboole_0 != sK530
    | o_0_0_xboole_0 = sK529 ),
    inference(cnf_transformation,[],[f8598])).

cnf(c_2822,negated_conjecture,
    ( v1_funct_1(sK531) ),
    inference(cnf_transformation,[],[f7396])).

cnf(c_2973,plain,
    ( v1_funct_1(sK531) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2822])).

cnf(c_2819,negated_conjecture,
    ( v1_funct_2(sK531,sK529,sK530) ),
    inference(cnf_transformation,[],[f7399])).

cnf(c_2976,plain,
    ( v1_funct_2(sK531,sK529,sK530) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2819])).

cnf(c_181,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f7680])).

cnf(c_110680,plain,
    ( ~ v1_xboole_0(sK530)
    | o_0_0_xboole_0 = sK530 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_110681,plain,
    ( o_0_0_xboole_0 = sK530
    | v1_xboole_0(sK530) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_110680])).

cnf(c_2695,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f7275])).

cnf(c_85189,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2695])).

cnf(c_110863,plain,
    ( v1_funct_2(sK531,sK529,sK530) != iProver_top
    | v1_partfun1(sK531,sK529) = iProver_top
    | v1_funct_1(sK531) != iProver_top
    | v1_xboole_0(sK530) = iProver_top ),
    inference(superposition,[status(thm)],[c_85076,c_85189])).

cnf(c_111330,negated_conjecture,
    ( o_0_0_xboole_0 = sK529 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2817,c_2973,c_2976,c_2978,c_110681,c_110863])).

cnf(c_112160,plain,
    ( v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_112156,c_111330])).

cnf(c_2567,plain,
    ( v1_xboole_0(k1_wellord2(o_0_0_xboole_0)) ),
    inference(cnf_transformation,[],[f8566])).

cnf(c_4067,plain,
    ( v1_xboole_0(k1_wellord2(o_0_0_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_2569,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f7149])).

cnf(c_4063,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_wellord2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2569])).

cnf(c_4065,plain,
    ( v1_xboole_0(k1_wellord2(o_0_0_xboole_0)) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4063])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_112160,c_4067,c_4065])).

%------------------------------------------------------------------------------
