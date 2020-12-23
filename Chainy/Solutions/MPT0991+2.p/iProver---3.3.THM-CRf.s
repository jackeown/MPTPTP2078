%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0991+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Theorem 39.78s
% Output     : CNFRefutation 39.78s
% Verified   : 
% Statistics : Number of formulae       :   39 (  88 expanded)
%              Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :    4 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  154 ( 651 expanded)
%              Number of equality atoms :   30 (  79 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1511,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ v2_funct_1(X2)
          & ? [X3] :
              ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1512,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ~ ( ~ v2_funct_1(X2)
            & ? [X3] :
                ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f1511])).

fof(f3076,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1512])).

fof(f3077,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f3076])).

fof(f4361,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK541),k6_partfun1(X0))
        & m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK541,X1,X0)
        & v1_funct_1(sK541) ) ) ),
    introduced(choice_axiom,[])).

fof(f4360,plain,
    ( ? [X0,X1,X2] :
        ( ~ v2_funct_1(X2)
        & ? [X3] :
            ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(sK540)
      & ? [X3] :
          ( r2_relset_1(sK538,sK538,k1_partfun1(sK538,sK539,sK539,sK538,sK540,X3),k6_partfun1(sK538))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK539,sK538)))
          & v1_funct_2(X3,sK539,sK538)
          & v1_funct_1(X3) )
      & k1_xboole_0 != sK539
      & m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539)))
      & v1_funct_2(sK540,sK538,sK539)
      & v1_funct_1(sK540) ) ),
    introduced(choice_axiom,[])).

fof(f4362,plain,
    ( ~ v2_funct_1(sK540)
    & r2_relset_1(sK538,sK538,k1_partfun1(sK538,sK539,sK539,sK538,sK540,sK541),k6_partfun1(sK538))
    & m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK538)))
    & v1_funct_2(sK541,sK539,sK538)
    & v1_funct_1(sK541)
    & k1_xboole_0 != sK539
    & m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539)))
    & v1_funct_2(sK540,sK538,sK539)
    & v1_funct_1(sK540) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK538,sK539,sK540,sK541])],[f3077,f4361,f4360])).

fof(f7220,plain,(
    r2_relset_1(sK538,sK538,k1_partfun1(sK538,sK539,sK539,sK538,sK540,sK541),k6_partfun1(sK538)) ),
    inference(cnf_transformation,[],[f4362])).

fof(f1503,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3060,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1503])).

fof(f3061,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3060])).

fof(f7193,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3061])).

fof(f7221,plain,(
    ~ v2_funct_1(sK540) ),
    inference(cnf_transformation,[],[f4362])).

fof(f7219,plain,(
    m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK538))) ),
    inference(cnf_transformation,[],[f4362])).

fof(f7218,plain,(
    v1_funct_2(sK541,sK539,sK538) ),
    inference(cnf_transformation,[],[f4362])).

fof(f7217,plain,(
    v1_funct_1(sK541) ),
    inference(cnf_transformation,[],[f4362])).

fof(f7215,plain,(
    m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) ),
    inference(cnf_transformation,[],[f4362])).

fof(f7214,plain,(
    v1_funct_2(sK540,sK538,sK539) ),
    inference(cnf_transformation,[],[f4362])).

fof(f7213,plain,(
    v1_funct_1(sK540) ),
    inference(cnf_transformation,[],[f4362])).

cnf(c_2825,negated_conjecture,
    ( r2_relset_1(sK538,sK538,k1_partfun1(sK538,sK539,sK539,sK538,sK540,sK541),k6_partfun1(sK538)) ),
    inference(cnf_transformation,[],[f7220])).

cnf(c_140754,plain,
    ( r2_relset_1(sK538,sK538,k1_partfun1(sK538,sK539,sK539,sK538,sK540,sK541),k6_partfun1(sK538)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_2805,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f7193])).

cnf(c_140770,plain,
    ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v2_funct_1(X2) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2805])).

cnf(c_159186,plain,
    ( v1_funct_2(sK541,sK539,sK538) != iProver_top
    | v1_funct_2(sK540,sK538,sK539) != iProver_top
    | m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK538))) != iProver_top
    | m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) != iProver_top
    | v2_funct_1(sK540) = iProver_top
    | v1_funct_1(sK541) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_140754,c_140770])).

cnf(c_2824,negated_conjecture,
    ( ~ v2_funct_1(sK540) ),
    inference(cnf_transformation,[],[f7221])).

cnf(c_2866,plain,
    ( v2_funct_1(sK540) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2824])).

cnf(c_2826,negated_conjecture,
    ( m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK538))) ),
    inference(cnf_transformation,[],[f7219])).

cnf(c_2864,plain,
    ( m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK538))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2826])).

cnf(c_2827,negated_conjecture,
    ( v1_funct_2(sK541,sK539,sK538) ),
    inference(cnf_transformation,[],[f7218])).

cnf(c_2863,plain,
    ( v1_funct_2(sK541,sK539,sK538) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2827])).

cnf(c_2828,negated_conjecture,
    ( v1_funct_1(sK541) ),
    inference(cnf_transformation,[],[f7217])).

cnf(c_2862,plain,
    ( v1_funct_1(sK541) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2828])).

cnf(c_2830,negated_conjecture,
    ( m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) ),
    inference(cnf_transformation,[],[f7215])).

cnf(c_2861,plain,
    ( m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK538,sK539))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2830])).

cnf(c_2831,negated_conjecture,
    ( v1_funct_2(sK540,sK538,sK539) ),
    inference(cnf_transformation,[],[f7214])).

cnf(c_2860,plain,
    ( v1_funct_2(sK540,sK538,sK539) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2831])).

cnf(c_2832,negated_conjecture,
    ( v1_funct_1(sK540) ),
    inference(cnf_transformation,[],[f7213])).

cnf(c_2859,plain,
    ( v1_funct_1(sK540) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2832])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_159186,c_2866,c_2864,c_2863,c_2862,c_2861,c_2860,c_2859])).

%------------------------------------------------------------------------------
