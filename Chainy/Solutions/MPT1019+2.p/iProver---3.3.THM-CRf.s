%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1019+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Theorem 51.84s
% Output     : CNFRefutation 51.84s
% Verified   : 
% Statistics : Number of formulae       :   42 (  98 expanded)
%              Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :    5 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  206 ( 862 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1470,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3059,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1470])).

fof(f3060,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f3059])).

fof(f7215,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f3060])).

fof(f1560,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
           => r2_relset_1(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1561,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
             => r2_relset_1(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1560])).

fof(f3216,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1561])).

fof(f3217,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f3216])).

fof(f4505,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK545),sK545)
        & m1_subset_1(sK545,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK545,X0,X0)
        & v1_funct_2(sK545,X0,X0)
        & v1_funct_1(sK545) ) ) ),
    introduced(choice_axiom,[])).

fof(f4504,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,k6_partfun1(X0))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK543,sK543,sK544,k6_partfun1(sK543))
          & r2_relset_1(sK543,sK543,k1_partfun1(sK543,sK543,sK543,sK543,sK544,X2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543)))
          & v3_funct_2(X2,sK543,sK543)
          & v1_funct_2(X2,sK543,sK543)
          & v1_funct_1(X2) )
      & m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543)))
      & v3_funct_2(sK544,sK543,sK543)
      & v1_funct_2(sK544,sK543,sK543)
      & v1_funct_1(sK544) ) ),
    introduced(choice_axiom,[])).

fof(f4506,plain,
    ( ~ r2_relset_1(sK543,sK543,sK544,k6_partfun1(sK543))
    & r2_relset_1(sK543,sK543,k1_partfun1(sK543,sK543,sK543,sK543,sK544,sK545),sK545)
    & m1_subset_1(sK545,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543)))
    & v3_funct_2(sK545,sK543,sK543)
    & v1_funct_2(sK545,sK543,sK543)
    & v1_funct_1(sK545)
    & m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543)))
    & v3_funct_2(sK544,sK543,sK543)
    & v1_funct_2(sK544,sK543,sK543)
    & v1_funct_1(sK544) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK543,sK544,sK545])],[f3217,f4505,f4504])).

fof(f7460,plain,(
    r2_relset_1(sK543,sK543,k1_partfun1(sK543,sK543,sK543,sK543,sK544,sK545),sK545) ),
    inference(cnf_transformation,[],[f4506])).

fof(f1555,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3206,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          | ~ v2_funct_1(X1)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v1_funct_2(X2,X0,X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1555])).

fof(f3207,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          | ~ v2_funct_1(X1)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v1_funct_2(X2,X0,X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f3206])).

fof(f7440,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X0,X2,k6_partfun1(X0))
      | ~ v2_funct_1(X1)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f3207])).

fof(f7461,plain,(
    ~ r2_relset_1(sK543,sK543,sK544,k6_partfun1(sK543)) ),
    inference(cnf_transformation,[],[f4506])).

fof(f7459,plain,(
    m1_subset_1(sK545,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543))) ),
    inference(cnf_transformation,[],[f4506])).

fof(f7458,plain,(
    v3_funct_2(sK545,sK543,sK543) ),
    inference(cnf_transformation,[],[f4506])).

fof(f7457,plain,(
    v1_funct_2(sK545,sK543,sK543) ),
    inference(cnf_transformation,[],[f4506])).

fof(f7456,plain,(
    v1_funct_1(sK545) ),
    inference(cnf_transformation,[],[f4506])).

fof(f7455,plain,(
    m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543))) ),
    inference(cnf_transformation,[],[f4506])).

fof(f7453,plain,(
    v1_funct_2(sK544,sK543,sK543) ),
    inference(cnf_transformation,[],[f4506])).

fof(f7452,plain,(
    v1_funct_1(sK544) ),
    inference(cnf_transformation,[],[f4506])).

cnf(c_2685,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f7215])).

cnf(c_134036,plain,
    ( ~ v3_funct_2(sK545,X0,X1)
    | ~ m1_subset_1(sK545,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK545)
    | ~ v1_funct_1(sK545) ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_184273,plain,
    ( ~ v3_funct_2(sK545,sK543,sK543)
    | ~ m1_subset_1(sK545,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543)))
    | v2_funct_1(sK545)
    | ~ v1_funct_1(sK545) ),
    inference(instantiation,[status(thm)],[c_134036])).

cnf(c_2922,negated_conjecture,
    ( r2_relset_1(sK543,sK543,k1_partfun1(sK543,sK543,sK543,sK543,sK544,sK545),sK545) ),
    inference(cnf_transformation,[],[f7460])).

cnf(c_84261,plain,
    ( r2_relset_1(sK543,sK543,k1_partfun1(sK543,sK543,sK543,sK543,sK544,sK545),sK545) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2922])).

cnf(c_2909,plain,
    ( r2_relset_1(X0,X0,X1,k6_partfun1(X0))
    | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2)
    | ~ v1_funct_2(X2,X0,X0)
    | ~ v1_funct_2(X1,X0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f7440])).

cnf(c_84271,plain,
    ( r2_relset_1(X0,X0,X1,k6_partfun1(X0)) = iProver_top
    | r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X2) != iProver_top
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v1_funct_2(X2,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2909])).

cnf(c_119658,plain,
    ( r2_relset_1(sK543,sK543,sK544,k6_partfun1(sK543)) = iProver_top
    | v1_funct_2(sK545,sK543,sK543) != iProver_top
    | v1_funct_2(sK544,sK543,sK543) != iProver_top
    | m1_subset_1(sK545,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543))) != iProver_top
    | m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543))) != iProver_top
    | v2_funct_1(sK545) != iProver_top
    | v1_funct_1(sK545) != iProver_top
    | v1_funct_1(sK544) != iProver_top ),
    inference(superposition,[status(thm)],[c_84261,c_84271])).

cnf(c_119659,plain,
    ( r2_relset_1(sK543,sK543,sK544,k6_partfun1(sK543))
    | ~ v1_funct_2(sK545,sK543,sK543)
    | ~ v1_funct_2(sK544,sK543,sK543)
    | ~ m1_subset_1(sK545,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543)))
    | ~ m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543)))
    | ~ v2_funct_1(sK545)
    | ~ v1_funct_1(sK545)
    | ~ v1_funct_1(sK544) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_119658])).

cnf(c_2921,negated_conjecture,
    ( ~ r2_relset_1(sK543,sK543,sK544,k6_partfun1(sK543)) ),
    inference(cnf_transformation,[],[f7461])).

cnf(c_2923,negated_conjecture,
    ( m1_subset_1(sK545,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543))) ),
    inference(cnf_transformation,[],[f7459])).

cnf(c_2924,negated_conjecture,
    ( v3_funct_2(sK545,sK543,sK543) ),
    inference(cnf_transformation,[],[f7458])).

cnf(c_2925,negated_conjecture,
    ( v1_funct_2(sK545,sK543,sK543) ),
    inference(cnf_transformation,[],[f7457])).

cnf(c_2926,negated_conjecture,
    ( v1_funct_1(sK545) ),
    inference(cnf_transformation,[],[f7456])).

cnf(c_2927,negated_conjecture,
    ( m1_subset_1(sK544,k1_zfmisc_1(k2_zfmisc_1(sK543,sK543))) ),
    inference(cnf_transformation,[],[f7455])).

cnf(c_2929,negated_conjecture,
    ( v1_funct_2(sK544,sK543,sK543) ),
    inference(cnf_transformation,[],[f7453])).

cnf(c_2930,negated_conjecture,
    ( v1_funct_1(sK544) ),
    inference(cnf_transformation,[],[f7452])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_184273,c_119659,c_2921,c_2923,c_2924,c_2925,c_2926,c_2927,c_2929,c_2930])).

%------------------------------------------------------------------------------
