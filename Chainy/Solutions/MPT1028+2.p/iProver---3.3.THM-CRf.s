%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1028+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Theorem 35.32s
% Output     : CNFRefutation 35.32s
% Verified   : 
% Statistics : Number of formulae       :   27 (  53 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 262 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1517,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1518,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f1517])).

fof(f3142,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & v1_partfun1(X2,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1518])).

fof(f3143,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & v1_partfun1(X2,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f3142])).

fof(f4510,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & v1_partfun1(X2,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
        | ~ v1_funct_2(sK531,sK529,sK530)
        | ~ v1_funct_1(sK531) )
      & v1_partfun1(sK531,sK529)
      & m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
      & v1_funct_1(sK531) ) ),
    introduced(choice_axiom,[])).

fof(f4511,plain,
    ( ( ~ m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
      | ~ v1_funct_2(sK531,sK529,sK530)
      | ~ v1_funct_1(sK531) )
    & v1_partfun1(sK531,sK529)
    & m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
    & v1_funct_1(sK531) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK529,sK530,sK531])],[f3143,f4510])).

fof(f7391,plain,(
    m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) ),
    inference(cnf_transformation,[],[f4511])).

fof(f1468,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3071,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1468])).

fof(f3072,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f3071])).

fof(f7258,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f3072])).

fof(f7393,plain,
    ( ~ m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
    | ~ v1_funct_2(sK531,sK529,sK530)
    | ~ v1_funct_1(sK531) ),
    inference(cnf_transformation,[],[f4511])).

fof(f7392,plain,(
    v1_partfun1(sK531,sK529) ),
    inference(cnf_transformation,[],[f4511])).

fof(f7390,plain,(
    v1_funct_1(sK531) ),
    inference(cnf_transformation,[],[f4511])).

cnf(c_2815,negated_conjecture,
    ( m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) ),
    inference(cnf_transformation,[],[f7391])).

cnf(c_85054,plain,
    ( m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2815])).

cnf(c_2681,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f7258])).

cnf(c_85175,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2681])).

cnf(c_113036,plain,
    ( v1_funct_2(sK531,sK529,sK530) = iProver_top
    | v1_partfun1(sK531,sK529) != iProver_top
    | v1_funct_1(sK531) != iProver_top ),
    inference(superposition,[status(thm)],[c_85054,c_85175])).

cnf(c_2813,negated_conjecture,
    ( ~ v1_funct_2(sK531,sK529,sK530)
    | ~ m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530)))
    | ~ v1_funct_1(sK531) ),
    inference(cnf_transformation,[],[f7393])).

cnf(c_2970,plain,
    ( v1_funct_2(sK531,sK529,sK530) != iProver_top
    | m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) != iProver_top
    | v1_funct_1(sK531) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2813])).

cnf(c_2814,negated_conjecture,
    ( v1_partfun1(sK531,sK529) ),
    inference(cnf_transformation,[],[f7392])).

cnf(c_2969,plain,
    ( v1_partfun1(sK531,sK529) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2814])).

cnf(c_2968,plain,
    ( m1_subset_1(sK531,k1_zfmisc_1(k2_zfmisc_1(sK529,sK530))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2815])).

cnf(c_2816,negated_conjecture,
    ( v1_funct_1(sK531) ),
    inference(cnf_transformation,[],[f7390])).

cnf(c_2967,plain,
    ( v1_funct_1(sK531) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2816])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_113036,c_2970,c_2969,c_2968,c_2967])).

%------------------------------------------------------------------------------
