%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:05 EST 2020

% Result     : Theorem 43.70s
% Output     : CNFRefutation 43.70s
% Verified   : 
% Statistics : Number of formulae       :  348 (14769 expanded)
%              Number of clauses        :  238 (3919 expanded)
%              Number of leaves         :   27 (3843 expanded)
%              Depth                    :   35
%              Number of atoms          : 1146 (111066 expanded)
%              Number of equality atoms :  642 (6747 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,conjecture,(
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
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,negated_conjecture,(
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
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f37])).

fof(f83,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f84,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f83])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK3,X0,X0)
        & v1_funct_2(sK3,X0,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2))
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v3_funct_2(X2,sK1,sK1)
          & v1_funct_2(X2,sK1,sK1)
          & v1_funct_1(X2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v3_funct_2(sK2,sK1,sK1)
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK3,sK1,sK1)
    & v1_funct_2(sK3,sK1,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f84,f92,f91])).

fof(f153,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f93])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f67])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f71])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f72])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f150,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

fof(f152,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f93])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f81])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f151,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f93])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f79])).

fof(f146,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f75])).

fof(f143,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f77])).

fof(f145,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f140,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f73])).

fof(f139,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f157,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f93])).

fof(f154,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

fof(f138,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f63])).

fof(f88,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f158,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f93])).

fof(f32,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f32])).

fof(f144,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f142,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f112,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f35,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f147,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f161,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f112,f147])).

fof(f156,plain,(
    v3_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f93])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f155,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f93])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f110,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f164,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f121])).

fof(f159,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f93])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f69])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f70])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f111,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f160,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f111,f147])).

cnf(c_61,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_3182,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_3207,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6457,plain,
    ( k7_relset_1(sK1,sK1,sK2,sK1) = k2_relset_1(sK1,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3182,c_3207])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3210,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5892,plain,
    ( k7_relset_1(sK1,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_3182,c_3210])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_828,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_23,c_13])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_832,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_828,c_23,c_21,c_13])).

cnf(c_3176,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_4944,plain,
    ( k7_relat_1(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_3182,c_3176])).

cnf(c_3212,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4409,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3182,c_3212])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3219,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4952,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_4409,c_3219])).

cnf(c_6129,plain,
    ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4944,c_4952])).

cnf(c_33,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_43,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_932,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_22,c_43])).

cnf(c_944,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_932,c_21])).

cnf(c_1019,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_944])).

cnf(c_1020,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_1019])).

cnf(c_3173,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_4158,plain,
    ( k2_relat_1(sK2) = sK1
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3182,c_3173])).

cnf(c_64,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_65,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_62,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_67,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_4861,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4158,c_65,c_67])).

cnf(c_4862,plain,
    ( k2_relat_1(sK2) = sK1
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4861])).

cnf(c_4868,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_3182,c_4862])).

cnf(c_6132,plain,
    ( k9_relat_1(sK2,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_6129,c_4868])).

cnf(c_6458,plain,
    ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_6457,c_5892,c_6132])).

cnf(c_53,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f149])).

cnf(c_3188,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_6556,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6458,c_3188])).

cnf(c_63,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_66,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_34,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3204,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7769,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3182,c_3204])).

cnf(c_22019,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6556,c_65,c_66,c_67,c_68,c_7769])).

cnf(c_52,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_3189,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_8223,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3182,c_3189])).

cnf(c_3475,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_8774,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8223,c_64,c_63,c_62,c_61,c_3475])).

cnf(c_46,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_3195,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_8785,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8774,c_3195])).

cnf(c_12985,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8785,c_65,c_66,c_67,c_68])).

cnf(c_51,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_3190,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_9456,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3182,c_3190])).

cnf(c_9876,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9456,c_65])).

cnf(c_9877,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9876])).

cnf(c_12990,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12985,c_9877])).

cnf(c_49,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_3192,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_6762,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3182,c_3192])).

cnf(c_7137,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6762,c_65,c_66,c_67])).

cnf(c_8778,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8774,c_7137])).

cnf(c_13085,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12990,c_8778])).

cnf(c_44,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_3197,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_57,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_3186,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_9455,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_3190])).

cnf(c_60,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_69,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_9739,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9455,c_69])).

cnf(c_9740,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9739])).

cnf(c_9746,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,k1_partfun1(X0,X2,X3,X1,X4,X5),sK3) = k5_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5),sK3)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k1_partfun1(X0,X2,X3,X1,X4,X5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3197,c_9740])).

cnf(c_13614,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),sK3)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13085,c_9746])).

cnf(c_13617,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13614,c_13085])).

cnf(c_45,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_3196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_13088,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13085,c_3196])).

cnf(c_168148,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13617,c_65,c_66,c_67,c_68,c_8778,c_8785,c_13088])).

cnf(c_4408,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_3212])).

cnf(c_13001,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12985,c_3212])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3218,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13294,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_13001,c_3218])).

cnf(c_28090,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4409,c_13294])).

cnf(c_28499,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) ),
    inference(superposition,[status(thm)],[c_4408,c_28090])).

cnf(c_9750,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3182,c_9740])).

cnf(c_27,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_56,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_987,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_56])).

cnf(c_988,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_987])).

cnf(c_50,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_996,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_988,c_50])).

cnf(c_3174,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_3305,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_3856,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3174,c_64,c_61,c_60,c_57,c_996,c_3305])).

cnf(c_9751,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9750,c_3856])).

cnf(c_10716,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9751,c_65])).

cnf(c_28508,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_28499,c_10716])).

cnf(c_8372,plain,
    ( k2_relat_1(k2_funct_2(X0,X1)) = X0
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(k2_funct_2(X0,X1),X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3195,c_3173])).

cnf(c_41913,plain,
    ( k2_relat_1(k2_funct_2(sK1,sK2)) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8774,c_8372])).

cnf(c_41990,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41913,c_8774])).

cnf(c_47,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_3194,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_8103,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3182,c_3194])).

cnf(c_8919,plain,
    ( v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8103,c_65,c_66,c_67])).

cnf(c_8923,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8919,c_8774])).

cnf(c_13002,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK1
    | v3_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12985,c_3173])).

cnf(c_42495,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_41990,c_8778,c_8923,c_13002])).

cnf(c_42496,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_42495])).

cnf(c_42502,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_12985,c_42496])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f161])).

cnf(c_3214,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13297,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_13001,c_3214])).

cnf(c_42789,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK1)) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_42502,c_13297])).

cnf(c_168150,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_168148,c_28508,c_42789])).

cnf(c_168159,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k6_partfun1(sK1),sK3) = k2_funct_1(sK2)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22019,c_168150])).

cnf(c_6456,plain,
    ( k7_relset_1(sK1,sK1,sK3,sK1) = k2_relset_1(sK1,sK1,sK3) ),
    inference(superposition,[status(thm)],[c_3186,c_3207])).

cnf(c_4943,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_3186,c_3176])).

cnf(c_4951,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_4408,c_3219])).

cnf(c_5576,plain,
    ( k9_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4943,c_4951])).

cnf(c_4157,plain,
    ( k2_relat_1(sK3) = sK1
    | v3_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_3173])).

cnf(c_58,negated_conjecture,
    ( v3_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_71,plain,
    ( v3_funct_2(sK3,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_4764,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | k2_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4157,c_69,c_71])).

cnf(c_4765,plain,
    ( k2_relat_1(sK3) = sK1
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4764])).

cnf(c_4771,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(superposition,[status(thm)],[c_3186,c_4765])).

cnf(c_5579,plain,
    ( k9_relat_1(sK3,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5576,c_4771])).

cnf(c_5891,plain,
    ( k7_relset_1(sK1,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_3186,c_3210])).

cnf(c_6459,plain,
    ( k2_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_6456,c_5579,c_5891])).

cnf(c_54,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f148])).

cnf(c_3187,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_6583,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6459,c_3187])).

cnf(c_59,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_6585,plain,
    ( ~ v1_funct_2(sK3,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6583])).

cnf(c_4679,plain,
    ( ~ v3_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_7075,plain,
    ( ~ v3_funct_2(sK3,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4679])).

cnf(c_23590,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6583,c_60,c_59,c_58,c_57,c_6585,c_7075])).

cnf(c_8222,plain,
    ( k2_funct_2(sK1,sK3) = k2_funct_1(sK3)
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | v3_funct_2(sK3,sK1,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_3189])).

cnf(c_70,plain,
    ( v1_funct_2(sK3,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_8763,plain,
    ( k2_funct_2(sK1,sK3) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8222,c_69,c_70,c_71])).

cnf(c_8771,plain,
    ( v1_funct_2(sK3,sK1,sK1) != iProver_top
    | v3_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8763,c_3195])).

cnf(c_72,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_12882,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8771,c_69,c_70,c_71,c_72])).

cnf(c_12900,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK3)) = k5_relat_1(X2,k2_funct_1(sK3))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12882,c_3190])).

cnf(c_6761,plain,
    ( v1_funct_2(sK3,sK1,sK1) != iProver_top
    | v3_funct_2(sK3,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_3192])).

cnf(c_7130,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6761,c_69,c_70,c_71])).

cnf(c_8767,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8763,c_7130])).

cnf(c_39658,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK3)) = k5_relat_1(X2,k2_funct_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12900,c_8767])).

cnf(c_39659,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK3)) = k5_relat_1(X2,k2_funct_1(sK3))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_39658])).

cnf(c_39668,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,k2_funct_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_39659])).

cnf(c_39945,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,k2_funct_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39668,c_69])).

cnf(c_9639,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,k1_partfun1(X2,X5,X6,X3,X7,X8)) = k5_relat_1(X4,k1_partfun1(X2,X5,X6,X3,X7,X8))
    | m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X3))) != iProver_top
    | m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X5))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X8) != iProver_top
    | v1_funct_1(X7) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k1_partfun1(X2,X5,X6,X3,X7,X8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3197,c_3190])).

cnf(c_71469,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k1_partfun1(sK1,sK1,sK1,sK1,sK3,k2_funct_1(sK3))) = k5_relat_1(X2,k1_partfun1(sK1,sK1,sK1,sK1,sK3,k2_funct_1(sK3)))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_39945,c_9639])).

cnf(c_71496,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(X2,k5_relat_1(sK3,k2_funct_1(sK3)))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_71469,c_39945])).

cnf(c_39948,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_39945,c_3196])).

cnf(c_39947,plain,
    ( m1_subset_1(k5_relat_1(sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_39945,c_3197])).

cnf(c_40201,plain,
    ( m1_subset_1(k5_relat_1(sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39947,c_69,c_70,c_71,c_72,c_8767,c_8771])).

cnf(c_40222,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(X2,k5_relat_1(sK3,k2_funct_1(sK3)))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_40201,c_3190])).

cnf(c_79365,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(X2,k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_71496,c_69,c_70,c_71,c_72,c_8767,c_8771,c_39948,c_40222])).

cnf(c_79366,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(X2,k5_relat_1(sK3,k2_funct_1(sK3)))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_79365])).

cnf(c_79375,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_79366])).

cnf(c_79711,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_79375,c_69])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3222,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9626,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | r1_tarski(k1_partfun1(X4,X5,X1,X2,X3,X0),k2_zfmisc_1(X4,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3197,c_3222])).

cnf(c_79716,plain,
    ( m1_subset_1(k5_relat_1(sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | r1_tarski(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),k2_zfmisc_1(sK1,sK1)) = iProver_top
    | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_79711,c_9626])).

cnf(c_80032,plain,
    ( r1_tarski(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),k2_zfmisc_1(sK1,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_79716,c_69,c_70,c_71,c_72,c_8767,c_8771,c_39947,c_39948])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3211,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5880,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3223,c_3211])).

cnf(c_80064,plain,
    ( k1_relset_1(sK1,sK1,k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) ),
    inference(superposition,[status(thm)],[c_80032,c_5880])).

cnf(c_139476,plain,
    ( k1_relset_1(sK1,sK1,k5_relat_1(sK3,k6_partfun1(sK1))) = k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_23590,c_80064])).

cnf(c_4596,plain,
    ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
    inference(superposition,[status(thm)],[c_4408,c_3214])).

cnf(c_5358,plain,
    ( k5_relat_1(sK3,k6_partfun1(sK1)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_4596,c_4596,c_4771])).

cnf(c_5882,plain,
    ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3186,c_3211])).

cnf(c_139478,plain,
    ( k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = k1_relat_1(sK3)
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_139476,c_5358,c_5882])).

cnf(c_41914,plain,
    ( k2_relat_1(k2_funct_2(sK1,sK3)) = sK1
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_2(sK1,sK3),sK1,sK1) != iProver_top
    | v3_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8763,c_8372])).

cnf(c_41989,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK1
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_1(sK3),sK1,sK1) != iProver_top
    | v3_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41914,c_8763])).

cnf(c_8102,plain,
    ( v1_funct_2(sK3,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_2(sK1,sK3),sK1,sK1) = iProver_top
    | v3_funct_2(sK3,sK1,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_3194])).

cnf(c_8912,plain,
    ( v3_funct_2(k2_funct_2(sK1,sK3),sK1,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8102,c_69,c_70,c_71])).

cnf(c_8916,plain,
    ( v3_funct_2(k2_funct_1(sK3),sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8912,c_8763])).

cnf(c_12899,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK1
    | v3_funct_2(k2_funct_1(sK3),sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12882,c_3173])).

cnf(c_42486,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_41989,c_8767,c_8916,c_12899])).

cnf(c_42487,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_42486])).

cnf(c_42493,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK1 ),
    inference(superposition,[status(thm)],[c_12882,c_42487])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3217,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_42785,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_42493,c_3217])).

cnf(c_26,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f164])).

cnf(c_55,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_977,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_funct_2(sK1,sK2) != X0
    | sK3 != X0
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_55])).

cnf(c_978,plain,
    ( ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | sK3 != k2_funct_2(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_977])).

cnf(c_5134,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4771,c_3217])).

cnf(c_6579,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_1978,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3300,plain,
    ( k2_funct_2(sK1,sK2) != X0
    | sK3 != X0
    | sK3 = k2_funct_2(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1978])).

cnf(c_7909,plain,
    ( k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
    | sK3 = k2_funct_2(sK1,sK2)
    | sK3 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3300])).

cnf(c_3329,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1978])).

cnf(c_8140,plain,
    ( k2_funct_1(sK2) != X0
    | sK3 != X0
    | sK3 = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3329])).

cnf(c_8143,plain,
    ( k2_funct_1(sK2) != k1_xboole_0
    | sK3 = k2_funct_1(sK2)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8140])).

cnf(c_42790,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_42502,c_3217])).

cnf(c_46990,plain,
    ( sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_42785,c_64,c_63,c_62,c_61,c_978,c_3475,c_4408,c_5134,c_6579,c_7909,c_8143,c_13001,c_42790])).

cnf(c_139480,plain,
    ( k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_139478,c_64,c_63,c_62,c_61,c_978,c_3475,c_4408,c_5134,c_6579,c_7909,c_8143,c_13001,c_42790])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_3198,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_9627,plain,
    ( k1_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(k1_partfun1(X0,X2,X3,X1,X4,X5),X0,X1) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3197,c_3198])).

cnf(c_79719,plain,
    ( k1_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = sK1
    | sK1 = k1_xboole_0
    | v1_funct_2(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),sK1,sK1) != iProver_top
    | m1_subset_1(k5_relat_1(sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_79711,c_9627])).

cnf(c_79728,plain,
    ( k1_relset_1(sK1,sK1,k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = sK1
    | sK1 = k1_xboole_0
    | v1_funct_2(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),sK1,sK1) != iProver_top
    | m1_subset_1(k5_relat_1(sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_79719,c_79711])).

cnf(c_130232,plain,
    ( k1_relset_1(sK1,sK1,k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = sK1
    | v1_funct_2(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),sK1,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_79728,c_64,c_63,c_62,c_61,c_69,c_70,c_71,c_72,c_978,c_3475,c_4408,c_5134,c_6579,c_7909,c_8143,c_8767,c_8771,c_13001,c_39947,c_39948,c_42790])).

cnf(c_130236,plain,
    ( k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = sK1
    | v1_funct_2(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),sK1,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_130232,c_80064])).

cnf(c_139483,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_funct_2(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),sK1,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_139480,c_130236])).

cnf(c_7701,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_3198])).

cnf(c_7704,plain,
    ( k1_relat_1(sK3) = sK1
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7701,c_5882])).

cnf(c_142729,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_139483,c_64,c_63,c_62,c_61,c_70,c_978,c_3475,c_4408,c_5134,c_6579,c_7704,c_7909,c_8143,c_13001,c_42790])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f160])).

cnf(c_3215,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4595,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_4408,c_3215])).

cnf(c_142749,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_142729,c_4595])).

cnf(c_9445,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k6_partfun1(sK1)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3856,c_3196])).

cnf(c_54746,plain,
    ( v1_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9445,c_65,c_68,c_69,c_72])).

cnf(c_3191,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_9748,plain,
    ( k1_partfun1(X0,X0,sK1,sK1,k6_partfun1(X0),sK3) = k5_relat_1(k6_partfun1(X0),sK3)
    | v1_funct_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3191,c_9740])).

cnf(c_54756,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k6_partfun1(sK1),sK3) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_54746,c_9748])).

cnf(c_142795,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_142749,c_54756])).

cnf(c_168186,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_168159,c_142795])).

cnf(c_3175,plain,
    ( sK3 != k2_funct_2(sK1,sK2)
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_978])).

cnf(c_8780,plain,
    ( k2_funct_1(sK2) != sK3
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8774,c_3175])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_168186,c_46990,c_8785,c_8780,c_68,c_67,c_66,c_65])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.70/5.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.70/5.99  
% 43.70/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.70/5.99  
% 43.70/5.99  ------  iProver source info
% 43.70/5.99  
% 43.70/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.70/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.70/5.99  git: non_committed_changes: false
% 43.70/5.99  git: last_make_outside_of_git: false
% 43.70/5.99  
% 43.70/5.99  ------ 
% 43.70/5.99  
% 43.70/5.99  ------ Input Options
% 43.70/5.99  
% 43.70/5.99  --out_options                           all
% 43.70/5.99  --tptp_safe_out                         true
% 43.70/5.99  --problem_path                          ""
% 43.70/5.99  --include_path                          ""
% 43.70/5.99  --clausifier                            res/vclausify_rel
% 43.70/5.99  --clausifier_options                    ""
% 43.70/5.99  --stdin                                 false
% 43.70/5.99  --stats_out                             all
% 43.70/5.99  
% 43.70/5.99  ------ General Options
% 43.70/5.99  
% 43.70/5.99  --fof                                   false
% 43.70/5.99  --time_out_real                         305.
% 43.70/5.99  --time_out_virtual                      -1.
% 43.70/5.99  --symbol_type_check                     false
% 43.70/5.99  --clausify_out                          false
% 43.70/5.99  --sig_cnt_out                           false
% 43.70/5.99  --trig_cnt_out                          false
% 43.70/5.99  --trig_cnt_out_tolerance                1.
% 43.70/5.99  --trig_cnt_out_sk_spl                   false
% 43.70/5.99  --abstr_cl_out                          false
% 43.70/5.99  
% 43.70/5.99  ------ Global Options
% 43.70/5.99  
% 43.70/5.99  --schedule                              default
% 43.70/5.99  --add_important_lit                     false
% 43.70/5.99  --prop_solver_per_cl                    1000
% 43.70/5.99  --min_unsat_core                        false
% 43.70/5.99  --soft_assumptions                      false
% 43.70/5.99  --soft_lemma_size                       3
% 43.70/5.99  --prop_impl_unit_size                   0
% 43.70/5.99  --prop_impl_unit                        []
% 43.70/5.99  --share_sel_clauses                     true
% 43.70/5.99  --reset_solvers                         false
% 43.70/5.99  --bc_imp_inh                            [conj_cone]
% 43.70/5.99  --conj_cone_tolerance                   3.
% 43.70/5.99  --extra_neg_conj                        none
% 43.70/5.99  --large_theory_mode                     true
% 43.70/5.99  --prolific_symb_bound                   200
% 43.70/5.99  --lt_threshold                          2000
% 43.70/5.99  --clause_weak_htbl                      true
% 43.70/5.99  --gc_record_bc_elim                     false
% 43.70/5.99  
% 43.70/5.99  ------ Preprocessing Options
% 43.70/5.99  
% 43.70/5.99  --preprocessing_flag                    true
% 43.70/5.99  --time_out_prep_mult                    0.1
% 43.70/5.99  --splitting_mode                        input
% 43.70/5.99  --splitting_grd                         true
% 43.70/5.99  --splitting_cvd                         false
% 43.70/5.99  --splitting_cvd_svl                     false
% 43.70/5.99  --splitting_nvd                         32
% 43.70/5.99  --sub_typing                            true
% 43.70/5.99  --prep_gs_sim                           true
% 43.70/5.99  --prep_unflatten                        true
% 43.70/5.99  --prep_res_sim                          true
% 43.70/5.99  --prep_upred                            true
% 43.70/5.99  --prep_sem_filter                       exhaustive
% 43.70/5.99  --prep_sem_filter_out                   false
% 43.70/5.99  --pred_elim                             true
% 43.70/5.99  --res_sim_input                         true
% 43.70/5.99  --eq_ax_congr_red                       true
% 43.70/5.99  --pure_diseq_elim                       true
% 43.70/5.99  --brand_transform                       false
% 43.70/5.99  --non_eq_to_eq                          false
% 43.70/5.99  --prep_def_merge                        true
% 43.70/5.99  --prep_def_merge_prop_impl              false
% 43.70/5.99  --prep_def_merge_mbd                    true
% 43.70/5.99  --prep_def_merge_tr_red                 false
% 43.70/5.99  --prep_def_merge_tr_cl                  false
% 43.70/5.99  --smt_preprocessing                     true
% 43.70/5.99  --smt_ac_axioms                         fast
% 43.70/5.99  --preprocessed_out                      false
% 43.70/5.99  --preprocessed_stats                    false
% 43.70/5.99  
% 43.70/5.99  ------ Abstraction refinement Options
% 43.70/5.99  
% 43.70/5.99  --abstr_ref                             []
% 43.70/5.99  --abstr_ref_prep                        false
% 43.70/5.99  --abstr_ref_until_sat                   false
% 43.70/5.99  --abstr_ref_sig_restrict                funpre
% 43.70/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 43.70/5.99  --abstr_ref_under                       []
% 43.70/5.99  
% 43.70/5.99  ------ SAT Options
% 43.70/5.99  
% 43.70/5.99  --sat_mode                              false
% 43.70/5.99  --sat_fm_restart_options                ""
% 43.70/5.99  --sat_gr_def                            false
% 43.70/5.99  --sat_epr_types                         true
% 43.70/5.99  --sat_non_cyclic_types                  false
% 43.70/5.99  --sat_finite_models                     false
% 43.70/5.99  --sat_fm_lemmas                         false
% 43.70/5.99  --sat_fm_prep                           false
% 43.70/5.99  --sat_fm_uc_incr                        true
% 43.70/5.99  --sat_out_model                         small
% 43.70/5.99  --sat_out_clauses                       false
% 43.70/5.99  
% 43.70/5.99  ------ QBF Options
% 43.70/5.99  
% 43.70/5.99  --qbf_mode                              false
% 43.70/5.99  --qbf_elim_univ                         false
% 43.70/5.99  --qbf_dom_inst                          none
% 43.70/5.99  --qbf_dom_pre_inst                      false
% 43.70/5.99  --qbf_sk_in                             false
% 43.70/5.99  --qbf_pred_elim                         true
% 43.70/5.99  --qbf_split                             512
% 43.70/5.99  
% 43.70/5.99  ------ BMC1 Options
% 43.70/5.99  
% 43.70/5.99  --bmc1_incremental                      false
% 43.70/5.99  --bmc1_axioms                           reachable_all
% 43.70/5.99  --bmc1_min_bound                        0
% 43.70/5.99  --bmc1_max_bound                        -1
% 43.70/5.99  --bmc1_max_bound_default                -1
% 43.70/5.99  --bmc1_symbol_reachability              true
% 43.70/5.99  --bmc1_property_lemmas                  false
% 43.70/5.99  --bmc1_k_induction                      false
% 43.70/5.99  --bmc1_non_equiv_states                 false
% 43.70/5.99  --bmc1_deadlock                         false
% 43.70/5.99  --bmc1_ucm                              false
% 43.70/5.99  --bmc1_add_unsat_core                   none
% 43.70/5.99  --bmc1_unsat_core_children              false
% 43.70/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 43.70/5.99  --bmc1_out_stat                         full
% 43.70/5.99  --bmc1_ground_init                      false
% 43.70/5.99  --bmc1_pre_inst_next_state              false
% 43.70/5.99  --bmc1_pre_inst_state                   false
% 43.70/5.99  --bmc1_pre_inst_reach_state             false
% 43.70/5.99  --bmc1_out_unsat_core                   false
% 43.70/5.99  --bmc1_aig_witness_out                  false
% 43.70/5.99  --bmc1_verbose                          false
% 43.70/5.99  --bmc1_dump_clauses_tptp                false
% 43.70/5.99  --bmc1_dump_unsat_core_tptp             false
% 43.70/5.99  --bmc1_dump_file                        -
% 43.70/5.99  --bmc1_ucm_expand_uc_limit              128
% 43.70/5.99  --bmc1_ucm_n_expand_iterations          6
% 43.70/5.99  --bmc1_ucm_extend_mode                  1
% 43.70/5.99  --bmc1_ucm_init_mode                    2
% 43.70/5.99  --bmc1_ucm_cone_mode                    none
% 43.70/5.99  --bmc1_ucm_reduced_relation_type        0
% 43.70/5.99  --bmc1_ucm_relax_model                  4
% 43.70/5.99  --bmc1_ucm_full_tr_after_sat            true
% 43.70/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 43.70/5.99  --bmc1_ucm_layered_model                none
% 43.70/5.99  --bmc1_ucm_max_lemma_size               10
% 43.70/5.99  
% 43.70/5.99  ------ AIG Options
% 43.70/5.99  
% 43.70/5.99  --aig_mode                              false
% 43.70/5.99  
% 43.70/5.99  ------ Instantiation Options
% 43.70/5.99  
% 43.70/5.99  --instantiation_flag                    true
% 43.70/5.99  --inst_sos_flag                         true
% 43.70/5.99  --inst_sos_phase                        true
% 43.70/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.70/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.70/5.99  --inst_lit_sel_side                     num_symb
% 43.70/5.99  --inst_solver_per_active                1400
% 43.70/5.99  --inst_solver_calls_frac                1.
% 43.70/5.99  --inst_passive_queue_type               priority_queues
% 43.70/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.70/5.99  --inst_passive_queues_freq              [25;2]
% 43.70/5.99  --inst_dismatching                      true
% 43.70/5.99  --inst_eager_unprocessed_to_passive     true
% 43.70/5.99  --inst_prop_sim_given                   true
% 43.70/5.99  --inst_prop_sim_new                     false
% 43.70/5.99  --inst_subs_new                         false
% 43.70/5.99  --inst_eq_res_simp                      false
% 43.70/5.99  --inst_subs_given                       false
% 43.70/5.99  --inst_orphan_elimination               true
% 43.70/5.99  --inst_learning_loop_flag               true
% 43.70/5.99  --inst_learning_start                   3000
% 43.70/5.99  --inst_learning_factor                  2
% 43.70/5.99  --inst_start_prop_sim_after_learn       3
% 43.70/5.99  --inst_sel_renew                        solver
% 43.70/5.99  --inst_lit_activity_flag                true
% 43.70/5.99  --inst_restr_to_given                   false
% 43.70/5.99  --inst_activity_threshold               500
% 43.70/5.99  --inst_out_proof                        true
% 43.70/5.99  
% 43.70/5.99  ------ Resolution Options
% 43.70/5.99  
% 43.70/5.99  --resolution_flag                       true
% 43.70/5.99  --res_lit_sel                           adaptive
% 43.70/5.99  --res_lit_sel_side                      none
% 43.70/5.99  --res_ordering                          kbo
% 43.70/5.99  --res_to_prop_solver                    active
% 43.70/5.99  --res_prop_simpl_new                    false
% 43.70/5.99  --res_prop_simpl_given                  true
% 43.70/5.99  --res_passive_queue_type                priority_queues
% 43.70/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.70/5.99  --res_passive_queues_freq               [15;5]
% 43.70/5.99  --res_forward_subs                      full
% 43.70/5.99  --res_backward_subs                     full
% 43.70/5.99  --res_forward_subs_resolution           true
% 43.70/5.99  --res_backward_subs_resolution          true
% 43.70/5.99  --res_orphan_elimination                true
% 43.70/5.99  --res_time_limit                        2.
% 43.70/5.99  --res_out_proof                         true
% 43.70/5.99  
% 43.70/5.99  ------ Superposition Options
% 43.70/5.99  
% 43.70/5.99  --superposition_flag                    true
% 43.70/5.99  --sup_passive_queue_type                priority_queues
% 43.70/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.70/5.99  --sup_passive_queues_freq               [8;1;4]
% 43.70/5.99  --demod_completeness_check              fast
% 43.70/5.99  --demod_use_ground                      true
% 43.70/5.99  --sup_to_prop_solver                    passive
% 43.70/5.99  --sup_prop_simpl_new                    true
% 43.70/5.99  --sup_prop_simpl_given                  true
% 43.70/5.99  --sup_fun_splitting                     true
% 43.70/5.99  --sup_smt_interval                      50000
% 43.70/5.99  
% 43.70/5.99  ------ Superposition Simplification Setup
% 43.70/5.99  
% 43.70/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.70/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.70/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.70/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.70/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 43.70/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.70/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.70/5.99  --sup_immed_triv                        [TrivRules]
% 43.70/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.70/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.70/5.99  --sup_immed_bw_main                     []
% 43.70/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.70/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 43.70/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.70/5.99  --sup_input_bw                          []
% 43.70/5.99  
% 43.70/5.99  ------ Combination Options
% 43.70/5.99  
% 43.70/5.99  --comb_res_mult                         3
% 43.70/5.99  --comb_sup_mult                         2
% 43.70/5.99  --comb_inst_mult                        10
% 43.70/5.99  
% 43.70/5.99  ------ Debug Options
% 43.70/5.99  
% 43.70/5.99  --dbg_backtrace                         false
% 43.70/5.99  --dbg_dump_prop_clauses                 false
% 43.70/5.99  --dbg_dump_prop_clauses_file            -
% 43.70/5.99  --dbg_out_stat                          false
% 43.70/5.99  ------ Parsing...
% 43.70/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.70/5.99  
% 43.70/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 43.70/5.99  
% 43.70/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.70/5.99  
% 43.70/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.70/5.99  ------ Proving...
% 43.70/5.99  ------ Problem Properties 
% 43.70/5.99  
% 43.70/5.99  
% 43.70/5.99  clauses                                 59
% 43.70/5.99  conjectures                             8
% 43.70/5.99  EPR                                     11
% 43.70/5.99  Horn                                    52
% 43.70/5.99  unary                                   13
% 43.70/5.99  binary                                  21
% 43.70/5.99  lits                                    162
% 43.70/5.99  lits eq                                 40
% 43.70/5.99  fd_pure                                 0
% 43.70/5.99  fd_pseudo                               0
% 43.70/5.99  fd_cond                                 7
% 43.70/5.99  fd_pseudo_cond                          2
% 43.70/5.99  AC symbols                              0
% 43.70/5.99  
% 43.70/5.99  ------ Schedule dynamic 5 is on 
% 43.70/5.99  
% 43.70/5.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.70/5.99  
% 43.70/5.99  
% 43.70/5.99  ------ 
% 43.70/5.99  Current options:
% 43.70/5.99  ------ 
% 43.70/5.99  
% 43.70/5.99  ------ Input Options
% 43.70/5.99  
% 43.70/5.99  --out_options                           all
% 43.70/5.99  --tptp_safe_out                         true
% 43.70/5.99  --problem_path                          ""
% 43.70/5.99  --include_path                          ""
% 43.70/5.99  --clausifier                            res/vclausify_rel
% 43.70/5.99  --clausifier_options                    ""
% 43.70/5.99  --stdin                                 false
% 43.70/5.99  --stats_out                             all
% 43.70/5.99  
% 43.70/5.99  ------ General Options
% 43.70/5.99  
% 43.70/5.99  --fof                                   false
% 43.70/5.99  --time_out_real                         305.
% 43.70/5.99  --time_out_virtual                      -1.
% 43.70/5.99  --symbol_type_check                     false
% 43.70/5.99  --clausify_out                          false
% 43.70/5.99  --sig_cnt_out                           false
% 43.70/5.99  --trig_cnt_out                          false
% 43.70/5.99  --trig_cnt_out_tolerance                1.
% 43.70/5.99  --trig_cnt_out_sk_spl                   false
% 43.70/5.99  --abstr_cl_out                          false
% 43.70/5.99  
% 43.70/5.99  ------ Global Options
% 43.70/5.99  
% 43.70/5.99  --schedule                              default
% 43.70/5.99  --add_important_lit                     false
% 43.70/5.99  --prop_solver_per_cl                    1000
% 43.70/5.99  --min_unsat_core                        false
% 43.70/5.99  --soft_assumptions                      false
% 43.70/5.99  --soft_lemma_size                       3
% 43.70/5.99  --prop_impl_unit_size                   0
% 43.70/5.99  --prop_impl_unit                        []
% 43.70/5.99  --share_sel_clauses                     true
% 43.70/5.99  --reset_solvers                         false
% 43.70/5.99  --bc_imp_inh                            [conj_cone]
% 43.70/5.99  --conj_cone_tolerance                   3.
% 43.70/5.99  --extra_neg_conj                        none
% 43.70/5.99  --large_theory_mode                     true
% 43.70/5.99  --prolific_symb_bound                   200
% 43.70/5.99  --lt_threshold                          2000
% 43.70/5.99  --clause_weak_htbl                      true
% 43.70/5.99  --gc_record_bc_elim                     false
% 43.70/5.99  
% 43.70/5.99  ------ Preprocessing Options
% 43.70/5.99  
% 43.70/5.99  --preprocessing_flag                    true
% 43.70/5.99  --time_out_prep_mult                    0.1
% 43.70/5.99  --splitting_mode                        input
% 43.70/5.99  --splitting_grd                         true
% 43.70/5.99  --splitting_cvd                         false
% 43.70/5.99  --splitting_cvd_svl                     false
% 43.70/5.99  --splitting_nvd                         32
% 43.70/5.99  --sub_typing                            true
% 43.70/5.99  --prep_gs_sim                           true
% 43.70/5.99  --prep_unflatten                        true
% 43.70/5.99  --prep_res_sim                          true
% 43.70/5.99  --prep_upred                            true
% 43.70/5.99  --prep_sem_filter                       exhaustive
% 43.70/5.99  --prep_sem_filter_out                   false
% 43.70/5.99  --pred_elim                             true
% 43.70/5.99  --res_sim_input                         true
% 43.70/5.99  --eq_ax_congr_red                       true
% 43.70/5.99  --pure_diseq_elim                       true
% 43.70/5.99  --brand_transform                       false
% 43.70/5.99  --non_eq_to_eq                          false
% 43.70/5.99  --prep_def_merge                        true
% 43.70/5.99  --prep_def_merge_prop_impl              false
% 43.70/5.99  --prep_def_merge_mbd                    true
% 43.70/5.99  --prep_def_merge_tr_red                 false
% 43.70/5.99  --prep_def_merge_tr_cl                  false
% 43.70/5.99  --smt_preprocessing                     true
% 43.70/5.99  --smt_ac_axioms                         fast
% 43.70/5.99  --preprocessed_out                      false
% 43.70/5.99  --preprocessed_stats                    false
% 43.70/5.99  
% 43.70/5.99  ------ Abstraction refinement Options
% 43.70/5.99  
% 43.70/5.99  --abstr_ref                             []
% 43.70/5.99  --abstr_ref_prep                        false
% 43.70/5.99  --abstr_ref_until_sat                   false
% 43.70/5.99  --abstr_ref_sig_restrict                funpre
% 43.70/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 43.70/5.99  --abstr_ref_under                       []
% 43.70/5.99  
% 43.70/5.99  ------ SAT Options
% 43.70/5.99  
% 43.70/5.99  --sat_mode                              false
% 43.70/5.99  --sat_fm_restart_options                ""
% 43.70/5.99  --sat_gr_def                            false
% 43.70/5.99  --sat_epr_types                         true
% 43.70/5.99  --sat_non_cyclic_types                  false
% 43.70/5.99  --sat_finite_models                     false
% 43.70/5.99  --sat_fm_lemmas                         false
% 43.70/5.99  --sat_fm_prep                           false
% 43.70/5.99  --sat_fm_uc_incr                        true
% 43.70/5.99  --sat_out_model                         small
% 43.70/5.99  --sat_out_clauses                       false
% 43.70/5.99  
% 43.70/5.99  ------ QBF Options
% 43.70/5.99  
% 43.70/5.99  --qbf_mode                              false
% 43.70/5.99  --qbf_elim_univ                         false
% 43.70/5.99  --qbf_dom_inst                          none
% 43.70/5.99  --qbf_dom_pre_inst                      false
% 43.70/5.99  --qbf_sk_in                             false
% 43.70/5.99  --qbf_pred_elim                         true
% 43.70/5.99  --qbf_split                             512
% 43.70/5.99  
% 43.70/5.99  ------ BMC1 Options
% 43.70/5.99  
% 43.70/5.99  --bmc1_incremental                      false
% 43.70/5.99  --bmc1_axioms                           reachable_all
% 43.70/5.99  --bmc1_min_bound                        0
% 43.70/5.99  --bmc1_max_bound                        -1
% 43.70/5.99  --bmc1_max_bound_default                -1
% 43.70/5.99  --bmc1_symbol_reachability              true
% 43.70/5.99  --bmc1_property_lemmas                  false
% 43.70/5.99  --bmc1_k_induction                      false
% 43.70/5.99  --bmc1_non_equiv_states                 false
% 43.70/5.99  --bmc1_deadlock                         false
% 43.70/5.99  --bmc1_ucm                              false
% 43.70/5.99  --bmc1_add_unsat_core                   none
% 43.70/5.99  --bmc1_unsat_core_children              false
% 43.70/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 43.70/5.99  --bmc1_out_stat                         full
% 43.70/5.99  --bmc1_ground_init                      false
% 43.70/5.99  --bmc1_pre_inst_next_state              false
% 43.70/5.99  --bmc1_pre_inst_state                   false
% 43.70/5.99  --bmc1_pre_inst_reach_state             false
% 43.70/5.99  --bmc1_out_unsat_core                   false
% 43.70/5.99  --bmc1_aig_witness_out                  false
% 43.70/5.99  --bmc1_verbose                          false
% 43.70/5.99  --bmc1_dump_clauses_tptp                false
% 43.70/5.99  --bmc1_dump_unsat_core_tptp             false
% 43.70/5.99  --bmc1_dump_file                        -
% 43.70/5.99  --bmc1_ucm_expand_uc_limit              128
% 43.70/5.99  --bmc1_ucm_n_expand_iterations          6
% 43.70/5.99  --bmc1_ucm_extend_mode                  1
% 43.70/5.99  --bmc1_ucm_init_mode                    2
% 43.70/5.99  --bmc1_ucm_cone_mode                    none
% 43.70/5.99  --bmc1_ucm_reduced_relation_type        0
% 43.70/5.99  --bmc1_ucm_relax_model                  4
% 43.70/5.99  --bmc1_ucm_full_tr_after_sat            true
% 43.70/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 43.70/5.99  --bmc1_ucm_layered_model                none
% 43.70/5.99  --bmc1_ucm_max_lemma_size               10
% 43.70/5.99  
% 43.70/5.99  ------ AIG Options
% 43.70/5.99  
% 43.70/5.99  --aig_mode                              false
% 43.70/5.99  
% 43.70/5.99  ------ Instantiation Options
% 43.70/5.99  
% 43.70/5.99  --instantiation_flag                    true
% 43.70/5.99  --inst_sos_flag                         true
% 43.70/5.99  --inst_sos_phase                        true
% 43.70/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.70/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.70/5.99  --inst_lit_sel_side                     none
% 43.70/5.99  --inst_solver_per_active                1400
% 43.70/5.99  --inst_solver_calls_frac                1.
% 43.70/5.99  --inst_passive_queue_type               priority_queues
% 43.70/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.70/5.99  --inst_passive_queues_freq              [25;2]
% 43.70/5.99  --inst_dismatching                      true
% 43.70/5.99  --inst_eager_unprocessed_to_passive     true
% 43.70/5.99  --inst_prop_sim_given                   true
% 43.70/5.99  --inst_prop_sim_new                     false
% 43.70/5.99  --inst_subs_new                         false
% 43.70/5.99  --inst_eq_res_simp                      false
% 43.70/5.99  --inst_subs_given                       false
% 43.70/5.99  --inst_orphan_elimination               true
% 43.70/5.99  --inst_learning_loop_flag               true
% 43.70/5.99  --inst_learning_start                   3000
% 43.70/5.99  --inst_learning_factor                  2
% 43.70/5.99  --inst_start_prop_sim_after_learn       3
% 43.70/5.99  --inst_sel_renew                        solver
% 43.70/5.99  --inst_lit_activity_flag                true
% 43.70/5.99  --inst_restr_to_given                   false
% 43.70/5.99  --inst_activity_threshold               500
% 43.70/5.99  --inst_out_proof                        true
% 43.70/5.99  
% 43.70/5.99  ------ Resolution Options
% 43.70/5.99  
% 43.70/5.99  --resolution_flag                       false
% 43.70/5.99  --res_lit_sel                           adaptive
% 43.70/5.99  --res_lit_sel_side                      none
% 43.70/5.99  --res_ordering                          kbo
% 43.70/5.99  --res_to_prop_solver                    active
% 43.70/5.99  --res_prop_simpl_new                    false
% 43.70/5.99  --res_prop_simpl_given                  true
% 43.70/5.99  --res_passive_queue_type                priority_queues
% 43.70/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.70/5.99  --res_passive_queues_freq               [15;5]
% 43.70/5.99  --res_forward_subs                      full
% 43.70/5.99  --res_backward_subs                     full
% 43.70/5.99  --res_forward_subs_resolution           true
% 43.70/5.99  --res_backward_subs_resolution          true
% 43.70/5.99  --res_orphan_elimination                true
% 43.70/5.99  --res_time_limit                        2.
% 43.70/5.99  --res_out_proof                         true
% 43.70/5.99  
% 43.70/5.99  ------ Superposition Options
% 43.70/5.99  
% 43.70/5.99  --superposition_flag                    true
% 43.70/5.99  --sup_passive_queue_type                priority_queues
% 43.70/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.70/5.99  --sup_passive_queues_freq               [8;1;4]
% 43.70/5.99  --demod_completeness_check              fast
% 43.70/5.99  --demod_use_ground                      true
% 43.70/5.99  --sup_to_prop_solver                    passive
% 43.70/5.99  --sup_prop_simpl_new                    true
% 43.70/5.99  --sup_prop_simpl_given                  true
% 43.70/5.99  --sup_fun_splitting                     true
% 43.70/5.99  --sup_smt_interval                      50000
% 43.70/5.99  
% 43.70/5.99  ------ Superposition Simplification Setup
% 43.70/5.99  
% 43.70/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.70/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.70/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.70/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.70/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 43.70/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.70/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.70/5.99  --sup_immed_triv                        [TrivRules]
% 43.70/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.70/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.70/5.99  --sup_immed_bw_main                     []
% 43.70/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.70/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 43.70/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.70/5.99  --sup_input_bw                          []
% 43.70/5.99  
% 43.70/5.99  ------ Combination Options
% 43.70/5.99  
% 43.70/5.99  --comb_res_mult                         3
% 43.70/5.99  --comb_sup_mult                         2
% 43.70/5.99  --comb_inst_mult                        10
% 43.70/5.99  
% 43.70/5.99  ------ Debug Options
% 43.70/5.99  
% 43.70/5.99  --dbg_backtrace                         false
% 43.70/5.99  --dbg_dump_prop_clauses                 false
% 43.70/5.99  --dbg_dump_prop_clauses_file            -
% 43.70/5.99  --dbg_out_stat                          false
% 43.70/5.99  
% 43.70/5.99  
% 43.70/5.99  
% 43.70/5.99  
% 43.70/5.99  ------ Proving...
% 43.70/5.99  
% 43.70/5.99  
% 43.70/5.99  % SZS status Theorem for theBenchmark.p
% 43.70/5.99  
% 43.70/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 43.70/5.99  
% 43.70/5.99  fof(f37,conjecture,(
% 43.70/5.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f38,negated_conjecture,(
% 43.70/5.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 43.70/5.99    inference(negated_conjecture,[],[f37])).
% 43.70/5.99  
% 43.70/5.99  fof(f83,plain,(
% 43.70/5.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 43.70/5.99    inference(ennf_transformation,[],[f38])).
% 43.70/5.99  
% 43.70/5.99  fof(f84,plain,(
% 43.70/5.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 43.70/5.99    inference(flattening,[],[f83])).
% 43.70/5.99  
% 43.70/5.99  fof(f92,plain,(
% 43.70/5.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK3,X0,X0) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 43.70/5.99    introduced(choice_axiom,[])).
% 43.70/5.99  
% 43.70/5.99  fof(f91,plain,(
% 43.70/5.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(X2,sK1,sK1) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 43.70/5.99    introduced(choice_axiom,[])).
% 43.70/5.99  
% 43.70/5.99  fof(f93,plain,(
% 43.70/5.99    (~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 43.70/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f84,f92,f91])).
% 43.70/5.99  
% 43.70/5.99  fof(f153,plain,(
% 43.70/5.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 43.70/5.99    inference(cnf_transformation,[],[f93])).
% 43.70/5.99  
% 43.70/5.99  fof(f25,axiom,(
% 43.70/5.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f65,plain,(
% 43.70/5.99    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(ennf_transformation,[],[f25])).
% 43.70/5.99  
% 43.70/5.99  fof(f123,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f65])).
% 43.70/5.99  
% 43.70/5.99  fof(f22,axiom,(
% 43.70/5.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f62,plain,(
% 43.70/5.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(ennf_transformation,[],[f22])).
% 43.70/5.99  
% 43.70/5.99  fof(f119,plain,(
% 43.70/5.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f62])).
% 43.70/5.99  
% 43.70/5.99  fof(f20,axiom,(
% 43.70/5.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f60,plain,(
% 43.70/5.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(ennf_transformation,[],[f20])).
% 43.70/5.99  
% 43.70/5.99  fof(f116,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f60])).
% 43.70/5.99  
% 43.70/5.99  fof(f12,axiom,(
% 43.70/5.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f50,plain,(
% 43.70/5.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 43.70/5.99    inference(ennf_transformation,[],[f12])).
% 43.70/5.99  
% 43.70/5.99  fof(f51,plain,(
% 43.70/5.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 43.70/5.99    inference(flattening,[],[f50])).
% 43.70/5.99  
% 43.70/5.99  fof(f107,plain,(
% 43.70/5.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f51])).
% 43.70/5.99  
% 43.70/5.99  fof(f19,axiom,(
% 43.70/5.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f59,plain,(
% 43.70/5.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(ennf_transformation,[],[f19])).
% 43.70/5.99  
% 43.70/5.99  fof(f115,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f59])).
% 43.70/5.99  
% 43.70/5.99  fof(f11,axiom,(
% 43.70/5.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f49,plain,(
% 43.70/5.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 43.70/5.99    inference(ennf_transformation,[],[f11])).
% 43.70/5.99  
% 43.70/5.99  fof(f106,plain,(
% 43.70/5.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f49])).
% 43.70/5.99  
% 43.70/5.99  fof(f27,axiom,(
% 43.70/5.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f67,plain,(
% 43.70/5.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(ennf_transformation,[],[f27])).
% 43.70/5.99  
% 43.70/5.99  fof(f68,plain,(
% 43.70/5.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(flattening,[],[f67])).
% 43.70/5.99  
% 43.70/5.99  fof(f129,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f68])).
% 43.70/5.99  
% 43.70/5.99  fof(f117,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f60])).
% 43.70/5.99  
% 43.70/5.99  fof(f29,axiom,(
% 43.70/5.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f71,plain,(
% 43.70/5.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 43.70/5.99    inference(ennf_transformation,[],[f29])).
% 43.70/5.99  
% 43.70/5.99  fof(f72,plain,(
% 43.70/5.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 43.70/5.99    inference(flattening,[],[f71])).
% 43.70/5.99  
% 43.70/5.99  fof(f90,plain,(
% 43.70/5.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 43.70/5.99    inference(nnf_transformation,[],[f72])).
% 43.70/5.99  
% 43.70/5.99  fof(f136,plain,(
% 43.70/5.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f90])).
% 43.70/5.99  
% 43.70/5.99  fof(f150,plain,(
% 43.70/5.99    v1_funct_1(sK2)),
% 43.70/5.99    inference(cnf_transformation,[],[f93])).
% 43.70/5.99  
% 43.70/5.99  fof(f152,plain,(
% 43.70/5.99    v3_funct_2(sK2,sK1,sK1)),
% 43.70/5.99    inference(cnf_transformation,[],[f93])).
% 43.70/5.99  
% 43.70/5.99  fof(f36,axiom,(
% 43.70/5.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f81,plain,(
% 43.70/5.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 43.70/5.99    inference(ennf_transformation,[],[f36])).
% 43.70/5.99  
% 43.70/5.99  fof(f82,plain,(
% 43.70/5.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 43.70/5.99    inference(flattening,[],[f81])).
% 43.70/5.99  
% 43.70/5.99  fof(f149,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f82])).
% 43.70/5.99  
% 43.70/5.99  fof(f151,plain,(
% 43.70/5.99    v1_funct_2(sK2,sK1,sK1)),
% 43.70/5.99    inference(cnf_transformation,[],[f93])).
% 43.70/5.99  
% 43.70/5.99  fof(f128,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f68])).
% 43.70/5.99  
% 43.70/5.99  fof(f34,axiom,(
% 43.70/5.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f79,plain,(
% 43.70/5.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 43.70/5.99    inference(ennf_transformation,[],[f34])).
% 43.70/5.99  
% 43.70/5.99  fof(f80,plain,(
% 43.70/5.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 43.70/5.99    inference(flattening,[],[f79])).
% 43.70/5.99  
% 43.70/5.99  fof(f146,plain,(
% 43.70/5.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f80])).
% 43.70/5.99  
% 43.70/5.99  fof(f31,axiom,(
% 43.70/5.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f75,plain,(
% 43.70/5.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 43.70/5.99    inference(ennf_transformation,[],[f31])).
% 43.70/5.99  
% 43.70/5.99  fof(f76,plain,(
% 43.70/5.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 43.70/5.99    inference(flattening,[],[f75])).
% 43.70/5.99  
% 43.70/5.99  fof(f143,plain,(
% 43.70/5.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f76])).
% 43.70/5.99  
% 43.70/5.99  fof(f33,axiom,(
% 43.70/5.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f77,plain,(
% 43.70/5.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 43.70/5.99    inference(ennf_transformation,[],[f33])).
% 43.70/5.99  
% 43.70/5.99  fof(f78,plain,(
% 43.70/5.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 43.70/5.99    inference(flattening,[],[f77])).
% 43.70/5.99  
% 43.70/5.99  fof(f145,plain,(
% 43.70/5.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f78])).
% 43.70/5.99  
% 43.70/5.99  fof(f140,plain,(
% 43.70/5.99    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f76])).
% 43.70/5.99  
% 43.70/5.99  fof(f30,axiom,(
% 43.70/5.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f73,plain,(
% 43.70/5.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 43.70/5.99    inference(ennf_transformation,[],[f30])).
% 43.70/5.99  
% 43.70/5.99  fof(f74,plain,(
% 43.70/5.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 43.70/5.99    inference(flattening,[],[f73])).
% 43.70/5.99  
% 43.70/5.99  fof(f139,plain,(
% 43.70/5.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f74])).
% 43.70/5.99  
% 43.70/5.99  fof(f157,plain,(
% 43.70/5.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 43.70/5.99    inference(cnf_transformation,[],[f93])).
% 43.70/5.99  
% 43.70/5.99  fof(f154,plain,(
% 43.70/5.99    v1_funct_1(sK3)),
% 43.70/5.99    inference(cnf_transformation,[],[f93])).
% 43.70/5.99  
% 43.70/5.99  fof(f138,plain,(
% 43.70/5.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f74])).
% 43.70/5.99  
% 43.70/5.99  fof(f13,axiom,(
% 43.70/5.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f52,plain,(
% 43.70/5.99    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 43.70/5.99    inference(ennf_transformation,[],[f13])).
% 43.70/5.99  
% 43.70/5.99  fof(f108,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f52])).
% 43.70/5.99  
% 43.70/5.99  fof(f23,axiom,(
% 43.70/5.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f63,plain,(
% 43.70/5.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 43.70/5.99    inference(ennf_transformation,[],[f23])).
% 43.70/5.99  
% 43.70/5.99  fof(f64,plain,(
% 43.70/5.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(flattening,[],[f63])).
% 43.70/5.99  
% 43.70/5.99  fof(f88,plain,(
% 43.70/5.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(nnf_transformation,[],[f64])).
% 43.70/5.99  
% 43.70/5.99  fof(f120,plain,(
% 43.70/5.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f88])).
% 43.70/5.99  
% 43.70/5.99  fof(f158,plain,(
% 43.70/5.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))),
% 43.70/5.99    inference(cnf_transformation,[],[f93])).
% 43.70/5.99  
% 43.70/5.99  fof(f32,axiom,(
% 43.70/5.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f40,plain,(
% 43.70/5.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 43.70/5.99    inference(pure_predicate_removal,[],[f32])).
% 43.70/5.99  
% 43.70/5.99  fof(f144,plain,(
% 43.70/5.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f40])).
% 43.70/5.99  
% 43.70/5.99  fof(f142,plain,(
% 43.70/5.99    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f76])).
% 43.70/5.99  
% 43.70/5.99  fof(f16,axiom,(
% 43.70/5.99    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f56,plain,(
% 43.70/5.99    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 43.70/5.99    inference(ennf_transformation,[],[f16])).
% 43.70/5.99  
% 43.70/5.99  fof(f112,plain,(
% 43.70/5.99    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f56])).
% 43.70/5.99  
% 43.70/5.99  fof(f35,axiom,(
% 43.70/5.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f147,plain,(
% 43.70/5.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f35])).
% 43.70/5.99  
% 43.70/5.99  fof(f161,plain,(
% 43.70/5.99    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 43.70/5.99    inference(definition_unfolding,[],[f112,f147])).
% 43.70/5.99  
% 43.70/5.99  fof(f156,plain,(
% 43.70/5.99    v3_funct_2(sK3,sK1,sK1)),
% 43.70/5.99    inference(cnf_transformation,[],[f93])).
% 43.70/5.99  
% 43.70/5.99  fof(f148,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f82])).
% 43.70/5.99  
% 43.70/5.99  fof(f155,plain,(
% 43.70/5.99    v1_funct_2(sK3,sK1,sK1)),
% 43.70/5.99    inference(cnf_transformation,[],[f93])).
% 43.70/5.99  
% 43.70/5.99  fof(f6,axiom,(
% 43.70/5.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f87,plain,(
% 43.70/5.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 43.70/5.99    inference(nnf_transformation,[],[f6])).
% 43.70/5.99  
% 43.70/5.99  fof(f100,plain,(
% 43.70/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f87])).
% 43.70/5.99  
% 43.70/5.99  fof(f101,plain,(
% 43.70/5.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f87])).
% 43.70/5.99  
% 43.70/5.99  fof(f21,axiom,(
% 43.70/5.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f61,plain,(
% 43.70/5.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(ennf_transformation,[],[f21])).
% 43.70/5.99  
% 43.70/5.99  fof(f118,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f61])).
% 43.70/5.99  
% 43.70/5.99  fof(f14,axiom,(
% 43.70/5.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f53,plain,(
% 43.70/5.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 43.70/5.99    inference(ennf_transformation,[],[f14])).
% 43.70/5.99  
% 43.70/5.99  fof(f54,plain,(
% 43.70/5.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 43.70/5.99    inference(flattening,[],[f53])).
% 43.70/5.99  
% 43.70/5.99  fof(f110,plain,(
% 43.70/5.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f54])).
% 43.70/5.99  
% 43.70/5.99  fof(f121,plain,(
% 43.70/5.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f88])).
% 43.70/5.99  
% 43.70/5.99  fof(f164,plain,(
% 43.70/5.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(equality_resolution,[],[f121])).
% 43.70/5.99  
% 43.70/5.99  fof(f159,plain,(
% 43.70/5.99    ~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))),
% 43.70/5.99    inference(cnf_transformation,[],[f93])).
% 43.70/5.99  
% 43.70/5.99  fof(f28,axiom,(
% 43.70/5.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f69,plain,(
% 43.70/5.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(ennf_transformation,[],[f28])).
% 43.70/5.99  
% 43.70/5.99  fof(f70,plain,(
% 43.70/5.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(flattening,[],[f69])).
% 43.70/5.99  
% 43.70/5.99  fof(f89,plain,(
% 43.70/5.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.70/5.99    inference(nnf_transformation,[],[f70])).
% 43.70/5.99  
% 43.70/5.99  fof(f130,plain,(
% 43.70/5.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.70/5.99    inference(cnf_transformation,[],[f89])).
% 43.70/5.99  
% 43.70/5.99  fof(f15,axiom,(
% 43.70/5.99    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 43.70/5.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.70/5.99  
% 43.70/5.99  fof(f55,plain,(
% 43.70/5.99    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 43.70/5.99    inference(ennf_transformation,[],[f15])).
% 43.70/5.99  
% 43.70/5.99  fof(f111,plain,(
% 43.70/5.99    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 43.70/5.99    inference(cnf_transformation,[],[f55])).
% 43.70/5.99  
% 43.70/5.99  fof(f160,plain,(
% 43.70/5.99    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 43.70/5.99    inference(definition_unfolding,[],[f111,f147])).
% 43.70/5.99  
% 43.70/5.99  cnf(c_61,negated_conjecture,
% 43.70/5.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 43.70/5.99      inference(cnf_transformation,[],[f153]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3182,plain,
% 43.70/5.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_30,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 43.70/5.99      inference(cnf_transformation,[],[f123]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3207,plain,
% 43.70/5.99      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6457,plain,
% 43.70/5.99      ( k7_relset_1(sK1,sK1,sK2,sK1) = k2_relset_1(sK1,sK1,sK2) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_3207]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_25,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 43.70/5.99      inference(cnf_transformation,[],[f119]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3210,plain,
% 43.70/5.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_5892,plain,
% 43.70/5.99      ( k7_relset_1(sK1,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_3210]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_23,plain,
% 43.70/5.99      ( v4_relat_1(X0,X1)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 43.70/5.99      inference(cnf_transformation,[],[f116]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_13,plain,
% 43.70/5.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 43.70/5.99      inference(cnf_transformation,[],[f107]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_828,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ v1_relat_1(X0)
% 43.70/5.99      | k7_relat_1(X0,X1) = X0 ),
% 43.70/5.99      inference(resolution,[status(thm)],[c_23,c_13]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_21,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | v1_relat_1(X0) ),
% 43.70/5.99      inference(cnf_transformation,[],[f115]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_832,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | k7_relat_1(X0,X1) = X0 ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_828,c_23,c_21,c_13]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3176,plain,
% 43.70/5.99      ( k7_relat_1(X0,X1) = X0
% 43.70/5.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4944,plain,
% 43.70/5.99      ( k7_relat_1(sK2,sK1) = sK2 ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_3176]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3212,plain,
% 43.70/5.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 43.70/5.99      | v1_relat_1(X0) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4409,plain,
% 43.70/5.99      ( v1_relat_1(sK2) = iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_3212]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_12,plain,
% 43.70/5.99      ( ~ v1_relat_1(X0)
% 43.70/5.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 43.70/5.99      inference(cnf_transformation,[],[f106]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3219,plain,
% 43.70/5.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 43.70/5.99      | v1_relat_1(X0) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4952,plain,
% 43.70/5.99      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_4409,c_3219]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6129,plain,
% 43.70/5.99      ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_4944,c_4952]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_33,plain,
% 43.70/5.99      ( ~ v3_funct_2(X0,X1,X2)
% 43.70/5.99      | v2_funct_2(X0,X2)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ v1_funct_1(X0) ),
% 43.70/5.99      inference(cnf_transformation,[],[f129]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_22,plain,
% 43.70/5.99      ( v5_relat_1(X0,X1)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 43.70/5.99      inference(cnf_transformation,[],[f117]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_43,plain,
% 43.70/5.99      ( ~ v2_funct_2(X0,X1)
% 43.70/5.99      | ~ v5_relat_1(X0,X1)
% 43.70/5.99      | ~ v1_relat_1(X0)
% 43.70/5.99      | k2_relat_1(X0) = X1 ),
% 43.70/5.99      inference(cnf_transformation,[],[f136]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_932,plain,
% 43.70/5.99      ( ~ v2_funct_2(X0,X1)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 43.70/5.99      | ~ v1_relat_1(X0)
% 43.70/5.99      | k2_relat_1(X0) = X1 ),
% 43.70/5.99      inference(resolution,[status(thm)],[c_22,c_43]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_944,plain,
% 43.70/5.99      ( ~ v2_funct_2(X0,X1)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 43.70/5.99      | k2_relat_1(X0) = X1 ),
% 43.70/5.99      inference(forward_subsumption_resolution,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_932,c_21]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_1019,plain,
% 43.70/5.99      ( ~ v3_funct_2(X0,X1,X2)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 43.70/5.99      | ~ v1_funct_1(X0)
% 43.70/5.99      | X3 != X0
% 43.70/5.99      | X5 != X2
% 43.70/5.99      | k2_relat_1(X3) = X5 ),
% 43.70/5.99      inference(resolution_lifted,[status(thm)],[c_33,c_944]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_1020,plain,
% 43.70/5.99      ( ~ v3_funct_2(X0,X1,X2)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 43.70/5.99      | ~ v1_funct_1(X0)
% 43.70/5.99      | k2_relat_1(X0) = X2 ),
% 43.70/5.99      inference(unflattening,[status(thm)],[c_1019]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3173,plain,
% 43.70/5.99      ( k2_relat_1(X0) = X1
% 43.70/5.99      | v3_funct_2(X0,X2,X1) != iProver_top
% 43.70/5.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 43.70/5.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X0) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4158,plain,
% 43.70/5.99      ( k2_relat_1(sK2) = sK1
% 43.70/5.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_3173]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_64,negated_conjecture,
% 43.70/5.99      ( v1_funct_1(sK2) ),
% 43.70/5.99      inference(cnf_transformation,[],[f150]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_65,plain,
% 43.70/5.99      ( v1_funct_1(sK2) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_62,negated_conjecture,
% 43.70/5.99      ( v3_funct_2(sK2,sK1,sK1) ),
% 43.70/5.99      inference(cnf_transformation,[],[f152]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_67,plain,
% 43.70/5.99      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4861,plain,
% 43.70/5.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | k2_relat_1(sK2) = sK1 ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_4158,c_65,c_67]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4862,plain,
% 43.70/5.99      ( k2_relat_1(sK2) = sK1
% 43.70/5.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top ),
% 43.70/5.99      inference(renaming,[status(thm)],[c_4861]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4868,plain,
% 43.70/5.99      ( k2_relat_1(sK2) = sK1 ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_4862]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6132,plain,
% 43.70/5.99      ( k9_relat_1(sK2,sK1) = sK1 ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_6129,c_4868]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6458,plain,
% 43.70/5.99      ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
% 43.70/5.99      inference(demodulation,[status(thm)],[c_6457,c_5892,c_6132]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_53,plain,
% 43.70/5.99      ( ~ v1_funct_2(X0,X1,X2)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ v1_funct_1(X0)
% 43.70/5.99      | ~ v2_funct_1(X0)
% 43.70/5.99      | k2_relset_1(X1,X2,X0) != X2
% 43.70/5.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 43.70/5.99      | k1_xboole_0 = X2 ),
% 43.70/5.99      inference(cnf_transformation,[],[f149]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3188,plain,
% 43.70/5.99      ( k2_relset_1(X0,X1,X2) != X1
% 43.70/5.99      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 43.70/5.99      | k1_xboole_0 = X1
% 43.70/5.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top
% 43.70/5.99      | v2_funct_1(X2) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6556,plain,
% 43.70/5.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 43.70/5.99      | sK1 = k1_xboole_0
% 43.70/5.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top
% 43.70/5.99      | v2_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_6458,c_3188]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_63,negated_conjecture,
% 43.70/5.99      ( v1_funct_2(sK2,sK1,sK1) ),
% 43.70/5.99      inference(cnf_transformation,[],[f151]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_66,plain,
% 43.70/5.99      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_68,plain,
% 43.70/5.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_34,plain,
% 43.70/5.99      ( ~ v3_funct_2(X0,X1,X2)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ v1_funct_1(X0)
% 43.70/5.99      | v2_funct_1(X0) ),
% 43.70/5.99      inference(cnf_transformation,[],[f128]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3204,plain,
% 43.70/5.99      ( v3_funct_2(X0,X1,X2) != iProver_top
% 43.70/5.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 43.70/5.99      | v1_funct_1(X0) != iProver_top
% 43.70/5.99      | v2_funct_1(X0) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_7769,plain,
% 43.70/5.99      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top
% 43.70/5.99      | v2_funct_1(sK2) = iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_3204]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_22019,plain,
% 43.70/5.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 43.70/5.99      | sK1 = k1_xboole_0 ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_6556,c_65,c_66,c_67,c_68,c_7769]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_52,plain,
% 43.70/5.99      ( ~ v1_funct_2(X0,X1,X1)
% 43.70/5.99      | ~ v3_funct_2(X0,X1,X1)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 43.70/5.99      | ~ v1_funct_1(X0)
% 43.70/5.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 43.70/5.99      inference(cnf_transformation,[],[f146]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3189,plain,
% 43.70/5.99      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 43.70/5.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 43.70/5.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 43.70/5.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 43.70/5.99      | v1_funct_1(X1) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8223,plain,
% 43.70/5.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 43.70/5.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_3189]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3475,plain,
% 43.70/5.99      ( ~ v1_funct_2(sK2,sK1,sK1)
% 43.70/5.99      | ~ v3_funct_2(sK2,sK1,sK1)
% 43.70/5.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/5.99      | ~ v1_funct_1(sK2)
% 43.70/5.99      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 43.70/5.99      inference(instantiation,[status(thm)],[c_52]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8774,plain,
% 43.70/5.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_8223,c_64,c_63,c_62,c_61,c_3475]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_46,plain,
% 43.70/5.99      ( ~ v1_funct_2(X0,X1,X1)
% 43.70/5.99      | ~ v3_funct_2(X0,X1,X1)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 43.70/5.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 43.70/5.99      | ~ v1_funct_1(X0) ),
% 43.70/5.99      inference(cnf_transformation,[],[f143]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3195,plain,
% 43.70/5.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 43.70/5.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 43.70/5.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 43.70/5.99      | v1_funct_1(X0) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8785,plain,
% 43.70/5.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 43.70/5.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_8774,c_3195]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_12985,plain,
% 43.70/5.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_8785,c_65,c_66,c_67,c_68]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_51,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 43.70/5.99      | ~ v1_funct_1(X0)
% 43.70/5.99      | ~ v1_funct_1(X3)
% 43.70/5.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 43.70/5.99      inference(cnf_transformation,[],[f145]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3190,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 43.70/5.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 43.70/5.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X5) != iProver_top
% 43.70/5.99      | v1_funct_1(X4) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9456,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_3190]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9876,plain,
% 43.70/5.99      ( v1_funct_1(X2) != iProver_top
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_9456,c_65]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9877,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top ),
% 43.70/5.99      inference(renaming,[status(thm)],[c_9876]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_12990,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_12985,c_9877]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_49,plain,
% 43.70/5.99      ( ~ v1_funct_2(X0,X1,X1)
% 43.70/5.99      | ~ v3_funct_2(X0,X1,X1)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 43.70/5.99      | ~ v1_funct_1(X0)
% 43.70/5.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 43.70/5.99      inference(cnf_transformation,[],[f140]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3192,plain,
% 43.70/5.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 43.70/5.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 43.70/5.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X0) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6762,plain,
% 43.70/5.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_3192]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_7137,plain,
% 43.70/5.99      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_6762,c_65,c_66,c_67]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8778,plain,
% 43.70/5.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 43.70/5.99      inference(demodulation,[status(thm)],[c_8774,c_7137]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_13085,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_12990,c_8778]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_44,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 43.70/5.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 43.70/5.99      | ~ v1_funct_1(X0)
% 43.70/5.99      | ~ v1_funct_1(X3) ),
% 43.70/5.99      inference(cnf_transformation,[],[f139]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3197,plain,
% 43.70/5.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 43.70/5.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 43.70/5.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 43.70/5.99      | v1_funct_1(X0) != iProver_top
% 43.70/5.99      | v1_funct_1(X3) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_57,negated_conjecture,
% 43.70/5.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 43.70/5.99      inference(cnf_transformation,[],[f157]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3186,plain,
% 43.70/5.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9455,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3)
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_3190]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_60,negated_conjecture,
% 43.70/5.99      ( v1_funct_1(sK3) ),
% 43.70/5.99      inference(cnf_transformation,[],[f154]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_69,plain,
% 43.70/5.99      ( v1_funct_1(sK3) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9739,plain,
% 43.70/5.99      ( v1_funct_1(X2) != iProver_top
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_9455,c_69]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9740,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3)
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top ),
% 43.70/5.99      inference(renaming,[status(thm)],[c_9739]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9746,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,k1_partfun1(X0,X2,X3,X1,X4,X5),sK3) = k5_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5),sK3)
% 43.70/5.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 43.70/5.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 43.70/5.99      | v1_funct_1(X5) != iProver_top
% 43.70/5.99      | v1_funct_1(X4) != iProver_top
% 43.70/5.99      | v1_funct_1(k1_partfun1(X0,X2,X3,X1,X4,X5)) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3197,c_9740]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_13614,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),sK3)
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_13085,c_9746]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_13617,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_13614,c_13085]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_45,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 43.70/5.99      | ~ v1_funct_1(X0)
% 43.70/5.99      | ~ v1_funct_1(X3)
% 43.70/5.99      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
% 43.70/5.99      inference(cnf_transformation,[],[f138]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3196,plain,
% 43.70/5.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 43.70/5.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 43.70/5.99      | v1_funct_1(X0) != iProver_top
% 43.70/5.99      | v1_funct_1(X3) != iProver_top
% 43.70/5.99      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_13088,plain,
% 43.70/5.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) = iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_13085,c_3196]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_168148,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_13617,c_65,c_66,c_67,c_68,c_8778,c_8785,c_13088]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4408,plain,
% 43.70/5.99      ( v1_relat_1(sK3) = iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_3212]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_13001,plain,
% 43.70/5.99      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_12985,c_3212]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_14,plain,
% 43.70/5.99      ( ~ v1_relat_1(X0)
% 43.70/5.99      | ~ v1_relat_1(X1)
% 43.70/5.99      | ~ v1_relat_1(X2)
% 43.70/5.99      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 43.70/5.99      inference(cnf_transformation,[],[f108]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3218,plain,
% 43.70/5.99      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 43.70/5.99      | v1_relat_1(X0) != iProver_top
% 43.70/5.99      | v1_relat_1(X1) != iProver_top
% 43.70/5.99      | v1_relat_1(X2) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_13294,plain,
% 43.70/5.99      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
% 43.70/5.99      | v1_relat_1(X0) != iProver_top
% 43.70/5.99      | v1_relat_1(X1) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_13001,c_3218]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_28090,plain,
% 43.70/5.99      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
% 43.70/5.99      | v1_relat_1(X0) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_4409,c_13294]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_28499,plain,
% 43.70/5.99      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_4408,c_28090]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9750,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) = k5_relat_1(sK2,sK3)
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_9740]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_27,plain,
% 43.70/5.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 43.70/5.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 43.70/5.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 43.70/5.99      | X3 = X2 ),
% 43.70/5.99      inference(cnf_transformation,[],[f120]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_56,negated_conjecture,
% 43.70/5.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 43.70/5.99      inference(cnf_transformation,[],[f158]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_987,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | X3 = X0
% 43.70/5.99      | k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) != X0
% 43.70/5.99      | k6_partfun1(sK1) != X3
% 43.70/5.99      | sK1 != X2
% 43.70/5.99      | sK1 != X1 ),
% 43.70/5.99      inference(resolution_lifted,[status(thm)],[c_27,c_56]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_988,plain,
% 43.70/5.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/5.99      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/5.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) ),
% 43.70/5.99      inference(unflattening,[status(thm)],[c_987]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_50,plain,
% 43.70/5.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 43.70/5.99      inference(cnf_transformation,[],[f144]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_996,plain,
% 43.70/5.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/5.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) ),
% 43.70/5.99      inference(forward_subsumption_resolution,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_988,c_50]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3174,plain,
% 43.70/5.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3)
% 43.70/5.99      | m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3305,plain,
% 43.70/5.99      ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/5.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/5.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/5.99      | ~ v1_funct_1(sK2)
% 43.70/5.99      | ~ v1_funct_1(sK3) ),
% 43.70/5.99      inference(instantiation,[status(thm)],[c_44]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3856,plain,
% 43.70/5.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_3174,c_64,c_61,c_60,c_57,c_996,c_3305]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9751,plain,
% 43.70/5.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK1)
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_9750,c_3856]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_10716,plain,
% 43.70/5.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK1) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_9751,c_65]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_28508,plain,
% 43.70/5.99      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK1)) ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_28499,c_10716]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8372,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_2(X0,X1)) = X0
% 43.70/5.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 43.70/5.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 43.70/5.99      | v3_funct_2(k2_funct_2(X0,X1),X0,X0) != iProver_top
% 43.70/5.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 43.70/5.99      | v1_funct_1(X1) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3195,c_3173]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_41913,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_2(sK1,sK2)) = sK1
% 43.70/5.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_8774,c_8372]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_41990,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_1(sK2)) = sK1
% 43.70/5.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_41913,c_8774]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_47,plain,
% 43.70/5.99      ( ~ v1_funct_2(X0,X1,X1)
% 43.70/5.99      | ~ v3_funct_2(X0,X1,X1)
% 43.70/5.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 43.70/5.99      | ~ v1_funct_1(X0) ),
% 43.70/5.99      inference(cnf_transformation,[],[f142]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3194,plain,
% 43.70/5.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 43.70/5.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 43.70/5.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 43.70/5.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X0) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8103,plain,
% 43.70/5.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 43.70/5.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 43.70/5.99      | v1_funct_1(sK2) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3182,c_3194]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8919,plain,
% 43.70/5.99      ( v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_8103,c_65,c_66,c_67]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8923,plain,
% 43.70/5.99      ( v3_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_8919,c_8774]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_13002,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_1(sK2)) = sK1
% 43.70/5.99      | v3_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_12985,c_3173]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_42495,plain,
% 43.70/5.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | k2_relat_1(k2_funct_1(sK2)) = sK1 ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_41990,c_8778,c_8923,c_13002]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_42496,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_1(sK2)) = sK1
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top ),
% 43.70/5.99      inference(renaming,[status(thm)],[c_42495]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_42502,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_1(sK2)) = sK1 ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_12985,c_42496]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_18,plain,
% 43.70/5.99      ( ~ v1_relat_1(X0)
% 43.70/5.99      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 43.70/5.99      inference(cnf_transformation,[],[f161]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3214,plain,
% 43.70/5.99      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 43.70/5.99      | v1_relat_1(X0) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_13297,plain,
% 43.70/5.99      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_13001,c_3214]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_42789,plain,
% 43.70/5.99      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK1)) = k2_funct_1(sK2) ),
% 43.70/5.99      inference(demodulation,[status(thm)],[c_42502,c_13297]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_168150,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k2_funct_1(sK2) ),
% 43.70/5.99      inference(light_normalisation,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_168148,c_28508,c_42789]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_168159,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k6_partfun1(sK1),sK3) = k2_funct_1(sK2)
% 43.70/5.99      | sK1 = k1_xboole_0 ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_22019,c_168150]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6456,plain,
% 43.70/5.99      ( k7_relset_1(sK1,sK1,sK3,sK1) = k2_relset_1(sK1,sK1,sK3) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_3207]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4943,plain,
% 43.70/5.99      ( k7_relat_1(sK3,sK1) = sK3 ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_3176]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4951,plain,
% 43.70/5.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_4408,c_3219]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_5576,plain,
% 43.70/5.99      ( k9_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_4943,c_4951]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4157,plain,
% 43.70/5.99      ( k2_relat_1(sK3) = sK1
% 43.70/5.99      | v3_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_3173]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_58,negated_conjecture,
% 43.70/5.99      ( v3_funct_2(sK3,sK1,sK1) ),
% 43.70/5.99      inference(cnf_transformation,[],[f156]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_71,plain,
% 43.70/5.99      ( v3_funct_2(sK3,sK1,sK1) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4764,plain,
% 43.70/5.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | k2_relat_1(sK3) = sK1 ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_4157,c_69,c_71]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4765,plain,
% 43.70/5.99      ( k2_relat_1(sK3) = sK1
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top ),
% 43.70/5.99      inference(renaming,[status(thm)],[c_4764]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4771,plain,
% 43.70/5.99      ( k2_relat_1(sK3) = sK1 ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_4765]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_5579,plain,
% 43.70/5.99      ( k9_relat_1(sK3,sK1) = sK1 ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_5576,c_4771]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_5891,plain,
% 43.70/5.99      ( k7_relset_1(sK1,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_3210]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6459,plain,
% 43.70/5.99      ( k2_relset_1(sK1,sK1,sK3) = sK1 ),
% 43.70/5.99      inference(demodulation,[status(thm)],[c_6456,c_5579,c_5891]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_54,plain,
% 43.70/5.99      ( ~ v1_funct_2(X0,X1,X2)
% 43.70/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | ~ v1_funct_1(X0)
% 43.70/5.99      | ~ v2_funct_1(X0)
% 43.70/5.99      | k2_relset_1(X1,X2,X0) != X2
% 43.70/5.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 43.70/5.99      | k1_xboole_0 = X2 ),
% 43.70/5.99      inference(cnf_transformation,[],[f148]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3187,plain,
% 43.70/5.99      ( k2_relset_1(X0,X1,X2) != X1
% 43.70/5.99      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 43.70/5.99      | k1_xboole_0 = X1
% 43.70/5.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top
% 43.70/5.99      | v2_funct_1(X2) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6583,plain,
% 43.70/5.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 43.70/5.99      | sK1 = k1_xboole_0
% 43.70/5.99      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top
% 43.70/5.99      | v2_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_6459,c_3187]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_59,negated_conjecture,
% 43.70/5.99      ( v1_funct_2(sK3,sK1,sK1) ),
% 43.70/5.99      inference(cnf_transformation,[],[f155]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6585,plain,
% 43.70/5.99      ( ~ v1_funct_2(sK3,sK1,sK1)
% 43.70/5.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/5.99      | ~ v1_funct_1(sK3)
% 43.70/5.99      | ~ v2_funct_1(sK3)
% 43.70/5.99      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 43.70/5.99      | sK1 = k1_xboole_0 ),
% 43.70/5.99      inference(predicate_to_equality_rev,[status(thm)],[c_6583]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4679,plain,
% 43.70/5.99      ( ~ v3_funct_2(sK3,X0,X1)
% 43.70/5.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 43.70/5.99      | ~ v1_funct_1(sK3)
% 43.70/5.99      | v2_funct_1(sK3) ),
% 43.70/5.99      inference(instantiation,[status(thm)],[c_34]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_7075,plain,
% 43.70/5.99      ( ~ v3_funct_2(sK3,sK1,sK1)
% 43.70/5.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/5.99      | ~ v1_funct_1(sK3)
% 43.70/5.99      | v2_funct_1(sK3) ),
% 43.70/5.99      inference(instantiation,[status(thm)],[c_4679]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_23590,plain,
% 43.70/5.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 43.70/5.99      | sK1 = k1_xboole_0 ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_6583,c_60,c_59,c_58,c_57,c_6585,c_7075]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8222,plain,
% 43.70/5.99      ( k2_funct_2(sK1,sK3) = k2_funct_1(sK3)
% 43.70/5.99      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_3189]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_70,plain,
% 43.70/5.99      ( v1_funct_2(sK3,sK1,sK1) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8763,plain,
% 43.70/5.99      ( k2_funct_2(sK1,sK3) = k2_funct_1(sK3) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_8222,c_69,c_70,c_71]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8771,plain,
% 43.70/5.99      ( v1_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_8763,c_3195]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_72,plain,
% 43.70/5.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_12882,plain,
% 43.70/5.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_8771,c_69,c_70,c_71,c_72]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_12900,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK3)) = k5_relat_1(X2,k2_funct_1(sK3))
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_12882,c_3190]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6761,plain,
% 43.70/5.99      ( v1_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_2(sK1,sK3)) = iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_3192]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_7130,plain,
% 43.70/5.99      ( v1_funct_1(k2_funct_2(sK1,sK3)) = iProver_top ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_6761,c_69,c_70,c_71]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8767,plain,
% 43.70/5.99      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top ),
% 43.70/5.99      inference(demodulation,[status(thm)],[c_8763,c_7130]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_39658,plain,
% 43.70/5.99      ( v1_funct_1(X2) != iProver_top
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK3)) = k5_relat_1(X2,k2_funct_1(sK3)) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_12900,c_8767]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_39659,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK3)) = k5_relat_1(X2,k2_funct_1(sK3))
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top ),
% 43.70/5.99      inference(renaming,[status(thm)],[c_39658]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_39668,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,k2_funct_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_39659]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_39945,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,k2_funct_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_39668,c_69]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9639,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,X2,X3,X4,k1_partfun1(X2,X5,X6,X3,X7,X8)) = k5_relat_1(X4,k1_partfun1(X2,X5,X6,X3,X7,X8))
% 43.70/5.99      | m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X3))) != iProver_top
% 43.70/5.99      | m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X5))) != iProver_top
% 43.70/5.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X8) != iProver_top
% 43.70/5.99      | v1_funct_1(X7) != iProver_top
% 43.70/5.99      | v1_funct_1(X4) != iProver_top
% 43.70/5.99      | v1_funct_1(k1_partfun1(X2,X5,X6,X3,X7,X8)) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3197,c_3190]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_71469,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,k1_partfun1(sK1,sK1,sK1,sK1,sK3,k2_funct_1(sK3))) = k5_relat_1(X2,k1_partfun1(sK1,sK1,sK1,sK1,sK3,k2_funct_1(sK3)))
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top
% 43.70/5.99      | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_39945,c_9639]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_71496,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(X2,k5_relat_1(sK3,k2_funct_1(sK3)))
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top
% 43.70/5.99      | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_71469,c_39945]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_39948,plain,
% 43.70/5.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) = iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_39945,c_3196]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_39947,plain,
% 43.70/5.99      ( m1_subset_1(k5_relat_1(sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_39945,c_3197]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_40201,plain,
% 43.70/5.99      ( m1_subset_1(k5_relat_1(sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_39947,c_69,c_70,c_71,c_72,c_8767,c_8771]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_40222,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(X2,k5_relat_1(sK3,k2_funct_1(sK3)))
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top
% 43.70/5.99      | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_40201,c_3190]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_79365,plain,
% 43.70/5.99      ( v1_funct_1(X2) != iProver_top
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | k1_partfun1(X0,X1,sK1,sK1,X2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(X2,k5_relat_1(sK3,k2_funct_1(sK3))) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_71496,c_69,c_70,c_71,c_72,c_8767,c_8771,c_39948,
% 43.70/5.99                 c_40222]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_79366,plain,
% 43.70/5.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(X2,k5_relat_1(sK3,k2_funct_1(sK3)))
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 43.70/5.99      | v1_funct_1(X2) != iProver_top ),
% 43.70/5.99      inference(renaming,[status(thm)],[c_79365]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_79375,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_79366]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_79711,plain,
% 43.70/5.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))) ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_79375,c_69]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_7,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 43.70/5.99      inference(cnf_transformation,[],[f100]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3222,plain,
% 43.70/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 43.70/5.99      | r1_tarski(X0,X1) = iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_9626,plain,
% 43.70/5.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 43.70/5.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 43.70/5.99      | r1_tarski(k1_partfun1(X4,X5,X1,X2,X3,X0),k2_zfmisc_1(X4,X2)) = iProver_top
% 43.70/5.99      | v1_funct_1(X0) != iProver_top
% 43.70/5.99      | v1_funct_1(X3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3197,c_3222]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_79716,plain,
% 43.70/5.99      ( m1_subset_1(k5_relat_1(sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | r1_tarski(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),k2_zfmisc_1(sK1,sK1)) = iProver_top
% 43.70/5.99      | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_79711,c_9626]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_80032,plain,
% 43.70/5.99      ( r1_tarski(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),k2_zfmisc_1(sK1,sK1)) = iProver_top ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_79716,c_69,c_70,c_71,c_72,c_8767,c_8771,c_39947,
% 43.70/5.99                 c_39948]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_6,plain,
% 43.70/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.70/5.99      inference(cnf_transformation,[],[f101]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3223,plain,
% 43.70/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 43.70/5.99      | r1_tarski(X0,X1) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_24,plain,
% 43.70/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/5.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 43.70/5.99      inference(cnf_transformation,[],[f118]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3211,plain,
% 43.70/5.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 43.70/5.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_5880,plain,
% 43.70/5.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 43.70/5.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3223,c_3211]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_80064,plain,
% 43.70/5.99      ( k1_relset_1(sK1,sK1,k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_80032,c_5880]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_139476,plain,
% 43.70/5.99      ( k1_relset_1(sK1,sK1,k5_relat_1(sK3,k6_partfun1(sK1))) = k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))))
% 43.70/5.99      | sK1 = k1_xboole_0 ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_23590,c_80064]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_4596,plain,
% 43.70/5.99      ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_4408,c_3214]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_5358,plain,
% 43.70/5.99      ( k5_relat_1(sK3,k6_partfun1(sK1)) = sK3 ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_4596,c_4596,c_4771]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_5882,plain,
% 43.70/5.99      ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_3211]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_139478,plain,
% 43.70/5.99      ( k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = k1_relat_1(sK3)
% 43.70/5.99      | sK1 = k1_xboole_0 ),
% 43.70/5.99      inference(light_normalisation,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_139476,c_5358,c_5882]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_41914,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_2(sK1,sK3)) = sK1
% 43.70/5.99      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(k2_funct_2(sK1,sK3),sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_2(sK1,sK3)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_8763,c_8372]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_41989,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_1(sK3)) = sK1
% 43.70/5.99      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(k2_funct_1(sK3),sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_41914,c_8763]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8102,plain,
% 43.70/5.99      ( v1_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | v3_funct_2(k2_funct_2(sK1,sK3),sK1,sK1) = iProver_top
% 43.70/5.99      | v3_funct_2(sK3,sK1,sK1) != iProver_top
% 43.70/5.99      | v1_funct_1(sK3) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_3186,c_3194]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8912,plain,
% 43.70/5.99      ( v3_funct_2(k2_funct_2(sK1,sK3),sK1,sK1) = iProver_top ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_8102,c_69,c_70,c_71]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_8916,plain,
% 43.70/5.99      ( v3_funct_2(k2_funct_1(sK3),sK1,sK1) = iProver_top ),
% 43.70/5.99      inference(light_normalisation,[status(thm)],[c_8912,c_8763]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_12899,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_1(sK3)) = sK1
% 43.70/5.99      | v3_funct_2(k2_funct_1(sK3),sK1,sK1) != iProver_top
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_12882,c_3173]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_42486,plain,
% 43.70/5.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 43.70/5.99      | k2_relat_1(k2_funct_1(sK3)) = sK1 ),
% 43.70/5.99      inference(global_propositional_subsumption,
% 43.70/5.99                [status(thm)],
% 43.70/5.99                [c_41989,c_8767,c_8916,c_12899]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_42487,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_1(sK3)) = sK1
% 43.70/5.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top ),
% 43.70/5.99      inference(renaming,[status(thm)],[c_42486]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_42493,plain,
% 43.70/5.99      ( k2_relat_1(k2_funct_1(sK3)) = sK1 ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_12882,c_42487]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_15,plain,
% 43.70/5.99      ( ~ v1_relat_1(X0)
% 43.70/5.99      | k2_relat_1(X0) != k1_xboole_0
% 43.70/5.99      | k1_xboole_0 = X0 ),
% 43.70/5.99      inference(cnf_transformation,[],[f110]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_3217,plain,
% 43.70/5.99      ( k2_relat_1(X0) != k1_xboole_0
% 43.70/5.99      | k1_xboole_0 = X0
% 43.70/5.99      | v1_relat_1(X0) != iProver_top ),
% 43.70/5.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_42785,plain,
% 43.70/5.99      ( k2_funct_1(sK3) = k1_xboole_0
% 43.70/5.99      | sK1 != k1_xboole_0
% 43.70/5.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 43.70/5.99      inference(superposition,[status(thm)],[c_42493,c_3217]) ).
% 43.70/5.99  
% 43.70/5.99  cnf(c_26,plain,
% 43.70/5.99      ( r2_relset_1(X0,X1,X2,X2)
% 43.70/5.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 43.70/5.99      inference(cnf_transformation,[],[f164]) ).
% 43.70/5.99  
% 43.70/6.00  cnf(c_55,negated_conjecture,
% 43.70/6.00      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 43.70/6.00      inference(cnf_transformation,[],[f159]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_977,plain,
% 43.70/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/6.00      | k2_funct_2(sK1,sK2) != X0
% 43.70/6.00      | sK3 != X0
% 43.70/6.00      | sK1 != X2
% 43.70/6.00      | sK1 != X1 ),
% 43.70/6.00      inference(resolution_lifted,[status(thm)],[c_26,c_55]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_978,plain,
% 43.70/6.00      ( ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/6.00      | sK3 != k2_funct_2(sK1,sK2) ),
% 43.70/6.00      inference(unflattening,[status(thm)],[c_977]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_5134,plain,
% 43.70/6.00      ( sK3 = k1_xboole_0
% 43.70/6.00      | sK1 != k1_xboole_0
% 43.70/6.00      | v1_relat_1(sK3) != iProver_top ),
% 43.70/6.00      inference(superposition,[status(thm)],[c_4771,c_3217]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_6579,plain,
% 43.70/6.00      ( ~ v1_funct_2(sK2,sK1,sK1)
% 43.70/6.00      | ~ v3_funct_2(sK2,sK1,sK1)
% 43.70/6.00      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/6.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 43.70/6.00      | ~ v1_funct_1(sK2) ),
% 43.70/6.00      inference(instantiation,[status(thm)],[c_46]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_1978,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_3300,plain,
% 43.70/6.00      ( k2_funct_2(sK1,sK2) != X0
% 43.70/6.00      | sK3 != X0
% 43.70/6.00      | sK3 = k2_funct_2(sK1,sK2) ),
% 43.70/6.00      inference(instantiation,[status(thm)],[c_1978]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_7909,plain,
% 43.70/6.00      ( k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
% 43.70/6.00      | sK3 = k2_funct_2(sK1,sK2)
% 43.70/6.00      | sK3 != k2_funct_1(sK2) ),
% 43.70/6.00      inference(instantiation,[status(thm)],[c_3300]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_3329,plain,
% 43.70/6.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 43.70/6.00      inference(instantiation,[status(thm)],[c_1978]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_8140,plain,
% 43.70/6.00      ( k2_funct_1(sK2) != X0 | sK3 != X0 | sK3 = k2_funct_1(sK2) ),
% 43.70/6.00      inference(instantiation,[status(thm)],[c_3329]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_8143,plain,
% 43.70/6.00      ( k2_funct_1(sK2) != k1_xboole_0
% 43.70/6.00      | sK3 = k2_funct_1(sK2)
% 43.70/6.00      | sK3 != k1_xboole_0 ),
% 43.70/6.00      inference(instantiation,[status(thm)],[c_8140]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_42790,plain,
% 43.70/6.00      ( k2_funct_1(sK2) = k1_xboole_0
% 43.70/6.00      | sK1 != k1_xboole_0
% 43.70/6.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 43.70/6.00      inference(superposition,[status(thm)],[c_42502,c_3217]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_46990,plain,
% 43.70/6.00      ( sK1 != k1_xboole_0 ),
% 43.70/6.00      inference(global_propositional_subsumption,
% 43.70/6.00                [status(thm)],
% 43.70/6.00                [c_42785,c_64,c_63,c_62,c_61,c_978,c_3475,c_4408,c_5134,
% 43.70/6.00                 c_6579,c_7909,c_8143,c_13001,c_42790]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_139480,plain,
% 43.70/6.00      ( k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = k1_relat_1(sK3) ),
% 43.70/6.00      inference(global_propositional_subsumption,
% 43.70/6.00                [status(thm)],
% 43.70/6.00                [c_139478,c_64,c_63,c_62,c_61,c_978,c_3475,c_4408,c_5134,
% 43.70/6.00                 c_6579,c_7909,c_8143,c_13001,c_42790]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_41,plain,
% 43.70/6.00      ( ~ v1_funct_2(X0,X1,X2)
% 43.70/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.70/6.00      | k1_relset_1(X1,X2,X0) = X1
% 43.70/6.00      | k1_xboole_0 = X2 ),
% 43.70/6.00      inference(cnf_transformation,[],[f130]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_3198,plain,
% 43.70/6.00      ( k1_relset_1(X0,X1,X2) = X0
% 43.70/6.00      | k1_xboole_0 = X1
% 43.70/6.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 43.70/6.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 43.70/6.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_9627,plain,
% 43.70/6.00      ( k1_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = X0
% 43.70/6.00      | k1_xboole_0 = X1
% 43.70/6.00      | v1_funct_2(k1_partfun1(X0,X2,X3,X1,X4,X5),X0,X1) != iProver_top
% 43.70/6.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 43.70/6.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 43.70/6.00      | v1_funct_1(X5) != iProver_top
% 43.70/6.00      | v1_funct_1(X4) != iProver_top ),
% 43.70/6.00      inference(superposition,[status(thm)],[c_3197,c_3198]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_79719,plain,
% 43.70/6.00      ( k1_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = sK1
% 43.70/6.00      | sK1 = k1_xboole_0
% 43.70/6.00      | v1_funct_2(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),sK1,sK1) != iProver_top
% 43.70/6.00      | m1_subset_1(k5_relat_1(sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/6.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/6.00      | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
% 43.70/6.00      | v1_funct_1(sK3) != iProver_top ),
% 43.70/6.00      inference(superposition,[status(thm)],[c_79711,c_9627]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_79728,plain,
% 43.70/6.00      ( k1_relset_1(sK1,sK1,k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = sK1
% 43.70/6.00      | sK1 = k1_xboole_0
% 43.70/6.00      | v1_funct_2(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),sK1,sK1) != iProver_top
% 43.70/6.00      | m1_subset_1(k5_relat_1(sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/6.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/6.00      | v1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3))) != iProver_top
% 43.70/6.00      | v1_funct_1(sK3) != iProver_top ),
% 43.70/6.00      inference(light_normalisation,[status(thm)],[c_79719,c_79711]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_130232,plain,
% 43.70/6.00      ( k1_relset_1(sK1,sK1,k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = sK1
% 43.70/6.00      | v1_funct_2(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),sK1,sK1) != iProver_top ),
% 43.70/6.00      inference(global_propositional_subsumption,
% 43.70/6.00                [status(thm)],
% 43.70/6.00                [c_79728,c_64,c_63,c_62,c_61,c_69,c_70,c_71,c_72,c_978,
% 43.70/6.00                 c_3475,c_4408,c_5134,c_6579,c_7909,c_8143,c_8767,c_8771,
% 43.70/6.00                 c_13001,c_39947,c_39948,c_42790]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_130236,plain,
% 43.70/6.00      ( k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3)))) = sK1
% 43.70/6.00      | v1_funct_2(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),sK1,sK1) != iProver_top ),
% 43.70/6.00      inference(demodulation,[status(thm)],[c_130232,c_80064]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_139483,plain,
% 43.70/6.00      ( k1_relat_1(sK3) = sK1
% 43.70/6.00      | v1_funct_2(k5_relat_1(sK3,k5_relat_1(sK3,k2_funct_1(sK3))),sK1,sK1) != iProver_top ),
% 43.70/6.00      inference(demodulation,[status(thm)],[c_139480,c_130236]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_7701,plain,
% 43.70/6.00      ( k1_relset_1(sK1,sK1,sK3) = sK1
% 43.70/6.00      | sK1 = k1_xboole_0
% 43.70/6.00      | v1_funct_2(sK3,sK1,sK1) != iProver_top ),
% 43.70/6.00      inference(superposition,[status(thm)],[c_3186,c_3198]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_7704,plain,
% 43.70/6.00      ( k1_relat_1(sK3) = sK1
% 43.70/6.00      | sK1 = k1_xboole_0
% 43.70/6.00      | v1_funct_2(sK3,sK1,sK1) != iProver_top ),
% 43.70/6.00      inference(demodulation,[status(thm)],[c_7701,c_5882]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_142729,plain,
% 43.70/6.00      ( k1_relat_1(sK3) = sK1 ),
% 43.70/6.00      inference(global_propositional_subsumption,
% 43.70/6.00                [status(thm)],
% 43.70/6.00                [c_139483,c_64,c_63,c_62,c_61,c_70,c_978,c_3475,c_4408,
% 43.70/6.00                 c_5134,c_6579,c_7704,c_7909,c_8143,c_13001,c_42790]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_17,plain,
% 43.70/6.00      ( ~ v1_relat_1(X0)
% 43.70/6.00      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 43.70/6.00      inference(cnf_transformation,[],[f160]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_3215,plain,
% 43.70/6.00      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 43.70/6.00      | v1_relat_1(X0) != iProver_top ),
% 43.70/6.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_4595,plain,
% 43.70/6.00      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 43.70/6.00      inference(superposition,[status(thm)],[c_4408,c_3215]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_142749,plain,
% 43.70/6.00      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 43.70/6.00      inference(demodulation,[status(thm)],[c_142729,c_4595]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_9445,plain,
% 43.70/6.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/6.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 43.70/6.00      | v1_funct_1(k6_partfun1(sK1)) = iProver_top
% 43.70/6.00      | v1_funct_1(sK2) != iProver_top
% 43.70/6.00      | v1_funct_1(sK3) != iProver_top ),
% 43.70/6.00      inference(superposition,[status(thm)],[c_3856,c_3196]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_54746,plain,
% 43.70/6.00      ( v1_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 43.70/6.00      inference(global_propositional_subsumption,
% 43.70/6.00                [status(thm)],
% 43.70/6.00                [c_9445,c_65,c_68,c_69,c_72]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_3191,plain,
% 43.70/6.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 43.70/6.00      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_9748,plain,
% 43.70/6.00      ( k1_partfun1(X0,X0,sK1,sK1,k6_partfun1(X0),sK3) = k5_relat_1(k6_partfun1(X0),sK3)
% 43.70/6.00      | v1_funct_1(k6_partfun1(X0)) != iProver_top ),
% 43.70/6.00      inference(superposition,[status(thm)],[c_3191,c_9740]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_54756,plain,
% 43.70/6.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k6_partfun1(sK1),sK3) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 43.70/6.00      inference(superposition,[status(thm)],[c_54746,c_9748]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_142795,plain,
% 43.70/6.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k6_partfun1(sK1),sK3) = sK3 ),
% 43.70/6.00      inference(demodulation,[status(thm)],[c_142749,c_54756]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_168186,plain,
% 43.70/6.00      ( k2_funct_1(sK2) = sK3 | sK1 = k1_xboole_0 ),
% 43.70/6.00      inference(light_normalisation,[status(thm)],[c_168159,c_142795]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_3175,plain,
% 43.70/6.00      ( sK3 != k2_funct_2(sK1,sK2)
% 43.70/6.00      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 43.70/6.00      inference(predicate_to_equality,[status(thm)],[c_978]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(c_8780,plain,
% 43.70/6.00      ( k2_funct_1(sK2) != sK3
% 43.70/6.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 43.70/6.00      inference(demodulation,[status(thm)],[c_8774,c_3175]) ).
% 43.70/6.00  
% 43.70/6.00  cnf(contradiction,plain,
% 43.70/6.00      ( $false ),
% 43.70/6.00      inference(minisat,
% 43.70/6.00                [status(thm)],
% 43.70/6.00                [c_168186,c_46990,c_8785,c_8780,c_68,c_67,c_66,c_65]) ).
% 43.70/6.00  
% 43.70/6.00  
% 43.70/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 43.70/6.00  
% 43.70/6.00  ------                               Statistics
% 43.70/6.00  
% 43.70/6.00  ------ General
% 43.70/6.00  
% 43.70/6.00  abstr_ref_over_cycles:                  0
% 43.70/6.00  abstr_ref_under_cycles:                 0
% 43.70/6.00  gc_basic_clause_elim:                   0
% 43.70/6.00  forced_gc_time:                         0
% 43.70/6.00  parsing_time:                           0.012
% 43.70/6.00  unif_index_cands_time:                  0.
% 43.70/6.00  unif_index_add_time:                    0.
% 43.70/6.00  orderings_time:                         0.
% 43.70/6.00  out_proof_time:                         0.072
% 43.70/6.00  total_time:                             5.336
% 43.70/6.00  num_of_symbols:                         65
% 43.70/6.00  num_of_terms:                           134740
% 43.70/6.00  
% 43.70/6.00  ------ Preprocessing
% 43.70/6.00  
% 43.70/6.00  num_of_splits:                          0
% 43.70/6.00  num_of_split_atoms:                     0
% 43.70/6.00  num_of_reused_defs:                     0
% 43.70/6.00  num_eq_ax_congr_red:                    70
% 43.70/6.00  num_of_sem_filtered_clauses:            1
% 43.70/6.00  num_of_subtypes:                        0
% 43.70/6.00  monotx_restored_types:                  0
% 43.70/6.00  sat_num_of_epr_types:                   0
% 43.70/6.00  sat_num_of_non_cyclic_types:            0
% 43.70/6.00  sat_guarded_non_collapsed_types:        0
% 43.70/6.00  num_pure_diseq_elim:                    0
% 43.70/6.00  simp_replaced_by:                       0
% 43.70/6.00  res_preprocessed:                       284
% 43.70/6.00  prep_upred:                             0
% 43.70/6.00  prep_unflattend:                        47
% 43.70/6.00  smt_new_axioms:                         0
% 43.70/6.00  pred_elim_cands:                        10
% 43.70/6.00  pred_elim:                              4
% 43.70/6.00  pred_elim_cl:                           5
% 43.70/6.00  pred_elim_cycles:                       12
% 43.70/6.00  merged_defs:                            8
% 43.70/6.00  merged_defs_ncl:                        0
% 43.70/6.00  bin_hyper_res:                          10
% 43.70/6.00  prep_cycles:                            4
% 43.70/6.00  pred_elim_time:                         0.014
% 43.70/6.00  splitting_time:                         0.
% 43.70/6.00  sem_filter_time:                        0.
% 43.70/6.00  monotx_time:                            0.001
% 43.70/6.00  subtype_inf_time:                       0.
% 43.70/6.00  
% 43.70/6.00  ------ Problem properties
% 43.70/6.00  
% 43.70/6.00  clauses:                                59
% 43.70/6.00  conjectures:                            8
% 43.70/6.00  epr:                                    11
% 43.70/6.00  horn:                                   52
% 43.70/6.00  ground:                                 12
% 43.70/6.00  unary:                                  13
% 43.70/6.00  binary:                                 21
% 43.70/6.00  lits:                                   162
% 43.70/6.00  lits_eq:                                40
% 43.70/6.00  fd_pure:                                0
% 43.70/6.00  fd_pseudo:                              0
% 43.70/6.00  fd_cond:                                7
% 43.70/6.00  fd_pseudo_cond:                         2
% 43.70/6.00  ac_symbols:                             0
% 43.70/6.00  
% 43.70/6.00  ------ Propositional Solver
% 43.70/6.00  
% 43.70/6.00  prop_solver_calls:                      61
% 43.70/6.00  prop_fast_solver_calls:                 8476
% 43.70/6.00  smt_solver_calls:                       0
% 43.70/6.00  smt_fast_solver_calls:                  0
% 43.70/6.00  prop_num_of_clauses:                    60850
% 43.70/6.00  prop_preprocess_simplified:             116448
% 43.70/6.00  prop_fo_subsumed:                       1999
% 43.70/6.00  prop_solver_time:                       0.
% 43.70/6.00  smt_solver_time:                        0.
% 43.70/6.00  smt_fast_solver_time:                   0.
% 43.70/6.00  prop_fast_solver_time:                  0.
% 43.70/6.00  prop_unsat_core_time:                   0.007
% 43.70/6.00  
% 43.70/6.00  ------ QBF
% 43.70/6.00  
% 43.70/6.00  qbf_q_res:                              0
% 43.70/6.00  qbf_num_tautologies:                    0
% 43.70/6.00  qbf_prep_cycles:                        0
% 43.70/6.00  
% 43.70/6.00  ------ BMC1
% 43.70/6.00  
% 43.70/6.00  bmc1_current_bound:                     -1
% 43.70/6.00  bmc1_last_solved_bound:                 -1
% 43.70/6.00  bmc1_unsat_core_size:                   -1
% 43.70/6.00  bmc1_unsat_core_parents_size:           -1
% 43.70/6.00  bmc1_merge_next_fun:                    0
% 43.70/6.00  bmc1_unsat_core_clauses_time:           0.
% 43.70/6.00  
% 43.70/6.00  ------ Instantiation
% 43.70/6.00  
% 43.70/6.00  inst_num_of_clauses:                    12575
% 43.70/6.00  inst_num_in_passive:                    6913
% 43.70/6.00  inst_num_in_active:                     7828
% 43.70/6.00  inst_num_in_unprocessed:                195
% 43.70/6.00  inst_num_of_loops:                      8549
% 43.70/6.00  inst_num_of_learning_restarts:          1
% 43.70/6.00  inst_num_moves_active_passive:          715
% 43.70/6.00  inst_lit_activity:                      0
% 43.70/6.00  inst_lit_activity_moves:                1
% 43.70/6.00  inst_num_tautologies:                   0
% 43.70/6.00  inst_num_prop_implied:                  0
% 43.70/6.00  inst_num_existing_simplified:           0
% 43.70/6.00  inst_num_eq_res_simplified:             0
% 43.70/6.00  inst_num_child_elim:                    0
% 43.70/6.00  inst_num_of_dismatching_blockings:      18243
% 43.70/6.00  inst_num_of_non_proper_insts:           23733
% 43.70/6.00  inst_num_of_duplicates:                 0
% 43.70/6.00  inst_inst_num_from_inst_to_res:         0
% 43.70/6.00  inst_dismatching_checking_time:         0.
% 43.70/6.00  
% 43.70/6.00  ------ Resolution
% 43.70/6.00  
% 43.70/6.00  res_num_of_clauses:                     80
% 43.70/6.00  res_num_in_passive:                     80
% 43.70/6.00  res_num_in_active:                      0
% 43.70/6.00  res_num_of_loops:                       288
% 43.70/6.00  res_forward_subset_subsumed:            470
% 43.70/6.00  res_backward_subset_subsumed:           24
% 43.70/6.00  res_forward_subsumed:                   0
% 43.70/6.00  res_backward_subsumed:                  0
% 43.70/6.00  res_forward_subsumption_resolution:     4
% 43.70/6.00  res_backward_subsumption_resolution:    0
% 43.70/6.00  res_clause_to_clause_subsumption:       14196
% 43.70/6.00  res_orphan_elimination:                 0
% 43.70/6.00  res_tautology_del:                      1566
% 43.70/6.00  res_num_eq_res_simplified:              1
% 43.70/6.00  res_num_sel_changes:                    0
% 43.70/6.00  res_moves_from_active_to_pass:          0
% 43.70/6.00  
% 43.70/6.00  ------ Superposition
% 43.70/6.00  
% 43.70/6.00  sup_time_total:                         0.
% 43.70/6.00  sup_time_generating:                    0.
% 43.70/6.00  sup_time_sim_full:                      0.
% 43.70/6.00  sup_time_sim_immed:                     0.
% 43.70/6.00  
% 43.70/6.00  sup_num_of_clauses:                     6874
% 43.70/6.00  sup_num_in_active:                      1567
% 43.70/6.00  sup_num_in_passive:                     5307
% 43.70/6.00  sup_num_of_loops:                       1709
% 43.70/6.00  sup_fw_superposition:                   5187
% 43.70/6.00  sup_bw_superposition:                   4631
% 43.70/6.00  sup_immediate_simplified:               3777
% 43.70/6.00  sup_given_eliminated:                   3
% 43.70/6.00  comparisons_done:                       0
% 43.70/6.00  comparisons_avoided:                    14
% 43.70/6.00  
% 43.70/6.00  ------ Simplifications
% 43.70/6.00  
% 43.70/6.00  
% 43.70/6.00  sim_fw_subset_subsumed:                 159
% 43.70/6.00  sim_bw_subset_subsumed:                 411
% 43.70/6.00  sim_fw_subsumed:                        153
% 43.70/6.00  sim_bw_subsumed:                        11
% 43.70/6.00  sim_fw_subsumption_res:                 0
% 43.70/6.00  sim_bw_subsumption_res:                 0
% 43.70/6.00  sim_tautology_del:                      26
% 43.70/6.00  sim_eq_tautology_del:                   401
% 43.70/6.00  sim_eq_res_simp:                        0
% 43.70/6.00  sim_fw_demodulated:                     875
% 43.70/6.00  sim_bw_demodulated:                     103
% 43.70/6.00  sim_light_normalised:                   3135
% 43.70/6.00  sim_joinable_taut:                      0
% 43.70/6.00  sim_joinable_simp:                      0
% 43.70/6.00  sim_ac_normalised:                      0
% 43.70/6.00  sim_smt_subsumption:                    0
% 43.70/6.00  
%------------------------------------------------------------------------------
