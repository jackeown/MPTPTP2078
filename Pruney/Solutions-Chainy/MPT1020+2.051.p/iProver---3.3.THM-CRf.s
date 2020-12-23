%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:15 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  200 (2538 expanded)
%              Number of clauses        :  113 ( 742 expanded)
%              Number of leaves         :   22 ( 625 expanded)
%              Depth                    :   32
%              Number of atoms          :  700 (17559 expanded)
%              Number of equality atoms :  275 (1390 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f54,f53])).

fof(f90,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f7,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f97,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f65,f77,f77])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f99,plain,(
    ! [X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f94])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1752,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1748,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1764,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2757,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1764])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_101,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_103,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_1964,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2309,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1964])).

cnf(c_2310,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2309])).

cnf(c_3068,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2757,c_38,c_103,c_2310])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_19,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_479,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_480,plain,
    ( v2_funct_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_482,plain,
    ( v2_funct_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_34,c_31])).

cnf(c_565,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_482])).

cnf(c_566,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1
    | sK2 != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_566])).

cnf(c_613,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_615,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_617,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_31,c_615])).

cnf(c_1741,plain,
    ( k2_relat_1(sK2) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_3073,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_3068,c_1741])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1757,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2606,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1748,c_1757])).

cnf(c_3124,plain,
    ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_3073,c_2606])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_187,plain,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_22])).

cnf(c_188,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_187])).

cnf(c_1745,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_3473,plain,
    ( k2_funct_1(sK2) = X0
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3124,c_1745])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4680,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0
    | k2_funct_1(sK2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3473,c_35,c_36,c_38])).

cnf(c_4681,plain,
    ( k2_funct_1(sK2) = X0
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4680])).

cnf(c_4692,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1752,c_4681])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4693,plain,
    ( ~ v1_funct_2(sK3,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4692])).

cnf(c_4695,plain,
    ( sK1 = k1_xboole_0
    | k2_funct_1(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4692,c_39,c_40,c_42])).

cnf(c_4696,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4695])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1753,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_498,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_499,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_501,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_34,c_33,c_31])).

cnf(c_1797,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1753,c_501])).

cnf(c_4699,plain,
    ( sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4696,c_1797])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1999,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2000,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1999])).

cnf(c_4726,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4699,c_42,c_2000])).

cnf(c_4749,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4726,c_1797])).

cnf(c_4,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_9,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2077,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_9])).

cnf(c_2078,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2077,c_4])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1754,plain,
    ( k1_relset_1(X0,X0,X1) = X0
    | v1_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3314,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1754])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1758,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2747,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1748,c_1758])).

cnf(c_3318,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3314,c_2747])).

cnf(c_3478,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3318,c_35,c_36])).

cnf(c_6,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1761,plain,
    ( k6_partfun1(k1_relat_1(X0)) = X0
    | r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3483,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3478,c_1761])).

cnf(c_3489,plain,
    ( k6_partfun1(sK1) = sK2
    | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3483,c_3478])).

cnf(c_4411,plain,
    ( k6_partfun1(sK1) = sK2
    | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3489,c_35,c_38,c_103,c_2310])).

cnf(c_4732,plain,
    ( k6_partfun1(k1_xboole_0) = sK2
    | r2_hidden(sK0(k1_xboole_0,sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4726,c_4411])).

cnf(c_4826,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK2),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4732,c_4])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_366,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_367,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_1744,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_4978,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4826,c_1744])).

cnf(c_1751,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3313,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_1754])).

cnf(c_2746,plain,
    ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1751,c_1758])).

cnf(c_3325,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3313,c_2746])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( v1_funct_2(sK3,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3748,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3325,c_39,c_40])).

cnf(c_3753,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = sK3
    | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3748,c_1761])).

cnf(c_3759,plain,
    ( k6_partfun1(sK1) = sK3
    | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3753,c_3748])).

cnf(c_2306,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1964])).

cnf(c_2307,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2306])).

cnf(c_4634,plain,
    ( k6_partfun1(sK1) = sK3
    | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3759,c_39,c_42,c_103,c_2307])).

cnf(c_4731,plain,
    ( k6_partfun1(k1_xboole_0) = sK3
    | r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4726,c_4634])).

cnf(c_4831,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4731,c_4])).

cnf(c_5055,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4831,c_1744])).

cnf(c_6697,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4749,c_2078,c_4978,c_5055])).

cnf(c_4751,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4726,c_1751])).

cnf(c_5496,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4751,c_5055])).

cnf(c_1756,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5502,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5496,c_1756])).

cnf(c_6699,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6697,c_5502])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:47:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.33/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/1.00  
% 3.33/1.00  ------  iProver source info
% 3.33/1.00  
% 3.33/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.33/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/1.00  git: non_committed_changes: false
% 3.33/1.00  git: last_make_outside_of_git: false
% 3.33/1.00  
% 3.33/1.00  ------ 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options
% 3.33/1.00  
% 3.33/1.00  --out_options                           all
% 3.33/1.00  --tptp_safe_out                         true
% 3.33/1.00  --problem_path                          ""
% 3.33/1.00  --include_path                          ""
% 3.33/1.00  --clausifier                            res/vclausify_rel
% 3.33/1.00  --clausifier_options                    --mode clausify
% 3.33/1.00  --stdin                                 false
% 3.33/1.00  --stats_out                             all
% 3.33/1.00  
% 3.33/1.00  ------ General Options
% 3.33/1.00  
% 3.33/1.00  --fof                                   false
% 3.33/1.00  --time_out_real                         305.
% 3.33/1.00  --time_out_virtual                      -1.
% 3.33/1.00  --symbol_type_check                     false
% 3.33/1.00  --clausify_out                          false
% 3.33/1.00  --sig_cnt_out                           false
% 3.33/1.00  --trig_cnt_out                          false
% 3.33/1.00  --trig_cnt_out_tolerance                1.
% 3.33/1.00  --trig_cnt_out_sk_spl                   false
% 3.33/1.00  --abstr_cl_out                          false
% 3.33/1.00  
% 3.33/1.00  ------ Global Options
% 3.33/1.00  
% 3.33/1.00  --schedule                              default
% 3.33/1.00  --add_important_lit                     false
% 3.33/1.00  --prop_solver_per_cl                    1000
% 3.33/1.00  --min_unsat_core                        false
% 3.33/1.00  --soft_assumptions                      false
% 3.33/1.00  --soft_lemma_size                       3
% 3.33/1.00  --prop_impl_unit_size                   0
% 3.33/1.00  --prop_impl_unit                        []
% 3.33/1.00  --share_sel_clauses                     true
% 3.33/1.00  --reset_solvers                         false
% 3.33/1.00  --bc_imp_inh                            [conj_cone]
% 3.33/1.00  --conj_cone_tolerance                   3.
% 3.33/1.00  --extra_neg_conj                        none
% 3.33/1.00  --large_theory_mode                     true
% 3.33/1.00  --prolific_symb_bound                   200
% 3.33/1.00  --lt_threshold                          2000
% 3.33/1.00  --clause_weak_htbl                      true
% 3.33/1.00  --gc_record_bc_elim                     false
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing Options
% 3.33/1.00  
% 3.33/1.00  --preprocessing_flag                    true
% 3.33/1.00  --time_out_prep_mult                    0.1
% 3.33/1.00  --splitting_mode                        input
% 3.33/1.00  --splitting_grd                         true
% 3.33/1.00  --splitting_cvd                         false
% 3.33/1.00  --splitting_cvd_svl                     false
% 3.33/1.00  --splitting_nvd                         32
% 3.33/1.00  --sub_typing                            true
% 3.33/1.00  --prep_gs_sim                           true
% 3.33/1.00  --prep_unflatten                        true
% 3.33/1.00  --prep_res_sim                          true
% 3.33/1.00  --prep_upred                            true
% 3.33/1.00  --prep_sem_filter                       exhaustive
% 3.33/1.00  --prep_sem_filter_out                   false
% 3.33/1.00  --pred_elim                             true
% 3.33/1.00  --res_sim_input                         true
% 3.33/1.00  --eq_ax_congr_red                       true
% 3.33/1.00  --pure_diseq_elim                       true
% 3.33/1.00  --brand_transform                       false
% 3.33/1.00  --non_eq_to_eq                          false
% 3.33/1.00  --prep_def_merge                        true
% 3.33/1.00  --prep_def_merge_prop_impl              false
% 3.33/1.00  --prep_def_merge_mbd                    true
% 3.33/1.00  --prep_def_merge_tr_red                 false
% 3.33/1.00  --prep_def_merge_tr_cl                  false
% 3.33/1.00  --smt_preprocessing                     true
% 3.33/1.00  --smt_ac_axioms                         fast
% 3.33/1.00  --preprocessed_out                      false
% 3.33/1.00  --preprocessed_stats                    false
% 3.33/1.00  
% 3.33/1.00  ------ Abstraction refinement Options
% 3.33/1.00  
% 3.33/1.00  --abstr_ref                             []
% 3.33/1.00  --abstr_ref_prep                        false
% 3.33/1.00  --abstr_ref_until_sat                   false
% 3.33/1.00  --abstr_ref_sig_restrict                funpre
% 3.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.00  --abstr_ref_under                       []
% 3.33/1.00  
% 3.33/1.00  ------ SAT Options
% 3.33/1.00  
% 3.33/1.00  --sat_mode                              false
% 3.33/1.00  --sat_fm_restart_options                ""
% 3.33/1.00  --sat_gr_def                            false
% 3.33/1.00  --sat_epr_types                         true
% 3.33/1.00  --sat_non_cyclic_types                  false
% 3.33/1.00  --sat_finite_models                     false
% 3.33/1.00  --sat_fm_lemmas                         false
% 3.33/1.00  --sat_fm_prep                           false
% 3.33/1.00  --sat_fm_uc_incr                        true
% 3.33/1.00  --sat_out_model                         small
% 3.33/1.00  --sat_out_clauses                       false
% 3.33/1.00  
% 3.33/1.00  ------ QBF Options
% 3.33/1.00  
% 3.33/1.00  --qbf_mode                              false
% 3.33/1.00  --qbf_elim_univ                         false
% 3.33/1.00  --qbf_dom_inst                          none
% 3.33/1.00  --qbf_dom_pre_inst                      false
% 3.33/1.00  --qbf_sk_in                             false
% 3.33/1.00  --qbf_pred_elim                         true
% 3.33/1.00  --qbf_split                             512
% 3.33/1.00  
% 3.33/1.00  ------ BMC1 Options
% 3.33/1.00  
% 3.33/1.00  --bmc1_incremental                      false
% 3.33/1.00  --bmc1_axioms                           reachable_all
% 3.33/1.00  --bmc1_min_bound                        0
% 3.33/1.00  --bmc1_max_bound                        -1
% 3.33/1.00  --bmc1_max_bound_default                -1
% 3.33/1.00  --bmc1_symbol_reachability              true
% 3.33/1.00  --bmc1_property_lemmas                  false
% 3.33/1.00  --bmc1_k_induction                      false
% 3.33/1.00  --bmc1_non_equiv_states                 false
% 3.33/1.00  --bmc1_deadlock                         false
% 3.33/1.00  --bmc1_ucm                              false
% 3.33/1.00  --bmc1_add_unsat_core                   none
% 3.33/1.00  --bmc1_unsat_core_children              false
% 3.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.00  --bmc1_out_stat                         full
% 3.33/1.00  --bmc1_ground_init                      false
% 3.33/1.00  --bmc1_pre_inst_next_state              false
% 3.33/1.00  --bmc1_pre_inst_state                   false
% 3.33/1.00  --bmc1_pre_inst_reach_state             false
% 3.33/1.00  --bmc1_out_unsat_core                   false
% 3.33/1.00  --bmc1_aig_witness_out                  false
% 3.33/1.00  --bmc1_verbose                          false
% 3.33/1.00  --bmc1_dump_clauses_tptp                false
% 3.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.00  --bmc1_dump_file                        -
% 3.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.00  --bmc1_ucm_extend_mode                  1
% 3.33/1.00  --bmc1_ucm_init_mode                    2
% 3.33/1.00  --bmc1_ucm_cone_mode                    none
% 3.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.00  --bmc1_ucm_relax_model                  4
% 3.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.00  --bmc1_ucm_layered_model                none
% 3.33/1.00  --bmc1_ucm_max_lemma_size               10
% 3.33/1.00  
% 3.33/1.00  ------ AIG Options
% 3.33/1.00  
% 3.33/1.00  --aig_mode                              false
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation Options
% 3.33/1.00  
% 3.33/1.00  --instantiation_flag                    true
% 3.33/1.00  --inst_sos_flag                         false
% 3.33/1.00  --inst_sos_phase                        true
% 3.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel_side                     num_symb
% 3.33/1.00  --inst_solver_per_active                1400
% 3.33/1.00  --inst_solver_calls_frac                1.
% 3.33/1.00  --inst_passive_queue_type               priority_queues
% 3.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.00  --inst_passive_queues_freq              [25;2]
% 3.33/1.00  --inst_dismatching                      true
% 3.33/1.00  --inst_eager_unprocessed_to_passive     true
% 3.33/1.00  --inst_prop_sim_given                   true
% 3.33/1.00  --inst_prop_sim_new                     false
% 3.33/1.00  --inst_subs_new                         false
% 3.33/1.00  --inst_eq_res_simp                      false
% 3.33/1.00  --inst_subs_given                       false
% 3.33/1.00  --inst_orphan_elimination               true
% 3.33/1.00  --inst_learning_loop_flag               true
% 3.33/1.00  --inst_learning_start                   3000
% 3.33/1.00  --inst_learning_factor                  2
% 3.33/1.00  --inst_start_prop_sim_after_learn       3
% 3.33/1.00  --inst_sel_renew                        solver
% 3.33/1.00  --inst_lit_activity_flag                true
% 3.33/1.00  --inst_restr_to_given                   false
% 3.33/1.00  --inst_activity_threshold               500
% 3.33/1.00  --inst_out_proof                        true
% 3.33/1.00  
% 3.33/1.00  ------ Resolution Options
% 3.33/1.00  
% 3.33/1.00  --resolution_flag                       true
% 3.33/1.00  --res_lit_sel                           adaptive
% 3.33/1.00  --res_lit_sel_side                      none
% 3.33/1.00  --res_ordering                          kbo
% 3.33/1.00  --res_to_prop_solver                    active
% 3.33/1.00  --res_prop_simpl_new                    false
% 3.33/1.00  --res_prop_simpl_given                  true
% 3.33/1.00  --res_passive_queue_type                priority_queues
% 3.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.00  --res_passive_queues_freq               [15;5]
% 3.33/1.00  --res_forward_subs                      full
% 3.33/1.00  --res_backward_subs                     full
% 3.33/1.00  --res_forward_subs_resolution           true
% 3.33/1.00  --res_backward_subs_resolution          true
% 3.33/1.00  --res_orphan_elimination                true
% 3.33/1.00  --res_time_limit                        2.
% 3.33/1.00  --res_out_proof                         true
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Options
% 3.33/1.00  
% 3.33/1.00  --superposition_flag                    true
% 3.33/1.00  --sup_passive_queue_type                priority_queues
% 3.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.00  --demod_completeness_check              fast
% 3.33/1.00  --demod_use_ground                      true
% 3.33/1.00  --sup_to_prop_solver                    passive
% 3.33/1.00  --sup_prop_simpl_new                    true
% 3.33/1.00  --sup_prop_simpl_given                  true
% 3.33/1.00  --sup_fun_splitting                     false
% 3.33/1.00  --sup_smt_interval                      50000
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Simplification Setup
% 3.33/1.00  
% 3.33/1.00  --sup_indices_passive                   []
% 3.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_full_bw                           [BwDemod]
% 3.33/1.00  --sup_immed_triv                        [TrivRules]
% 3.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_immed_bw_main                     []
% 3.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  
% 3.33/1.00  ------ Combination Options
% 3.33/1.00  
% 3.33/1.00  --comb_res_mult                         3
% 3.33/1.00  --comb_sup_mult                         2
% 3.33/1.00  --comb_inst_mult                        10
% 3.33/1.00  
% 3.33/1.00  ------ Debug Options
% 3.33/1.00  
% 3.33/1.00  --dbg_backtrace                         false
% 3.33/1.00  --dbg_dump_prop_clauses                 false
% 3.33/1.00  --dbg_dump_prop_clauses_file            -
% 3.33/1.00  --dbg_out_stat                          false
% 3.33/1.00  ------ Parsing...
% 3.33/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/1.00  ------ Proving...
% 3.33/1.00  ------ Problem Properties 
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  clauses                                 28
% 3.33/1.00  conjectures                             8
% 3.33/1.00  EPR                                     5
% 3.33/1.00  Horn                                    26
% 3.33/1.00  unary                                   14
% 3.33/1.00  binary                                  5
% 3.33/1.00  lits                                    70
% 3.33/1.00  lits eq                                 20
% 3.33/1.00  fd_pure                                 0
% 3.33/1.00  fd_pseudo                               0
% 3.33/1.00  fd_cond                                 0
% 3.33/1.00  fd_pseudo_cond                          3
% 3.33/1.00  AC symbols                              0
% 3.33/1.00  
% 3.33/1.00  ------ Schedule dynamic 5 is on 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ 
% 3.33/1.00  Current options:
% 3.33/1.00  ------ 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options
% 3.33/1.00  
% 3.33/1.00  --out_options                           all
% 3.33/1.00  --tptp_safe_out                         true
% 3.33/1.00  --problem_path                          ""
% 3.33/1.00  --include_path                          ""
% 3.33/1.00  --clausifier                            res/vclausify_rel
% 3.33/1.00  --clausifier_options                    --mode clausify
% 3.33/1.00  --stdin                                 false
% 3.33/1.00  --stats_out                             all
% 3.33/1.00  
% 3.33/1.00  ------ General Options
% 3.33/1.00  
% 3.33/1.00  --fof                                   false
% 3.33/1.00  --time_out_real                         305.
% 3.33/1.00  --time_out_virtual                      -1.
% 3.33/1.00  --symbol_type_check                     false
% 3.33/1.00  --clausify_out                          false
% 3.33/1.00  --sig_cnt_out                           false
% 3.33/1.00  --trig_cnt_out                          false
% 3.33/1.00  --trig_cnt_out_tolerance                1.
% 3.33/1.00  --trig_cnt_out_sk_spl                   false
% 3.33/1.00  --abstr_cl_out                          false
% 3.33/1.00  
% 3.33/1.00  ------ Global Options
% 3.33/1.00  
% 3.33/1.00  --schedule                              default
% 3.33/1.00  --add_important_lit                     false
% 3.33/1.00  --prop_solver_per_cl                    1000
% 3.33/1.00  --min_unsat_core                        false
% 3.33/1.00  --soft_assumptions                      false
% 3.33/1.00  --soft_lemma_size                       3
% 3.33/1.00  --prop_impl_unit_size                   0
% 3.33/1.00  --prop_impl_unit                        []
% 3.33/1.00  --share_sel_clauses                     true
% 3.33/1.00  --reset_solvers                         false
% 3.33/1.00  --bc_imp_inh                            [conj_cone]
% 3.33/1.00  --conj_cone_tolerance                   3.
% 3.33/1.00  --extra_neg_conj                        none
% 3.33/1.00  --large_theory_mode                     true
% 3.33/1.00  --prolific_symb_bound                   200
% 3.33/1.00  --lt_threshold                          2000
% 3.33/1.00  --clause_weak_htbl                      true
% 3.33/1.00  --gc_record_bc_elim                     false
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing Options
% 3.33/1.00  
% 3.33/1.00  --preprocessing_flag                    true
% 3.33/1.00  --time_out_prep_mult                    0.1
% 3.33/1.00  --splitting_mode                        input
% 3.33/1.00  --splitting_grd                         true
% 3.33/1.00  --splitting_cvd                         false
% 3.33/1.00  --splitting_cvd_svl                     false
% 3.33/1.00  --splitting_nvd                         32
% 3.33/1.00  --sub_typing                            true
% 3.33/1.00  --prep_gs_sim                           true
% 3.33/1.00  --prep_unflatten                        true
% 3.33/1.00  --prep_res_sim                          true
% 3.33/1.00  --prep_upred                            true
% 3.33/1.00  --prep_sem_filter                       exhaustive
% 3.33/1.00  --prep_sem_filter_out                   false
% 3.33/1.00  --pred_elim                             true
% 3.33/1.00  --res_sim_input                         true
% 3.33/1.00  --eq_ax_congr_red                       true
% 3.33/1.00  --pure_diseq_elim                       true
% 3.33/1.00  --brand_transform                       false
% 3.33/1.00  --non_eq_to_eq                          false
% 3.33/1.00  --prep_def_merge                        true
% 3.33/1.00  --prep_def_merge_prop_impl              false
% 3.33/1.00  --prep_def_merge_mbd                    true
% 3.33/1.00  --prep_def_merge_tr_red                 false
% 3.33/1.00  --prep_def_merge_tr_cl                  false
% 3.33/1.00  --smt_preprocessing                     true
% 3.33/1.00  --smt_ac_axioms                         fast
% 3.33/1.00  --preprocessed_out                      false
% 3.33/1.00  --preprocessed_stats                    false
% 3.33/1.00  
% 3.33/1.00  ------ Abstraction refinement Options
% 3.33/1.00  
% 3.33/1.00  --abstr_ref                             []
% 3.33/1.00  --abstr_ref_prep                        false
% 3.33/1.00  --abstr_ref_until_sat                   false
% 3.33/1.00  --abstr_ref_sig_restrict                funpre
% 3.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.00  --abstr_ref_under                       []
% 3.33/1.00  
% 3.33/1.00  ------ SAT Options
% 3.33/1.00  
% 3.33/1.00  --sat_mode                              false
% 3.33/1.00  --sat_fm_restart_options                ""
% 3.33/1.00  --sat_gr_def                            false
% 3.33/1.00  --sat_epr_types                         true
% 3.33/1.00  --sat_non_cyclic_types                  false
% 3.33/1.00  --sat_finite_models                     false
% 3.33/1.00  --sat_fm_lemmas                         false
% 3.33/1.00  --sat_fm_prep                           false
% 3.33/1.00  --sat_fm_uc_incr                        true
% 3.33/1.00  --sat_out_model                         small
% 3.33/1.00  --sat_out_clauses                       false
% 3.33/1.00  
% 3.33/1.00  ------ QBF Options
% 3.33/1.00  
% 3.33/1.00  --qbf_mode                              false
% 3.33/1.00  --qbf_elim_univ                         false
% 3.33/1.00  --qbf_dom_inst                          none
% 3.33/1.00  --qbf_dom_pre_inst                      false
% 3.33/1.00  --qbf_sk_in                             false
% 3.33/1.00  --qbf_pred_elim                         true
% 3.33/1.00  --qbf_split                             512
% 3.33/1.00  
% 3.33/1.00  ------ BMC1 Options
% 3.33/1.00  
% 3.33/1.00  --bmc1_incremental                      false
% 3.33/1.00  --bmc1_axioms                           reachable_all
% 3.33/1.00  --bmc1_min_bound                        0
% 3.33/1.00  --bmc1_max_bound                        -1
% 3.33/1.00  --bmc1_max_bound_default                -1
% 3.33/1.00  --bmc1_symbol_reachability              true
% 3.33/1.00  --bmc1_property_lemmas                  false
% 3.33/1.00  --bmc1_k_induction                      false
% 3.33/1.00  --bmc1_non_equiv_states                 false
% 3.33/1.00  --bmc1_deadlock                         false
% 3.33/1.00  --bmc1_ucm                              false
% 3.33/1.00  --bmc1_add_unsat_core                   none
% 3.33/1.00  --bmc1_unsat_core_children              false
% 3.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.00  --bmc1_out_stat                         full
% 3.33/1.00  --bmc1_ground_init                      false
% 3.33/1.00  --bmc1_pre_inst_next_state              false
% 3.33/1.00  --bmc1_pre_inst_state                   false
% 3.33/1.00  --bmc1_pre_inst_reach_state             false
% 3.33/1.00  --bmc1_out_unsat_core                   false
% 3.33/1.00  --bmc1_aig_witness_out                  false
% 3.33/1.00  --bmc1_verbose                          false
% 3.33/1.00  --bmc1_dump_clauses_tptp                false
% 3.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.00  --bmc1_dump_file                        -
% 3.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.00  --bmc1_ucm_extend_mode                  1
% 3.33/1.00  --bmc1_ucm_init_mode                    2
% 3.33/1.00  --bmc1_ucm_cone_mode                    none
% 3.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.00  --bmc1_ucm_relax_model                  4
% 3.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.00  --bmc1_ucm_layered_model                none
% 3.33/1.00  --bmc1_ucm_max_lemma_size               10
% 3.33/1.00  
% 3.33/1.00  ------ AIG Options
% 3.33/1.00  
% 3.33/1.00  --aig_mode                              false
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation Options
% 3.33/1.00  
% 3.33/1.00  --instantiation_flag                    true
% 3.33/1.00  --inst_sos_flag                         false
% 3.33/1.00  --inst_sos_phase                        true
% 3.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel_side                     none
% 3.33/1.00  --inst_solver_per_active                1400
% 3.33/1.00  --inst_solver_calls_frac                1.
% 3.33/1.00  --inst_passive_queue_type               priority_queues
% 3.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.00  --inst_passive_queues_freq              [25;2]
% 3.33/1.00  --inst_dismatching                      true
% 3.33/1.00  --inst_eager_unprocessed_to_passive     true
% 3.33/1.00  --inst_prop_sim_given                   true
% 3.33/1.00  --inst_prop_sim_new                     false
% 3.33/1.00  --inst_subs_new                         false
% 3.33/1.00  --inst_eq_res_simp                      false
% 3.33/1.00  --inst_subs_given                       false
% 3.33/1.00  --inst_orphan_elimination               true
% 3.33/1.00  --inst_learning_loop_flag               true
% 3.33/1.00  --inst_learning_start                   3000
% 3.33/1.00  --inst_learning_factor                  2
% 3.33/1.00  --inst_start_prop_sim_after_learn       3
% 3.33/1.00  --inst_sel_renew                        solver
% 3.33/1.00  --inst_lit_activity_flag                true
% 3.33/1.00  --inst_restr_to_given                   false
% 3.33/1.00  --inst_activity_threshold               500
% 3.33/1.00  --inst_out_proof                        true
% 3.33/1.00  
% 3.33/1.00  ------ Resolution Options
% 3.33/1.00  
% 3.33/1.00  --resolution_flag                       false
% 3.33/1.00  --res_lit_sel                           adaptive
% 3.33/1.00  --res_lit_sel_side                      none
% 3.33/1.00  --res_ordering                          kbo
% 3.33/1.00  --res_to_prop_solver                    active
% 3.33/1.00  --res_prop_simpl_new                    false
% 3.33/1.00  --res_prop_simpl_given                  true
% 3.33/1.00  --res_passive_queue_type                priority_queues
% 3.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.00  --res_passive_queues_freq               [15;5]
% 3.33/1.00  --res_forward_subs                      full
% 3.33/1.00  --res_backward_subs                     full
% 3.33/1.00  --res_forward_subs_resolution           true
% 3.33/1.00  --res_backward_subs_resolution          true
% 3.33/1.00  --res_orphan_elimination                true
% 3.33/1.00  --res_time_limit                        2.
% 3.33/1.00  --res_out_proof                         true
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Options
% 3.33/1.00  
% 3.33/1.00  --superposition_flag                    true
% 3.33/1.00  --sup_passive_queue_type                priority_queues
% 3.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.00  --demod_completeness_check              fast
% 3.33/1.00  --demod_use_ground                      true
% 3.33/1.00  --sup_to_prop_solver                    passive
% 3.33/1.00  --sup_prop_simpl_new                    true
% 3.33/1.00  --sup_prop_simpl_given                  true
% 3.33/1.00  --sup_fun_splitting                     false
% 3.33/1.00  --sup_smt_interval                      50000
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Simplification Setup
% 3.33/1.00  
% 3.33/1.00  --sup_indices_passive                   []
% 3.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_full_bw                           [BwDemod]
% 3.33/1.00  --sup_immed_triv                        [TrivRules]
% 3.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_immed_bw_main                     []
% 3.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  
% 3.33/1.00  ------ Combination Options
% 3.33/1.00  
% 3.33/1.00  --comb_res_mult                         3
% 3.33/1.00  --comb_sup_mult                         2
% 3.33/1.00  --comb_inst_mult                        10
% 3.33/1.00  
% 3.33/1.00  ------ Debug Options
% 3.33/1.00  
% 3.33/1.00  --dbg_backtrace                         false
% 3.33/1.00  --dbg_dump_prop_clauses                 false
% 3.33/1.00  --dbg_dump_prop_clauses_file            -
% 3.33/1.00  --dbg_out_stat                          false
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ Proving...
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS status Theorem for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00   Resolution empty clause
% 3.33/1.00  
% 3.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  fof(f19,conjecture,(
% 3.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f20,negated_conjecture,(
% 3.33/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.33/1.00    inference(negated_conjecture,[],[f19])).
% 3.33/1.00  
% 3.33/1.00  fof(f44,plain,(
% 3.33/1.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.33/1.00    inference(ennf_transformation,[],[f20])).
% 3.33/1.00  
% 3.33/1.00  fof(f45,plain,(
% 3.33/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.33/1.00    inference(flattening,[],[f44])).
% 3.33/1.00  
% 3.33/1.00  fof(f54,plain,(
% 3.33/1.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK3,X0,X0) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f53,plain,(
% 3.33/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(X2,sK1,sK1) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f55,plain,(
% 3.33/1.00    (~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f54,f53])).
% 3.33/1.00  
% 3.33/1.00  fof(f90,plain,(
% 3.33/1.00    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))),
% 3.33/1.00    inference(cnf_transformation,[],[f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f85,plain,(
% 3.33/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.33/1.00    inference(cnf_transformation,[],[f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f3,axiom,(
% 3.33/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f24,plain,(
% 3.33/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f3])).
% 3.33/1.00  
% 3.33/1.00  fof(f58,plain,(
% 3.33/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f24])).
% 3.33/1.00  
% 3.33/1.00  fof(f4,axiom,(
% 3.33/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f59,plain,(
% 3.33/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f4])).
% 3.33/1.00  
% 3.33/1.00  fof(f8,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f22,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.33/1.00    inference(pure_predicate_removal,[],[f8])).
% 3.33/1.00  
% 3.33/1.00  fof(f27,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f22])).
% 3.33/1.00  
% 3.33/1.00  fof(f66,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f27])).
% 3.33/1.00  
% 3.33/1.00  fof(f13,axiom,(
% 3.33/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f34,plain,(
% 3.33/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.33/1.00    inference(ennf_transformation,[],[f13])).
% 3.33/1.00  
% 3.33/1.00  fof(f35,plain,(
% 3.33/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(flattening,[],[f34])).
% 3.33/1.00  
% 3.33/1.00  fof(f52,plain,(
% 3.33/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(nnf_transformation,[],[f35])).
% 3.33/1.00  
% 3.33/1.00  fof(f74,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f52])).
% 3.33/1.00  
% 3.33/1.00  fof(f12,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f32,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f12])).
% 3.33/1.00  
% 3.33/1.00  fof(f33,plain,(
% 3.33/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(flattening,[],[f32])).
% 3.33/1.00  
% 3.33/1.00  fof(f73,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f33])).
% 3.33/1.00  
% 3.33/1.00  fof(f84,plain,(
% 3.33/1.00    v3_funct_2(sK2,sK1,sK1)),
% 3.33/1.00    inference(cnf_transformation,[],[f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f82,plain,(
% 3.33/1.00    v1_funct_1(sK2)),
% 3.33/1.00    inference(cnf_transformation,[],[f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f10,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f29,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f10])).
% 3.33/1.00  
% 3.33/1.00  fof(f68,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f29])).
% 3.33/1.00  
% 3.33/1.00  fof(f17,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f40,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.33/1.00    inference(ennf_transformation,[],[f17])).
% 3.33/1.00  
% 3.33/1.00  fof(f41,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.33/1.00    inference(flattening,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f80,plain,(
% 3.33/1.00    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f41])).
% 3.33/1.00  
% 3.33/1.00  fof(f16,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f38,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.33/1.00    inference(ennf_transformation,[],[f16])).
% 3.33/1.00  
% 3.33/1.00  fof(f39,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.33/1.00    inference(flattening,[],[f38])).
% 3.33/1.00  
% 3.33/1.00  fof(f78,plain,(
% 3.33/1.00    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f39])).
% 3.33/1.00  
% 3.33/1.00  fof(f83,plain,(
% 3.33/1.00    v1_funct_2(sK2,sK1,sK1)),
% 3.33/1.00    inference(cnf_transformation,[],[f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f86,plain,(
% 3.33/1.00    v1_funct_1(sK3)),
% 3.33/1.00    inference(cnf_transformation,[],[f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f87,plain,(
% 3.33/1.00    v1_funct_2(sK3,sK1,sK1)),
% 3.33/1.00    inference(cnf_transformation,[],[f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f89,plain,(
% 3.33/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.33/1.00    inference(cnf_transformation,[],[f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f91,plain,(
% 3.33/1.00    ~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))),
% 3.33/1.00    inference(cnf_transformation,[],[f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f14,axiom,(
% 3.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f36,plain,(
% 3.33/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.33/1.00    inference(ennf_transformation,[],[f14])).
% 3.33/1.00  
% 3.33/1.00  fof(f37,plain,(
% 3.33/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.33/1.00    inference(flattening,[],[f36])).
% 3.33/1.00  
% 3.33/1.00  fof(f76,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f11,axiom,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f30,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.33/1.00    inference(ennf_transformation,[],[f11])).
% 3.33/1.00  
% 3.33/1.00  fof(f31,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(flattening,[],[f30])).
% 3.33/1.00  
% 3.33/1.00  fof(f51,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(nnf_transformation,[],[f31])).
% 3.33/1.00  
% 3.33/1.00  fof(f70,plain,(
% 3.33/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f51])).
% 3.33/1.00  
% 3.33/1.00  fof(f102,plain,(
% 3.33/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(equality_resolution,[],[f70])).
% 3.33/1.00  
% 3.33/1.00  fof(f5,axiom,(
% 3.33/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f60,plain,(
% 3.33/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.33/1.00    inference(cnf_transformation,[],[f5])).
% 3.33/1.00  
% 3.33/1.00  fof(f15,axiom,(
% 3.33/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f77,plain,(
% 3.33/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f15])).
% 3.33/1.00  
% 3.33/1.00  fof(f92,plain,(
% 3.33/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.33/1.00    inference(definition_unfolding,[],[f60,f77])).
% 3.33/1.00  
% 3.33/1.00  fof(f7,axiom,(
% 3.33/1.00    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f65,plain,(
% 3.33/1.00    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f7])).
% 3.33/1.00  
% 3.33/1.00  fof(f97,plain,(
% 3.33/1.00    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.33/1.00    inference(definition_unfolding,[],[f65,f77,f77])).
% 3.33/1.00  
% 3.33/1.00  fof(f18,axiom,(
% 3.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f42,plain,(
% 3.33/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.33/1.00    inference(ennf_transformation,[],[f18])).
% 3.33/1.00  
% 3.33/1.00  fof(f43,plain,(
% 3.33/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.33/1.00    inference(flattening,[],[f42])).
% 3.33/1.00  
% 3.33/1.00  fof(f81,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f43])).
% 3.33/1.00  
% 3.33/1.00  fof(f9,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f28,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f9])).
% 3.33/1.00  
% 3.33/1.00  fof(f67,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f28])).
% 3.33/1.00  
% 3.33/1.00  fof(f6,axiom,(
% 3.33/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f25,plain,(
% 3.33/1.00    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.33/1.00    inference(ennf_transformation,[],[f6])).
% 3.33/1.00  
% 3.33/1.00  fof(f26,plain,(
% 3.33/1.00    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(flattening,[],[f25])).
% 3.33/1.00  
% 3.33/1.00  fof(f46,plain,(
% 3.33/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(nnf_transformation,[],[f26])).
% 3.33/1.00  
% 3.33/1.00  fof(f47,plain,(
% 3.33/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(flattening,[],[f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f48,plain,(
% 3.33/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(rectify,[],[f47])).
% 3.33/1.00  
% 3.33/1.00  fof(f49,plain,(
% 3.33/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f50,plain,(
% 3.33/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 3.33/1.00  
% 3.33/1.00  fof(f63,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f50])).
% 3.33/1.00  
% 3.33/1.00  fof(f94,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.33/1.00    inference(definition_unfolding,[],[f63,f77])).
% 3.33/1.00  
% 3.33/1.00  fof(f99,plain,(
% 3.33/1.00    ( ! [X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.33/1.00    inference(equality_resolution,[],[f94])).
% 3.33/1.00  
% 3.33/1.00  fof(f1,axiom,(
% 3.33/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f21,plain,(
% 3.33/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.33/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.33/1.00  
% 3.33/1.00  fof(f23,plain,(
% 3.33/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f21])).
% 3.33/1.00  
% 3.33/1.00  fof(f56,plain,(
% 3.33/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f23])).
% 3.33/1.00  
% 3.33/1.00  fof(f2,axiom,(
% 3.33/1.00    v1_xboole_0(k1_xboole_0)),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f57,plain,(
% 3.33/1.00    v1_xboole_0(k1_xboole_0)),
% 3.33/1.00    inference(cnf_transformation,[],[f2])).
% 3.33/1.00  
% 3.33/1.00  cnf(c_26,negated_conjecture,
% 3.33/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1752,plain,
% 3.33/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_31,negated_conjecture,
% 3.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1748,plain,
% 3.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1764,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.33/1.00      | v1_relat_1(X1) != iProver_top
% 3.33/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2757,plain,
% 3.33/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
% 3.33/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1748,c_1764]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_38,plain,
% 3.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3,plain,
% 3.33/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_101,plain,
% 3.33/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_103,plain,
% 3.33/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_101]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1964,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | v1_relat_1(X0)
% 3.33/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2309,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.33/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
% 3.33/1.00      | v1_relat_1(sK2) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1964]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2310,plain,
% 3.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.33/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
% 3.33/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2309]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3068,plain,
% 3.33/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_2757,c_38,c_103,c_2310]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10,plain,
% 3.33/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_19,plain,
% 3.33/1.00      ( ~ v2_funct_2(X0,X1)
% 3.33/1.00      | ~ v5_relat_1(X0,X1)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | k2_relat_1(X0) = X1 ),
% 3.33/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_15,plain,
% 3.33/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.33/1.00      | v2_funct_2(X0,X2)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ v1_funct_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_32,negated_conjecture,
% 3.33/1.00      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_479,plain,
% 3.33/1.00      ( v2_funct_2(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | sK2 != X0
% 3.33/1.00      | sK1 != X1
% 3.33/1.00      | sK1 != X2 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_480,plain,
% 3.33/1.00      ( v2_funct_2(sK2,sK1)
% 3.33/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.33/1.00      | ~ v1_funct_1(sK2) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_479]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_34,negated_conjecture,
% 3.33/1.00      ( v1_funct_1(sK2) ),
% 3.33/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_482,plain,
% 3.33/1.00      ( v2_funct_2(sK2,sK1) ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_480,c_34,c_31]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_565,plain,
% 3.33/1.00      ( ~ v5_relat_1(X0,X1)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | k2_relat_1(X0) = X1
% 3.33/1.00      | sK2 != X0
% 3.33/1.00      | sK1 != X1 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_482]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_566,plain,
% 3.33/1.00      ( ~ v5_relat_1(sK2,sK1) | ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK1 ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_565]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_612,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ v1_relat_1(sK2)
% 3.33/1.00      | k2_relat_1(sK2) = sK1
% 3.33/1.00      | sK2 != X0
% 3.33/1.00      | sK1 != X2 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_566]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_613,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.33/1.00      | ~ v1_relat_1(sK2)
% 3.33/1.00      | k2_relat_1(sK2) = sK1 ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_612]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_615,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.33/1.00      | ~ v1_relat_1(sK2)
% 3.33/1.00      | k2_relat_1(sK2) = sK1 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_613]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_617,plain,
% 3.33/1.00      ( ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK1 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_613,c_31,c_615]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1741,plain,
% 3.33/1.00      ( k2_relat_1(sK2) = sK1 | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3073,plain,
% 3.33/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3068,c_1741]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_12,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1757,plain,
% 3.33/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2606,plain,
% 3.33/1.00      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1748,c_1757]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3124,plain,
% 3.33/1.00      ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_3073,c_2606]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_23,plain,
% 3.33/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.33/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.33/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.33/1.00      | ~ v2_funct_1(X2)
% 3.33/1.00      | ~ v1_funct_1(X2)
% 3.33/1.00      | ~ v1_funct_1(X3)
% 3.33/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.33/1.00      | k2_funct_1(X2) = X3
% 3.33/1.00      | k1_xboole_0 = X1
% 3.33/1.00      | k1_xboole_0 = X0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_22,plain,
% 3.33/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.33/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.33/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.33/1.00      | v2_funct_1(X2)
% 3.33/1.00      | ~ v1_funct_1(X2)
% 3.33/1.00      | ~ v1_funct_1(X3) ),
% 3.33/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_187,plain,
% 3.33/1.00      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.33/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.33/1.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.33/1.00      | ~ v1_funct_1(X2)
% 3.33/1.00      | ~ v1_funct_1(X3)
% 3.33/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.33/1.00      | k2_funct_1(X2) = X3
% 3.33/1.00      | k1_xboole_0 = X1
% 3.33/1.00      | k1_xboole_0 = X0 ),
% 3.33/1.00      inference(global_propositional_subsumption,[status(thm)],[c_23,c_22]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_188,plain,
% 3.33/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.33/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.33/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.33/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.00      | ~ v1_funct_1(X3)
% 3.33/1.00      | ~ v1_funct_1(X2)
% 3.33/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.33/1.00      | k2_funct_1(X2) = X3
% 3.33/1.00      | k1_xboole_0 = X0
% 3.33/1.00      | k1_xboole_0 = X1 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_187]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1745,plain,
% 3.33/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.33/1.00      | k2_funct_1(X2) = X3
% 3.33/1.00      | k1_xboole_0 = X0
% 3.33/1.00      | k1_xboole_0 = X1
% 3.33/1.00      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.33/1.00      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.33/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.33/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.33/1.00      | v1_funct_1(X2) != iProver_top
% 3.33/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_188]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3473,plain,
% 3.33/1.00      ( k2_funct_1(sK2) = X0
% 3.33/1.00      | sK1 = k1_xboole_0
% 3.33/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.33/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.33/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.33/1.00      | v1_funct_1(X0) != iProver_top
% 3.33/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3124,c_1745]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_35,plain,
% 3.33/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_33,negated_conjecture,
% 3.33/1.00      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_36,plain,
% 3.33/1.00      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4680,plain,
% 3.33/1.00      ( v1_funct_1(X0) != iProver_top
% 3.33/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.33/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.33/1.00      | sK1 = k1_xboole_0
% 3.33/1.00      | k2_funct_1(sK2) = X0
% 3.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_3473,c_35,c_36,c_38]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4681,plain,
% 3.33/1.00      ( k2_funct_1(sK2) = X0
% 3.33/1.00      | sK1 = k1_xboole_0
% 3.33/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.33/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.33/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.33/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_4680]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4692,plain,
% 3.33/1.00      ( k2_funct_1(sK2) = sK3
% 3.33/1.00      | sK1 = k1_xboole_0
% 3.33/1.00      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.33/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.33/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1752,c_4681]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_30,negated_conjecture,
% 3.33/1.00      ( v1_funct_1(sK3) ),
% 3.33/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_29,negated_conjecture,
% 3.33/1.00      ( v1_funct_2(sK3,sK1,sK1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_27,negated_conjecture,
% 3.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4693,plain,
% 3.33/1.00      ( ~ v1_funct_2(sK3,sK1,sK1)
% 3.33/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.33/1.00      | ~ v1_funct_1(sK3)
% 3.33/1.00      | k2_funct_1(sK2) = sK3
% 3.33/1.00      | sK1 = k1_xboole_0 ),
% 3.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4692]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4695,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0 | k2_funct_1(sK2) = sK3 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_4692,c_39,c_40,c_42]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4696,plain,
% 3.33/1.00      ( k2_funct_1(sK2) = sK3 | sK1 = k1_xboole_0 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_4695]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_25,negated_conjecture,
% 3.33/1.00      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1753,plain,
% 3.33/1.00      ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_20,plain,
% 3.33/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.33/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_498,plain,
% 3.33/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.33/1.00      | sK2 != X0
% 3.33/1.00      | sK1 != X1 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_499,plain,
% 3.33/1.00      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.33/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.33/1.00      | ~ v1_funct_1(sK2)
% 3.33/1.00      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_498]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_501,plain,
% 3.33/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_499,c_34,c_33,c_31]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1797,plain,
% 3.33/1.00      ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_1753,c_501]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4699,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0 | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_4696,c_1797]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_42,plain,
% 3.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_13,plain,
% 3.33/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1999,plain,
% 3.33/1.00      ( r2_relset_1(sK1,sK1,sK3,sK3)
% 3.33/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2000,plain,
% 3.33/1.00      ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
% 3.33/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1999]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4726,plain,
% 3.33/1.00      ( sK1 = k1_xboole_0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_4699,c_42,c_2000]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4749,plain,
% 3.33/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_4726,c_1797]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4,plain,
% 3.33/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9,plain,
% 3.33/1.00      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2077,plain,
% 3.33/1.00      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_4,c_9]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2078,plain,
% 3.33/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_2077,c_4]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_24,plain,
% 3.33/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.33/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1754,plain,
% 3.33/1.00      ( k1_relset_1(X0,X0,X1) = X0
% 3.33/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.33/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.33/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3314,plain,
% 3.33/1.00      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.33/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.33/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1748,c_1754]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_11,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1758,plain,
% 3.33/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2747,plain,
% 3.33/1.00      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1748,c_1758]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3318,plain,
% 3.33/1.00      ( k1_relat_1(sK2) = sK1
% 3.33/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.33/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_3314,c_2747]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3478,plain,
% 3.33/1.00      ( k1_relat_1(sK2) = sK1 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_3318,c_35,c_36]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6,plain,
% 3.33/1.00      ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1761,plain,
% 3.33/1.00      ( k6_partfun1(k1_relat_1(X0)) = X0
% 3.33/1.00      | r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
% 3.33/1.00      | v1_funct_1(X0) != iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3483,plain,
% 3.33/1.00      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 3.33/1.00      | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top
% 3.33/1.00      | v1_funct_1(sK2) != iProver_top
% 3.33/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3478,c_1761]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3489,plain,
% 3.33/1.00      ( k6_partfun1(sK1) = sK2
% 3.33/1.00      | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top
% 3.33/1.00      | v1_funct_1(sK2) != iProver_top
% 3.33/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_3483,c_3478]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4411,plain,
% 3.33/1.00      ( k6_partfun1(sK1) = sK2 | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_3489,c_35,c_38,c_103,c_2310]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4732,plain,
% 3.33/1.00      ( k6_partfun1(k1_xboole_0) = sK2
% 3.33/1.00      | r2_hidden(sK0(k1_xboole_0,sK2),k1_xboole_0) = iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_4726,c_4411]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4826,plain,
% 3.33/1.00      ( sK2 = k1_xboole_0
% 3.33/1.00      | r2_hidden(sK0(k1_xboole_0,sK2),k1_xboole_0) = iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_4732,c_4]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_0,plain,
% 3.33/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1,plain,
% 3.33/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_366,plain,
% 3.33/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_367,plain,
% 3.33/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_366]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1744,plain,
% 3.33/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4978,plain,
% 3.33/1.00      ( sK2 = k1_xboole_0 ),
% 3.33/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4826,c_1744]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1751,plain,
% 3.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3313,plain,
% 3.33/1.00      ( k1_relset_1(sK1,sK1,sK3) = sK1
% 3.33/1.00      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.33/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1751,c_1754]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2746,plain,
% 3.33/1.00      ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1751,c_1758]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3325,plain,
% 3.33/1.00      ( k1_relat_1(sK3) = sK1
% 3.33/1.00      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.33/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_3313,c_2746]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_39,plain,
% 3.33/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_40,plain,
% 3.33/1.00      ( v1_funct_2(sK3,sK1,sK1) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3748,plain,
% 3.33/1.00      ( k1_relat_1(sK3) = sK1 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_3325,c_39,c_40]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3753,plain,
% 3.33/1.00      ( k6_partfun1(k1_relat_1(sK3)) = sK3
% 3.33/1.00      | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top
% 3.33/1.00      | v1_funct_1(sK3) != iProver_top
% 3.33/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3748,c_1761]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3759,plain,
% 3.33/1.00      ( k6_partfun1(sK1) = sK3
% 3.33/1.00      | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top
% 3.33/1.00      | v1_funct_1(sK3) != iProver_top
% 3.33/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_3753,c_3748]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2306,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.33/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
% 3.33/1.00      | v1_relat_1(sK3) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1964]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2307,plain,
% 3.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.33/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
% 3.33/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2306]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4634,plain,
% 3.33/1.00      ( k6_partfun1(sK1) = sK3 | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_3759,c_39,c_42,c_103,c_2307]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4731,plain,
% 3.33/1.00      ( k6_partfun1(k1_xboole_0) = sK3
% 3.33/1.00      | r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_4726,c_4634]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4831,plain,
% 3.33/1.00      ( sK3 = k1_xboole_0
% 3.33/1.00      | r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_4731,c_4]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5055,plain,
% 3.33/1.00      ( sK3 = k1_xboole_0 ),
% 3.33/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4831,c_1744]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6697,plain,
% 3.33/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.33/1.00      inference(light_normalisation,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_4749,c_2078,c_4978,c_5055]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4751,plain,
% 3.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_4726,c_1751]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5496,plain,
% 3.33/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_4751,c_5055]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1756,plain,
% 3.33/1.00      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5502,plain,
% 3.33/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_5496,c_1756]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6699,plain,
% 3.33/1.00      ( $false ),
% 3.33/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6697,c_5502]) ).
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  ------                               Statistics
% 3.33/1.00  
% 3.33/1.00  ------ General
% 3.33/1.00  
% 3.33/1.00  abstr_ref_over_cycles:                  0
% 3.33/1.00  abstr_ref_under_cycles:                 0
% 3.33/1.00  gc_basic_clause_elim:                   0
% 3.33/1.00  forced_gc_time:                         0
% 3.33/1.00  parsing_time:                           0.01
% 3.33/1.00  unif_index_cands_time:                  0.
% 3.33/1.00  unif_index_add_time:                    0.
% 3.33/1.00  orderings_time:                         0.
% 3.33/1.00  out_proof_time:                         0.015
% 3.33/1.00  total_time:                             0.371
% 3.33/1.00  num_of_symbols:                         58
% 3.33/1.00  num_of_terms:                           9489
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing
% 3.33/1.00  
% 3.33/1.00  num_of_splits:                          0
% 3.33/1.00  num_of_split_atoms:                     0
% 3.33/1.00  num_of_reused_defs:                     0
% 3.33/1.00  num_eq_ax_congr_red:                    25
% 3.33/1.00  num_of_sem_filtered_clauses:            3
% 3.33/1.00  num_of_subtypes:                        0
% 3.33/1.00  monotx_restored_types:                  0
% 3.33/1.00  sat_num_of_epr_types:                   0
% 3.33/1.00  sat_num_of_non_cyclic_types:            0
% 3.33/1.00  sat_guarded_non_collapsed_types:        0
% 3.33/1.00  num_pure_diseq_elim:                    0
% 3.33/1.00  simp_replaced_by:                       0
% 3.33/1.00  res_preprocessed:                       155
% 3.33/1.00  prep_upred:                             0
% 3.33/1.00  prep_unflattend:                        69
% 3.33/1.00  smt_new_axioms:                         0
% 3.33/1.00  pred_elim_cands:                        6
% 3.33/1.00  pred_elim:                              4
% 3.33/1.00  pred_elim_cl:                           4
% 3.33/1.00  pred_elim_cycles:                       9
% 3.33/1.00  merged_defs:                            0
% 3.33/1.00  merged_defs_ncl:                        0
% 3.33/1.00  bin_hyper_res:                          0
% 3.33/1.00  prep_cycles:                            4
% 3.33/1.00  pred_elim_time:                         0.019
% 3.33/1.00  splitting_time:                         0.
% 3.33/1.00  sem_filter_time:                        0.
% 3.33/1.00  monotx_time:                            0.001
% 3.33/1.00  subtype_inf_time:                       0.
% 3.33/1.00  
% 3.33/1.00  ------ Problem properties
% 3.33/1.00  
% 3.33/1.00  clauses:                                28
% 3.33/1.00  conjectures:                            8
% 3.33/1.00  epr:                                    5
% 3.33/1.00  horn:                                   26
% 3.33/1.00  ground:                                 13
% 3.33/1.00  unary:                                  14
% 3.33/1.00  binary:                                 5
% 3.33/1.00  lits:                                   70
% 3.33/1.00  lits_eq:                                20
% 3.33/1.00  fd_pure:                                0
% 3.33/1.00  fd_pseudo:                              0
% 3.33/1.00  fd_cond:                                0
% 3.33/1.00  fd_pseudo_cond:                         3
% 3.33/1.00  ac_symbols:                             0
% 3.33/1.00  
% 3.33/1.00  ------ Propositional Solver
% 3.33/1.00  
% 3.33/1.00  prop_solver_calls:                      28
% 3.33/1.00  prop_fast_solver_calls:                 1256
% 3.33/1.00  smt_solver_calls:                       0
% 3.33/1.00  smt_fast_solver_calls:                  0
% 3.33/1.00  prop_num_of_clauses:                    2226
% 3.33/1.00  prop_preprocess_simplified:             6533
% 3.33/1.00  prop_fo_subsumed:                       39
% 3.33/1.00  prop_solver_time:                       0.
% 3.33/1.00  smt_solver_time:                        0.
% 3.33/1.00  smt_fast_solver_time:                   0.
% 3.33/1.00  prop_fast_solver_time:                  0.
% 3.33/1.00  prop_unsat_core_time:                   0.
% 3.33/1.00  
% 3.33/1.00  ------ QBF
% 3.33/1.00  
% 3.33/1.00  qbf_q_res:                              0
% 3.33/1.00  qbf_num_tautologies:                    0
% 3.33/1.00  qbf_prep_cycles:                        0
% 3.33/1.00  
% 3.33/1.00  ------ BMC1
% 3.33/1.00  
% 3.33/1.00  bmc1_current_bound:                     -1
% 3.33/1.00  bmc1_last_solved_bound:                 -1
% 3.33/1.00  bmc1_unsat_core_size:                   -1
% 3.33/1.00  bmc1_unsat_core_parents_size:           -1
% 3.33/1.00  bmc1_merge_next_fun:                    0
% 3.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation
% 3.33/1.00  
% 3.33/1.00  inst_num_of_clauses:                    675
% 3.33/1.00  inst_num_in_passive:                    58
% 3.33/1.00  inst_num_in_active:                     343
% 3.33/1.00  inst_num_in_unprocessed:                274
% 3.33/1.00  inst_num_of_loops:                      370
% 3.33/1.00  inst_num_of_learning_restarts:          0
% 3.33/1.00  inst_num_moves_active_passive:          24
% 3.33/1.00  inst_lit_activity:                      0
% 3.33/1.00  inst_lit_activity_moves:                0
% 3.33/1.00  inst_num_tautologies:                   0
% 3.33/1.00  inst_num_prop_implied:                  0
% 3.33/1.00  inst_num_existing_simplified:           0
% 3.33/1.00  inst_num_eq_res_simplified:             0
% 3.33/1.00  inst_num_child_elim:                    0
% 3.33/1.00  inst_num_of_dismatching_blockings:      257
% 3.33/1.00  inst_num_of_non_proper_insts:           721
% 3.33/1.00  inst_num_of_duplicates:                 0
% 3.33/1.00  inst_inst_num_from_inst_to_res:         0
% 3.33/1.00  inst_dismatching_checking_time:         0.
% 3.33/1.00  
% 3.33/1.00  ------ Resolution
% 3.33/1.00  
% 3.33/1.00  res_num_of_clauses:                     0
% 3.33/1.00  res_num_in_passive:                     0
% 3.33/1.00  res_num_in_active:                      0
% 3.33/1.00  res_num_of_loops:                       159
% 3.33/1.00  res_forward_subset_subsumed:            21
% 3.33/1.00  res_backward_subset_subsumed:           0
% 3.33/1.00  res_forward_subsumed:                   0
% 3.33/1.00  res_backward_subsumed:                  0
% 3.33/1.00  res_forward_subsumption_resolution:     1
% 3.33/1.00  res_backward_subsumption_resolution:    0
% 3.33/1.00  res_clause_to_clause_subsumption:       139
% 3.33/1.00  res_orphan_elimination:                 0
% 3.33/1.00  res_tautology_del:                      22
% 3.33/1.00  res_num_eq_res_simplified:              0
% 3.33/1.00  res_num_sel_changes:                    0
% 3.33/1.00  res_moves_from_active_to_pass:          0
% 3.33/1.00  
% 3.33/1.00  ------ Superposition
% 3.33/1.00  
% 3.33/1.00  sup_time_total:                         0.
% 3.33/1.00  sup_time_generating:                    0.
% 3.33/1.00  sup_time_sim_full:                      0.
% 3.33/1.00  sup_time_sim_immed:                     0.
% 3.33/1.00  
% 3.33/1.00  sup_num_of_clauses:                     56
% 3.33/1.00  sup_num_in_active:                      32
% 3.33/1.00  sup_num_in_passive:                     24
% 3.33/1.00  sup_num_of_loops:                       72
% 3.33/1.00  sup_fw_superposition:                   21
% 3.33/1.00  sup_bw_superposition:                   23
% 3.33/1.00  sup_immediate_simplified:               18
% 3.33/1.00  sup_given_eliminated:                   0
% 3.33/1.00  comparisons_done:                       0
% 3.33/1.00  comparisons_avoided:                    6
% 3.33/1.00  
% 3.33/1.00  ------ Simplifications
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  sim_fw_subset_subsumed:                 2
% 3.33/1.00  sim_bw_subset_subsumed:                 2
% 3.33/1.00  sim_fw_subsumed:                        1
% 3.33/1.00  sim_bw_subsumed:                        0
% 3.33/1.00  sim_fw_subsumption_res:                 3
% 3.33/1.00  sim_bw_subsumption_res:                 0
% 3.33/1.00  sim_tautology_del:                      0
% 3.33/1.00  sim_eq_tautology_del:                   7
% 3.33/1.00  sim_eq_res_simp:                        0
% 3.33/1.00  sim_fw_demodulated:                     2
% 3.33/1.00  sim_bw_demodulated:                     39
% 3.33/1.00  sim_light_normalised:                   23
% 3.33/1.00  sim_joinable_taut:                      0
% 3.33/1.00  sim_joinable_simp:                      0
% 3.33/1.00  sim_ac_normalised:                      0
% 3.33/1.00  sim_smt_subsumption:                    0
% 3.33/1.00  
%------------------------------------------------------------------------------
